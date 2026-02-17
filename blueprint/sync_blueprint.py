#!/usr/bin/env python3
"""
Sync blueprint content.tex and lean_decls with actual Lean source files.

Usage: python3 blueprint/sync_blueprint.py [--dry-run]

This script:
1. Parses Lean source files for declarations (lemma/theorem/def/abbrev)
2. Detects sorry/admit status in each declaration
3. Updates leanok annotations in content.tex to match
4. Auto-generates new LaTeX entries for declarations not yet in content.tex
5. Regenerates lean_decls
"""

import re
import os
import sys
from pathlib import Path
from dataclasses import dataclass, field

# ---------------------------------------------------------------------------
# Configuration
# ---------------------------------------------------------------------------

PROJECT_ROOT = Path(__file__).resolve().parent.parent
LEAN_DIR = PROJECT_ROOT / "RamanujanNagell"
CONTENT_TEX = PROJECT_ROOT / "blueprint" / "src" / "content.tex"
LEAN_DECLS = PROJECT_ROOT / "blueprint" / "lean_decls"

# Only scan primary source files (skip test/playground/backup)
SCAN_FILES = ["Basic.lean", "Helpers.lean"]

# Declaration regex: matches lemma, theorem, def, abbrev at start of line
# Handles optional prefixes: noncomputable, private, protected, @[...]
# Lean identifiers can contain apostrophes ('), subscripts, and Unicode
DECL_RE = re.compile(
    r"^(?:(?:noncomputable|private|protected)\s+)*"
    r"(lemma|theorem|def|abbrev)\s+([\w']+)",
    re.MULTILINE,
)

# Docstring regex: /-- ... -/ immediately before a declaration
DOCSTRING_RE = re.compile(
    r"/--\s*(.*?)\s*-/\s*\n(?=(?:(?:noncomputable|private|protected)\s+)*(?:lemma|theorem|def|abbrev)\s)",
    re.DOTALL,
)

# Skip declarations that are internal/not blueprint-relevant
SKIP_NAMES = {
    "f_minpoly",  # internal abbrev
}


# ---------------------------------------------------------------------------
# Data structures
# ---------------------------------------------------------------------------

@dataclass
class LeanDecl:
    name: str
    kind: str  # lemma, theorem, def, abbrev
    docstring: str = ""
    has_sorry: bool = False
    source_file: str = ""
    body: str = ""  # raw body text for reference detection
    references: list = field(default_factory=list)


# ---------------------------------------------------------------------------
# Step 1: Parse Lean source files
# ---------------------------------------------------------------------------

def parse_lean_files() -> dict[str, LeanDecl]:
    """Parse Lean files and return dict of name -> LeanDecl."""
    decls: dict[str, LeanDecl] = {}

    for filename in SCAN_FILES:
        filepath = LEAN_DIR / filename
        if not filepath.exists():
            print(f"  WARNING: {filepath} not found, skipping")
            continue

        text = filepath.read_text()
        lines = text.split("\n")

        # Find all declarations with their positions
        matches = list(DECL_RE.finditer(text))

        for i, m in enumerate(matches):
            kind = m.group(1)
            name = m.group(2)

            if name in SKIP_NAMES:
                continue

            # Skip commented-out declarations
            line_start = text.rfind("\n", 0, m.start()) + 1
            line_text = text[line_start:m.start()]
            if line_text.strip().startswith("--"):
                continue

            # Skip private declarations (internal helpers, not blueprint-relevant)
            prefix = text[line_start:m.start() + len(m.group(0))]
            if "private" in prefix:
                continue

            # Extract body (from declaration start to next declaration or EOF)
            body_start = m.start()
            if i + 1 < len(matches):
                body_end = matches[i + 1].start()
            else:
                body_end = len(text)
            body = text[body_start:body_end]

            # Extract docstring (look backwards from declaration)
            docstring = ""
            # Search for /-- ... -/ ending just before this declaration
            # (may have noncomputable/private/protected prefix between docstring and decl keyword)
            before = text[:m.start()]
            doc_match = re.search(r"/--\s*(.*?)\s*-/\s*(?:(?:noncomputable|private|protected)\s+)*$", before, re.DOTALL)
            if doc_match:
                docstring = doc_match.group(1).strip()
                # Clean up: take first line/sentence as summary
                first_line = docstring.split("\n")[0].strip()
                if first_line:
                    docstring = first_line

            # Detect sorry/admit in body (not in comments)
            has_sorry = _has_sorry_in_body(body)

            decls[name] = LeanDecl(
                name=name,
                kind=kind,
                docstring=docstring,
                has_sorry=has_sorry,
                source_file=filename,
                body=body,
            )

    # Compute references (other decl names appearing in proof bodies)
    all_names = set(decls.keys())
    for decl in decls.values():
        # Strip comments from body before scanning for references
        body_no_comments = _strip_lean_comments(decl.body)
        # Also skip the first line (the declaration signature itself)
        body_lines = body_no_comments.split("\n")
        body_for_refs = "\n".join(body_lines[1:]) if len(body_lines) > 1 else ""
        refs = []
        for other_name in all_names:
            if other_name != decl.name and re.search(
                r"(?<!\w)" + re.escape(other_name) + r"(?!\w)", body_for_refs
            ):
                refs.append(other_name)
        decl.references = sorted(refs)

    return decls


def _strip_lean_comments(text: str) -> str:
    """Remove Lean comments from text: -- line comments and /- block comments -/."""
    # Remove block comments (including nested /- ... -/ and /-- ... -/)
    result = re.sub(r"/-.*?-/", "", text, flags=re.DOTALL)
    # Remove line comments
    lines = []
    for line in result.split("\n"):
        idx = line.find("--")
        if idx >= 0:
            lines.append(line[:idx])
        else:
            lines.append(line)
    return "\n".join(lines)


def _has_sorry_in_body(body: str) -> bool:
    """Check if body contains sorry or admit (not in comments)."""
    for line in body.split("\n"):
        # Strip inline comments
        stripped = line.split("--")[0]
        # Also strip block comments (simple heuristic)
        stripped = re.sub(r"/-.*?-/", "", stripped)
        if re.search(r"\bsorry\b", stripped) or re.search(r"\badmit\b", stripped):
            return True
    return False


# ---------------------------------------------------------------------------
# Step 2 & 3: Parse and update content.tex
# ---------------------------------------------------------------------------

def update_content_tex(decls: dict[str, LeanDecl], dry_run: bool = False):
    r"""Update \leanok in content.tex and append new entries."""
    text = CONTENT_TEX.read_text()

    # Track changes for report
    added_leanok = []
    removed_leanok = []
    new_entries = []
    uses_changes = []  # (name, old_uses, new_uses)

    # Find all \lean{name} entries
    lean_entries = set(re.findall(r"\\lean\{([\w']+)\}", text))

    # Build map from Lean name -> existing LaTeX label
    # by finding \lean{name} and looking backwards for the nearest \label{...}
    lean_name_to_label: dict[str, str] = {}
    for m in re.finditer(r"\\lean\{([\w']+)\}", text):
        lean_name = m.group(1)
        before = text[:m.start()]
        label_match = re.search(r"\\label\{([^}]+)\}\s*$", before)
        if label_match:
            lean_name_to_label[lean_name] = label_match.group(1)

    # --- Step 3: Update \leanok on existing entries ---
    # Strategy: process block by block. A "block" is from \begin{env} to
    # the matching \end{proof} (or \end{env} if no proof).

    # We process the file tracking \lean{} entries and their \leanok status.
    # For each \lean{name}, find its enclosing environment and proof block.

    lines = text.split("\n")
    new_lines = []
    i = 0
    while i < len(lines):
        line = lines[i]

        # Check if this line has \lean{name}
        lean_match = re.search(r"\\lean\{([\w']+)\}", line)
        if lean_match:
            name = lean_match.group(1)
            decl = decls.get(name)

            if decl is not None:
                fully_proved = not decl.has_sorry
            else:
                # Declaration no longer exists in Lean source — remove \leanok
                fully_proved = False

            # We need to handle \leanok on the statement (appears between
            # \begin{env} and \end{env}) and on the proof (\begin{proof}...\end{proof}).
            #
            # Walk backwards to find the \begin{env} line, then forward to
            # find \end{env} and optionally \begin{proof}...\end{proof}.
            #
            # For simplicity, we process line-by-line from here:
            # - The current region: from \lean{} line until we leave the
            #   current environment+proof block.

            # Just add the current line and continue — we'll handle \leanok
            # on surrounding lines as we encounter them.
            new_lines.append(line)
            i += 1
            continue

        # Check for \leanok on statement lines (not inside \begin{proof})
        # We detect this by looking at context: if we're between \begin{lemma/theorem/definition}
        # and \end{lemma/theorem/definition}, this is a statement \leanok
        leanok_match = re.match(r"^(\s*)\\leanok\s*$", line)
        if leanok_match:
            # Look backwards to find which \lean{} entry this belongs to
            name = _find_lean_name_backwards(new_lines + [line], len(new_lines))
            if name:
                decl = decls.get(name)
                fully_proved = decl is not None and not decl.has_sorry

                if not fully_proved:
                    # Remove this \leanok line
                    removed_leanok.append(name)
                    i += 1
                    continue
            # Keep it
            new_lines.append(line)
            i += 1
            continue

        # Check for \begin{proof}\leanok or \begin{proof} followed by \leanok
        proof_leanok = re.match(r"^(\\begin\{proof\})\\leanok(.*)$", line)
        if proof_leanok:
            name = _find_lean_name_backwards(new_lines + [line], len(new_lines))
            if name:
                decl = decls.get(name)
                fully_proved = decl is not None and not decl.has_sorry

                if not fully_proved:
                    # Remove \leanok from proof line
                    removed_leanok.append(f"{name} (proof)")
                    new_lines.append(proof_leanok.group(1) + proof_leanok.group(2))
                    i += 1
                    continue
            new_lines.append(line)
            i += 1
            continue

        new_lines.append(line)
        i += 1

    # --- Now handle adding \leanok where missing ---
    # Re-scan the updated text for entries that should have \leanok but don't
    updated_text = "\n".join(new_lines)
    new_lines = []
    lines = updated_text.split("\n")
    i = 0
    while i < len(lines):
        line = lines[i]
        new_lines.append(line)

        lean_match = re.search(r"\\lean\{([\w']+)\}", line)
        if lean_match:
            name = lean_match.group(1)
            decl = decls.get(name)
            if decl and not decl.has_sorry:
                # Check if \leanok follows (possibly with \uses{} in between)
                has_statement_leanok = _has_leanok_nearby(lines, i)
                if not has_statement_leanok:
                    # Add \leanok after this line (or after \uses if present)
                    insert_idx = i + 1
                    while insert_idx < len(lines) and re.match(
                        r"^\s*\\uses\{", lines[insert_idx]
                    ):
                        insert_idx += 1
                    # We already appended current line; handle insertion after
                    # processing remaining lines up to insert point
                    while i + 1 < insert_idx:
                        i += 1
                        new_lines.append(lines[i])
                    new_lines.append("  \\leanok")
                    added_leanok.append(name)

        # Check for \begin{proof} without \leanok that should have it
        proof_match = re.match(r"^\\begin\{proof\}\s*$", line)
        if proof_match:
            name = _find_lean_name_backwards(new_lines, len(new_lines) - 1)
            if name:
                decl = decls.get(name)
                if decl and not decl.has_sorry:
                    # Check next line isn't already \leanok
                    next_line = lines[i + 1] if i + 1 < len(lines) else ""
                    if not re.match(r"^\s*\\leanok", next_line):
                        # Replace line with \begin{proof}\leanok
                        new_lines[-1] = "\\begin{proof}\\leanok"
                        added_leanok.append(f"{name} (proof)")

        i += 1

    # --- Pass 3: Insert missing proof blocks for fully-proved entries ---
    # If an entry has \leanok on the statement but no \begin{proof} block,
    # insert one after \end{lemma/theorem/definition}.
    updated_text = "\n".join(new_lines)
    new_lines = []
    lines = updated_text.split("\n")
    current_lean_name = None
    i = 0
    while i < len(lines):
        line = lines[i]
        new_lines.append(line)

        # Track which \lean{} entry we're in
        lean_match = re.search(r"\\lean\{([\w']+)\}", line)
        if lean_match:
            current_lean_name = lean_match.group(1)

        # When we hit \end{lemma/theorem/definition}, check if proof block follows
        end_match = re.match(r"\\end\{(lemma|theorem|definition)\}", line)
        if end_match and current_lean_name:
            decl = decls.get(current_lean_name)
            if decl and not decl.has_sorry:
                # Check if next non-empty line is \begin{proof}
                next_idx = i + 1
                while next_idx < len(lines) and lines[next_idx].strip() == "":
                    next_idx += 1
                has_proof = (
                    next_idx < len(lines)
                    and re.match(r"\\begin\{proof\}", lines[next_idx])
                )
                if not has_proof:
                    new_lines.append("\\begin{proof}\\leanok")
                    new_lines.append("  Proof in Lean source.")
                    new_lines.append("\\end{proof}")
                    added_leanok.append(f"{current_lean_name} (proof)")
            current_lean_name = None

        i += 1

    # --- Pass 4: Normalize labels to match Lean names ---
    # Ensure all \label{prefix:X} match the \lean{Y} on the next line.
    # Build rename map and apply globally.
    current_text = "\n".join(new_lines)
    label_renames: dict[str, str] = {}  # old_label -> new_label
    for m_iter in re.finditer(
        r"\\label\{((?:lem|thm|def):([^}]+))\}\s*\n\s*\\lean\{([\w']+)\}",
        current_text,
    ):
        old_label = m_iter.group(1)
        label_prefix = old_label.split(":")[0]
        lean_name = m_iter.group(3)
        new_label = f"{label_prefix}:{lean_name}"
        if old_label != new_label:
            label_renames[old_label] = new_label

    if label_renames:
        text_to_fix = "\n".join(new_lines)
        for old_label, new_label in label_renames.items():
            text_to_fix = text_to_fix.replace(old_label, new_label)
        new_lines = text_to_fix.split("\n")

    # --- Pass 5: Update \uses{} on all existing entries ---
    # Recompute dependencies from Lean source and update \uses{} lines.
    # First, rebuild the label map from the current state of the file
    current_text = "\n".join(new_lines)
    lean_name_to_label = {}
    for m_iter in re.finditer(r"\\label\{([^}]+)\}\s*\n\s*\\lean\{([\w']+)\}", current_text):
        lean_name_to_label[m_iter.group(2)] = m_iter.group(1)

    # Also collect all lean names that are in the blueprint
    all_blueprint_lean_names = set(re.findall(r"\\lean\{([\w']+)\}", current_text))

    updated_text = "\n".join(new_lines)
    new_lines = []
    lines = updated_text.split("\n")
    i = 0
    current_lean_name = None
    while i < len(lines):
        line = lines[i]

        # Track current \lean{} entry
        lean_match = re.search(r"\\lean\{([\w']+)\}", line)
        if lean_match:
            current_lean_name = lean_match.group(1)
            new_lines.append(line)

            # Compute expected \uses from Lean source
            decl = decls.get(current_lean_name)
            if decl:
                # Filter references to only those in the blueprint
                expected_refs = [
                    ref for ref in decl.references
                    if ref in all_blueprint_lean_names and ref != current_lean_name
                ]
                expected_labels = []
                for ref in sorted(expected_refs):
                    if ref in lean_name_to_label:
                        expected_labels.append(lean_name_to_label[ref])
                    else:
                        ref_decl = decls.get(ref)
                        if ref_decl:
                            ref_prefix = _kind_to_label_prefix(ref_decl.kind)
                            expected_labels.append(f"{ref_prefix}:{ref}")

                # Check if next line is an existing \uses{}
                next_idx = i + 1
                if next_idx < len(lines) and re.match(r"^\s*\\uses\{", lines[next_idx]):
                    old_uses_line = lines[next_idx]
                    old_uses = re.search(r"\\uses\{([^}]*)\}", old_uses_line)
                    old_uses_str = old_uses.group(1) if old_uses else ""

                    if expected_labels:
                        new_uses_str = ", ".join(expected_labels)
                        if new_uses_str != old_uses_str:
                            uses_changes.append((current_lean_name, old_uses_str, new_uses_str))
                        new_lines.append(f"  \\uses{{{new_uses_str}}}")
                    else:
                        # No dependencies — remove \uses line
                        if old_uses_str:
                            uses_changes.append((current_lean_name, old_uses_str, ""))
                        # Skip the old \uses line (don't append it)
                    i = next_idx  # skip old \uses line (we replaced or removed it)
                else:
                    # No existing \uses line — add one if needed
                    if expected_labels:
                        new_uses_str = ", ".join(expected_labels)
                        uses_changes.append((current_lean_name, "", new_uses_str))
                        new_lines.append(f"  \\uses{{{new_uses_str}}}")

            i += 1
            continue

        new_lines.append(line)
        i += 1

    # --- Step 6: Auto-generate new entries ---
    # Refresh the label map and blueprint names after uses pass
    current_text = "\n".join(new_lines)
    lean_name_to_label = {}
    for m_iter in re.finditer(r"\\label\{([^}]+)\}\s*\n\s*\\lean\{([\w']+)\}", current_text):
        lean_name_to_label[m_iter.group(2)] = m_iter.group(1)
    existing_lean_names = set(re.findall(r"\\lean\{([\w']+)\}", current_text))
    missing = {
        name: decl
        for name, decl in decls.items()
        if name not in existing_lean_names
    }

    if missing:
        # Check if "Additional declarations" section already exists
        additional_section_re = re.compile(
            r"\\section\{Additional declarations\}"
        )
        has_section = additional_section_re.search("\n".join(new_lines))

        if has_section:
            # Remove old additional section to regenerate
            joined = "\n".join(new_lines)
            section_start = joined.find("\\section{Additional declarations}")
            if section_start >= 0:
                # Trim from section start to end
                new_lines = joined[:section_start].rstrip().split("\n")

        new_lines.append("")
        new_lines.append("\\section{Additional declarations}")
        new_lines.append("")

        # Pre-populate label map for new entries so cross-references work
        for name in missing:
            if name not in lean_name_to_label:
                decl = missing[name]
                label_prefix = _kind_to_label_prefix(decl.kind)
                lean_name_to_label[name] = f"{label_prefix}:{name}"

        # Sort by source file then name for stable ordering
        for name in sorted(missing.keys()):
            decl = missing[name]
            new_entries.append(name)

            env = _kind_to_env(decl.kind)
            label_prefix = _kind_to_label_prefix(decl.kind)

            desc = decl.docstring if decl.docstring else "TODO: add description"
            fully_proved = not decl.has_sorry

            new_lines.append(f"\\begin{{{env}}}[{name}]")
            new_lines.append(f"  \\label{{{label_prefix}:{name}}}")
            new_lines.append(f"  \\lean{{{name}}}")

            # Auto-detect \uses (prefer existing labels over auto-generated ones)
            uses_labels = []
            for ref in decl.references:
                if ref in existing_lean_names or ref in missing:
                    if ref in lean_name_to_label:
                        uses_labels.append(lean_name_to_label[ref])
                    else:
                        ref_decl = decls.get(ref)
                        if ref_decl:
                            ref_prefix = _kind_to_label_prefix(ref_decl.kind)
                            uses_labels.append(f"{ref_prefix}:{ref}")
            if uses_labels:
                new_lines.append(f"  \\uses{{{', '.join(uses_labels)}}}")

            if fully_proved:
                new_lines.append("  \\leanok")
            new_lines.append(f"  {desc}")
            new_lines.append(f"\\end{{{env}}}")

            if fully_proved:
                new_lines.append(f"\\begin{{proof}}\\leanok")
            else:
                new_lines.append(f"\\begin{{proof}}")
            new_lines.append(f"  Proof in Lean source.")
            new_lines.append(f"\\end{{proof}}")
            new_lines.append("")

    final_text = "\n".join(new_lines)
    # Ensure file ends with newline
    if not final_text.endswith("\n"):
        final_text += "\n"

    if not dry_run:
        CONTENT_TEX.write_text(final_text)

    return added_leanok, removed_leanok, new_entries, uses_changes, final_text


def _find_lean_name_backwards(lines: list[str], from_idx: int) -> str | None:
    """Look backwards from from_idx to find the nearest \\lean{name}."""
    for j in range(from_idx, max(from_idx - 20, -1), -1):
        m = re.search(r"\\lean\{([\w']+)\}", lines[j])
        if m:
            return m.group(1)
        # Stop if we hit a \begin{env} (we've gone too far back)
        if re.match(r"\\begin\{(lemma|theorem|definition)\}", lines[j]):
            break
    return None


def _has_leanok_nearby(lines: list[str], lean_line_idx: int) -> bool:
    """Check if \\leanok appears within a few lines after \\lean{} line,
    before \\end{env} or \\begin{proof}."""
    for j in range(lean_line_idx + 1, min(lean_line_idx + 6, len(lines))):
        if re.match(r"^\s*\\leanok", lines[j]):
            return True
        if re.match(r"\\end\{", lines[j]) or re.match(r"\\begin\{proof\}", lines[j]):
            return False
    return False


def _kind_to_env(kind: str) -> str:
    if kind in ("def", "abbrev"):
        return "definition"
    if kind == "theorem":
        return "theorem"
    return "lemma"


def _kind_to_label_prefix(kind: str) -> str:
    if kind in ("def", "abbrev"):
        return "def"
    if kind == "theorem":
        return "thm"
    return "lem"


# ---------------------------------------------------------------------------
# Step 5: Update lean_decls
# ---------------------------------------------------------------------------

def update_lean_decls(final_tex: str, dry_run: bool = False):
    """Regenerate lean_decls from final content.tex."""
    names = sorted(set(re.findall(r"\\lean\{([\w']+)\}", final_tex)))
    content = "\n".join(names) + "\n"
    if not dry_run:
        LEAN_DECLS.write_text(content)
    return names


# ---------------------------------------------------------------------------
# Step 6: Report
# ---------------------------------------------------------------------------

def print_report(
    decls: dict[str, LeanDecl],
    added: list[str],
    removed: list[str],
    new_entries: list[str],
    uses_changes: list[tuple[str, str, str]],
    lean_decl_names: list[str],
):
    print("=" * 60)
    print("Blueprint Sync Report")
    print("=" * 60)
    print()

    # Declaration stats
    sorry_count = sum(1 for d in decls.values() if d.has_sorry)
    proved_count = len(decls) - sorry_count
    print(f"Lean declarations scanned: {len(decls)}")
    print(f"  Fully proved (no sorry): {proved_count}")
    print(f"  Has sorry/admit:         {sorry_count}")
    if sorry_count > 0:
        for name, d in sorted(decls.items()):
            if d.has_sorry:
                print(f"    - {name} ({d.source_file})")
    print()

    # \leanok changes
    if added:
        print(f"\\leanok ADDED ({len(added)}):")
        for name in added:
            print(f"  + {name}")
    else:
        print("\\leanok added: none")

    if removed:
        print(f"\\leanok REMOVED ({len(removed)}):")
        for name in removed:
            print(f"  - {name}")
    else:
        print("\\leanok removed: none")
    print()

    # \uses changes
    if uses_changes:
        print(f"\\uses UPDATED ({len(uses_changes)}):")
        for name, old, new in uses_changes:
            if old and new:
                print(f"  ~ {name}")
                print(f"      was: {old}")
                print(f"      now: {new}")
            elif new:
                print(f"  + {name}: {new}")
            else:
                print(f"  - {name}: (removed)")
    else:
        print("\\uses changes: none")
    print()

    # New entries
    if new_entries:
        print(f"New LaTeX entries generated ({len(new_entries)}):")
        for name in new_entries:
            print(f"  * {name}")
    else:
        print("New LaTeX entries: none")
    print()

    print(f"lean_decls updated: {len(lean_decl_names)} entries")
    print()
    print("Done. Review changes with: git diff blueprint/")


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def main():
    dry_run = "--dry-run" in sys.argv

    if dry_run:
        print("[DRY RUN] No files will be modified.\n")

    os.chdir(PROJECT_ROOT)

    print("Parsing Lean source files...")
    decls = parse_lean_files()
    print(f"  Found {len(decls)} declarations\n")

    print("Updating content.tex...")
    added, removed, new_entries, uses_changes, final_tex = update_content_tex(decls, dry_run)

    print("Updating lean_decls...")
    lean_decl_names = update_lean_decls(final_tex, dry_run)

    print()
    print_report(decls, added, removed, new_entries, uses_changes, lean_decl_names)


if __name__ == "__main__":
    main()
