---
# Feel free to add content and custom Front Matter to this file.
# To modify the layout, see https://jekyllrb.com/docs/themes/#overriding-theme-defaults

# layout: home
usemathjax: true
---

## The Ramanujan--Nagell Theorem

The [Ramanujan--Nagell equation](https://en.wikipedia.org/wiki/Ramanujan%E2%80%93Nagell_equation) is the Diophantine equation

$$x^2 + 7 = 2^n,$$

where $x$ is an integer and $n$ is a natural number. Conjectured by Ramanujan in 1913 and proved by Nagell in 1948, the theorem states that the only solutions are

$$(x, n) \in \{(\pm 1, 3),\ (\pm 3, 4),\ (\pm 5, 5),\ (\pm 11, 7),\ (\pm 181, 15)\}.$$

The proof splits into an even case (a factorization argument over $\mathbb{Z}$) and an odd case, which requires algebraic number theory in the ring of integers of $\mathbb{Q}(\sqrt{-7})$ — in particular, the fact that this ring is a principal ideal domain (class number 1).

This project contains a Lean 4 / Mathlib formalization of the theorem, **complete modulo the computation of the discriminant of $\mathbb{Q}(\sqrt{-7})$ and the units in its ring of integers**. The discriminant result (`K_discriminant : discr K = 7`) is stated but currently marked `sorry`, pending the development of the relevant Mathlib machinery for quadratic field discriminants. The units results (`units_pm_1 : ∀ u : Rˣ, u = 1 ∨ u = -1`) has some `sorry`s but otherwise the structure for that is in place.

Useful links:

* [Zulip chat for Lean](https://leanprover.zulipchat.com/) for coordination
* [Blueprint]({{ site.url }}/blueprint/)
* [Blueprint as pdf]({{ site.url }}/blueprint.pdf)
* [Dependency graph]({{ site.url }}/blueprint/dep_graph_document.html)
* [Doc pages for this repository]({{ site.url }}/docs/)