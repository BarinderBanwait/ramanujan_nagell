# The Ramanujan–Nagell Theorem in Lean

A Lean 4 / Mathlib formalization of the Ramanujan–Nagell theorem, **complete with no `sorry`s**.

The [Ramanujan–Nagell equation](https://en.wikipedia.org/wiki/Ramanujan%E2%80%93Nagell_equation) is the Diophantine equation

$$x^2 + 7 = 2^n,$$

where $x$ is an integer and $n$ is a natural number. Conjectured by Ramanujan in 1913 and proved by Nagell in 1948, the theorem states that the only solutions are

$$(x, n) \in \{(\pm 1, 3),\ (\pm 3, 4),\ (\pm 5, 5),\ (\pm 11, 7),\ (\pm 181, 15)\}.$$

The proof splits into an even case (a factorization argument over $\mathbb{Z}$) and an odd case, which works in the ring $R = \mathbb{Z}[(1+\sqrt{-7})/2]$, the ring of integers of $\mathbb{Q}(\sqrt{-7})$. The key structural fact is that $R$ is a unique factorization domain.

Rather than computing the discriminant and class number, we prove directly that $R$ is a Euclidean domain — via a smart-rounding division algorithm for the norm $N(x + y\theta) = x^2 + xy + 2y^2$ — hence a principal ideal ring, hence a unique factorization domain. The units are exactly $\{\pm 1\}$, obtained from the positive-definite norm form $4N = (2x+y)^2 + 7y^2$.

## Links

* [Paper (arXiv:2604.09808)](https://arxiv.org/abs/2604.09808)
* [Blueprint](https://barindersbanwait.com/ramanujan_nagell/blueprint/)
* [Blueprint as PDF](https://barindersbanwait.com/ramanujan_nagell/blueprint.pdf)
* [Dependency graph](https://barindersbanwait.com/ramanujan_nagell/blueprint/dep_graph_document.html)
* [API documentation](https://barindersbanwait.com/ramanujan_nagell/docs/)
* [Zulip chat for Lean](https://leanprover.zulipchat.com/)
