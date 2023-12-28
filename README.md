# Confluence for 𝜑-calculus

Formalization of 𝜑-calculus variants and corresponding confluence results.

## About

We aim to formalize, using a computer proof assistant Lean 4,
𝜑-calculus and the rewrite rules for normalization
of 𝜑-programs (see <https://github.com/objectionary/normalizer>).
We are particularly interested in the confluence of the rewrite system.
To formalize this, we first focus on the minimal version of the calculus[^1],
and then gradually add features to match [EO](https://github.com/objectionary/eo)[^2].

## Installation

If you use VS Code, get [lean4 extension](https://github.com/leanprover/vscode-lean4).
Otherwise, install [`elan`](https://github.com/leanprover/elan), version manager for Lean.

In VScode, make sure to open the root directory of the project.
Then run the following from the Terminal:

```sh
lake build
```

[^1]: Nikolai Kudasov and Violetta Sim. 2023. _Formalizing 𝜑-Calculus: A Purely Object-Oriented Calculus of Decorated Objects._ In Proceedings of the 24th ACM International Workshop on Formal Techniques for Java-like Programs (FTfJP '22). Association for Computing Machinery, New York, NY, USA, 29–36. <https://doi.org/10.1145/3611096.3611103>

[^2]: Yegor Bugayenko. 2022. _EOLANG and φ-calculus._ <https://arxiv.org/abs/2111.13384>
