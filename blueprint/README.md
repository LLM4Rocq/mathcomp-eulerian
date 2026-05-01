# Blueprint

A [rocqblueprint](https://github.com/reiniscirpons/rocqblueprint) document
that gives an interactive, paper-style mathematical exposition of this
formalization, with cross-references back to the actual Rocq lemmas
and a clickable dependency graph.

The published site (auto-deployed by `.github/workflows/blueprint.yml`):

> https://llm4rocq.github.io/mathcomp-eulerian/

## Layout

```
blueprint/
  README.md              ← this file
  src/
    web.tex              ← entry point (web)
    print.tex            ← entry point (PDF)
    content.tex          ← chapter \input list
    plastex.cfg          ← plasTeX renderer config
    extra_styles.css     ← optional style overrides
    macros/
      common.tex         ← \newtheorem + math notation
      web.tex            ← web-only macros
      print.tex          ← PDF-only stubs (\rocq, \uses, ...)
    ch_descents.tex      ← Stanley §1.4 (descents, Eulerian, β)
    ch_mmtree.tex        ← min-max trees, ψᵢ operators (Fact #1)
    ch_cdindex.tex       ← cd-index, expand_cde, Fact #3
    ch_omega.tex         ← toggle action, ω, alternating sets
    ch_propositions.tex  ← Stanley Prop 1.6.4 + Cor 1.6.5
```

## Build locally

```bash
pip install rocqblueprint plastexdepgraph
sudo apt-get install -y graphviz libgraphviz-dev texlive-base

cd blueprint/src
rocqblueprint web    # builds blueprint/web/
rocqblueprint pdf    # builds blueprint/print/blueprint.pdf
rocqblueprint serve  # local web server on http://localhost:8080/
```

## Cross-reference convention

Every result block uses the rocqblueprint macros:

```latex
\begin{theorem}[Stanley Prop 1.6.4]
  \label{prop:omega_proper_beta_lt}
  \uses{def:omega_set, def:beta, thm:phi_w_support_general, thm:fact3}
  \rocq{mathcomp_eulerian.perm_seq_bridge.omega_proper_beta_lt}
  \rocqok
  ...
\end{theorem}
```

- `\rocq{...}` is the **fully qualified** Rocq name as resolved by
  `Locate`: `<library>.<file>.<lemma>`. For this project that's
  `mathcomp_eulerian.<file>.<lemma>`.
- `\rocqok` marks the result as fully formalized (every result here
  is `\rocqok` since the project is complete).
- `\uses{label1, label2, ...}` declares dependencies; these become
  edges in the rendered dependency graph.
