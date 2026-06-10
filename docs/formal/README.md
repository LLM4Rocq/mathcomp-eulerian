# Stanley-style formal companion (PDF)

A self-contained LaTeX document that reads like a chapter of Stanley
*Enumerative Combinatorics I* but pairs each definition and statement
with the verbatim Rocq text, with clickable links to the GitHub
source.

**Deployed:** https://llm4rocq.github.io/mathcomp-eulerian/eulerian_formal.pdf
(rebuilt by CI on every push to `main`).

## Contents

The PDF is 105 pages, structured as:

| Chapter / Appendix | Stanley | Pages |
|---|---|---|
| 1. A combinatorialist's mathcomp primer | — | 5-6 |
| 2. Cycles and Stirling numbers | §1.3.1-2 | 7-9 |
| 3. Inversions and the major index | §1.3.3 | 10-11 |
| 4. Foata's bijection and MacMahon's equidistribution | §1.3.4 | 12-13 |
| 5. Descents and Eulerian numbers | §1.4 | 14-20 |
| 6. The $q$-analogues | §1.4 | 21-22 |
| 7. Longest alternating subsequence | §1.6.2 | 23-25 |
| 8. Toggle action and Stanley's Corollary 1.6.5 (project headline) | §1.6.3 | 26-28 |
| 9. André's reflection method and Prop 1.6.1 (sec + tan) | §1.6.4 | 29 |
| **A. Comprehensive lemma catalog (1078 entries, auto-generated)** | — | 30-100 |
| B. Glossary of mathcomp primitives | — | 77-78 |
| C. Source map | — | 79 |

Every named result in the active build chain appears in Appendix A
with its `coqdoc` docstring and a clickable GitHub link. The
narrative chapters (2-9) cover the ~70 most-cited results in
expository form, with a "Decoded:" line under every formal block
restating it in plain math.

## Build

Requires a LaTeX distribution with `pdflatex` (or `lualatex`) and the
following packages: `listings`, `hyperref`, `bookmark`, `cleveref`,
`amsthm`, `mathtools`, `stmaryrd`, `xcolor`, `geometry`, `lmodern`,
`microtype`, `booktabs`.

On Debian/Ubuntu (and CI runners):

```bash
sudo apt-get install -y \
  texlive-latex-base texlive-latex-recommended texlive-latex-extra \
  texlive-fonts-recommended texlive-fonts-extra texlive-science
```

Then:

```bash
cd docs/formal
make             # produces eulerian_formal.pdf
make lua         # alternative using lualatex
make clean       # remove auxiliaries
```

## Format

Each definition is a `\begin{definition}` block with the informal
mathematical statement, immediately followed by a `\rocqsource{file}{line}`
macro (which produces a clickable link to the line on GitHub) and a
plain `lstlisting` environment containing the formal Rocq text
verbatim:

```latex
\rocqsource{descent.v}{25}
\begin{lstlisting}[language=Rocq]
Definition descent_set s : {set 'I_n} := [set i | is_descent s i].
\end{lstlisting}
```

(For multi-line ranges, use `\rocqsourcerange{file}{line1}{line2}`.)

Each theorem/lemma/proposition is structured the same way, with a
short prose proof sketch following the formal statement. The full
proof is one click away in the linked source.

The document is intentionally self-contained as a reading
experience: a mathematician should not need to install Rocq or
clone the repository to read it through. The clickable links are
opportunistic — they take you to the source if you want to look,
but the math is complete on the page.

## Audience

A combinatorialist familiar with Stanley EC1 who wants to:

- Read the formalized material as ordinary mathematics.
- Verify that the formal statements faithfully match Stanley's
  informal definitions.
- Click through to the actual Rocq source when something is
  unclear or worth a closer look.

Companion documents:

- [`../READING_GUIDE.md`](../READING_GUIDE.md) — 10-minute
  orientation: index conventions, type translations, worked example.
- [`../DEFINITIONS_AUDIT.md`](../DEFINITIONS_AUDIT.md) — focused
  side-by-side audit of every definition, in markdown.
- The blueprint at https://llm4rocq.github.io/mathcomp-eulerian/ —
  paper-style HTML with a clickable dependency graph.

This formal companion is the most "book-like" of the four: it reads
top-to-bottom like Stanley, is printable as a PDF, and includes
formal text inline rather than via separate hyperlinks.
