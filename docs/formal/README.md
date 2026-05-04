# Stanley-style formal companion (PDF)

A self-contained LaTeX document that reads like a chapter of Stanley
*Enumerative Combinatorics I* but pairs each definition and statement
with the verbatim Rocq text, with clickable links to the GitHub
source.

## Status (Session 1, prototype)

Only **Chapter 1: Descents and Eulerian numbers** is currently
written. Future chapters cover:

| Chapter | Stanley | Status |
|---------|---------|--------|
| 1. Descents and Eulerian numbers | §1.4 | ✅ written |
| 2. Cycles and Stirling numbers | §1.3.1-2 | planned |
| 3. Inversions and the major index | §1.3.3 | planned |
| 4. The Foata bijection | §1.3.4 | planned |
| 5. $q$-analogues | §1.4 | planned |
| 6. Longest alternating subsequence | §1.6.2 | planned |
| 7. Toggle action and Cor 1.6.5 | §1.6.3 | planned |
| 8. André's reflection method | §1.6.4 | planned (1 admit) |

The first chapter is intended as a proof-of-concept for the format:
each definition and statement appears twice (informal + formal),
with the formal block clickable through to GitHub.

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
