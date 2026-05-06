#!/usr/bin/env python3
"""
extract_catalog.py — generate lemma_catalog.tex from .v files in _CoqProject.

For every named result (Definition/Lemma/Theorem/Corollary/Proposition/Fact/
Fixpoint/Inductive) in the active build chain, emit a LaTeX entry containing:

  - The name (clickable link to GitHub).
  - The kind and line number.
  - The (** ... *) coqdoc docstring above the result, if any.
  - A "narrated in Ch X" badge if the result is covered in the PDF's
    narrative chapters.

Output: lemma_catalog.tex, intended to be \\input from eulerian_formal.tex.
"""

from __future__ import annotations
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent.parent  # /workspace
COQPROJECT = ROOT / "_CoqProject"
OUTPUT = Path(__file__).resolve().parent / "lemma_catalog.tex"

GITHUB_BASE = "https://github.com/LLM4Rocq/mathcomp-eulerian/blob/main"

# Map: result name -> "Ch X §Y" narration label.
NARRATION = {
    # Chapter 2: cycles
    "cycle_count": "Ch 2 §2.1",
    "stirling_c": "Ch 2 §2.2",
    "cycle_count_le": "Ch 2 §2.1",
    "cycle_count_id": "Ch 2 §2.1",
    "stirling_c_row_sum_fact": "Ch 2 §2.2",
    "stirling_c_rec": "Ch 2 §2.2",
    # Chapter 3: inversions, maj
    "is_inv": "Ch 3 §3.1",
    "inv_set": "Ch 3 §3.1",
    "inv": "Ch 3 §3.1",
    "maj": "Ch 3 §3.2",
    "inv_id": "Ch 3 §3.1",
    "inv_le": "Ch 3 §3.1",
    "inv_rev_perm": "Ch 3 §3.1",
    "maj_le": "Ch 3 §3.2",
    "coinv_set": "Ch 3 §3.1",
    # Chapter 4: Foata
    "foata_step": "Ch 4 §4.1",
    "foata": "Ch 4 §4.1",
    "foata_perm": "Ch 4 §4.2",
    "foata_perm_inv_maj": "Ch 4 §4.3",
    "foata_perm_inj": "Ch 4 §4.3",
    "inv_maj_equidistr": "Ch 4 §4.3",
    "is_desc_seq": "Ch 4 §4.1",
    "maj_seq": "Ch 4 §4.1",
    "inv_seq": "Ch 4 §4.1",
    # Chapter 5: descents, Eulerian, beta
    "is_descent": "Ch 5 §5.1",
    "descent_set": "Ch 5 §5.1",
    "des": "Ch 5 §5.1",
    "asc": "Ch 5 §5.1",
    "des_le": "Ch 5 §5.1",
    "des_id": "Ch 5 §5.1",
    "rev_perm": "Ch 5 §5.2",
    "rev_perm_ord": "Ch 5 §5.2",
    "is_descent_rev": "Ch 5 §5.2",
    "eulerian": "Ch 5 §5.3",
    "insert_max_perm": "Ch 5 §5.4",
    "insert_max_fun": "Ch 5 §5.4",
    "extract_max_perm": "Ch 5 §5.4",
    "extract_max_fun": "Ch 5 §5.4",
    "insert_max_perm_bij": "Ch 5 §5.4",
    "eulerian_rec": "Ch 5 §5.5",
    "eulerian_row_sum_fact": "Ch 5 §5.3",
    "eulerian_out_of_range": "Ch 5 §5.3",
    "des0_id": "Ch 5 §5.3",
    "beta": "Ch 5 §5.6",
    "beta_eulerian": "Ch 5 §5.6",
    "beta_rev": "Ch 5 §5.6",
    # Chapter 6: q-analogues
    "q_int": "Ch 6 §6.1",
    "q_fact": "Ch 6 §6.1",
    "inv_q_fact": "Ch 6 §6.1",
    "maj_q_fact": "Ch 6 §6.1",
    "q_eul_pol": "Ch 6 §6.2",
    "eul_pol": "Ch 6 §6.2",
    "q_eul_pol_t1": "Ch 6 §6.2",
    "q_eul_pol_q1": "Ch 6 §6.2",
    "q1_subst": "Ch 6 §6.2",
    # Chapter 7: alt subseq
    "is_turn": "Ch 7 §7.1",
    "turn_count": "Ch 7 §7.1",
    "is_alt": "Ch 7 §7.2",
    "perm_seq": "Ch 7 §7.2",
    "pick_seq": "Ch 7 §7.2",
    "as_perm_max": "Ch 7 §7.3",
    "as_perm": "Ch 7 §7.3",
    "as_perm_max_eq": "Ch 7 §7.4",
    # Chapter 8: toggle, omega, headline
    "sym_diff": "Ch 8 §8.1",
    "toggle_at": "Ch 8 §8.1",
    "omega_set": "Ch 8 §8.2",
    "alt_desc_set": "Ch 8 §8.3",
    "set_is_alt": "Ch 8 §8.3",
    "compl_perm": "Ch 8 §8.4",
    "descent_set_compl": "Ch 8 §8.4",
    "beta_compl": "Ch 8 §8.4",
    "set_is_alt_classify": "Ch 8 §8.4",
    "omega_proper_beta_lt": "Ch 8 §8.5",
    "beta_alt_max": "Ch 8 §8.6",
}

KEYWORDS = (
    "Definition",
    "Theorem",
    "Lemma",
    "Corollary",
    "Proposition",
    "Fact",
    "Fixpoint",
    "Inductive",
)
KEYWORD_RE = re.compile(
    r"^\s*(" + "|".join(KEYWORDS) + r")\s+([A-Za-z_][A-Za-z0-9_']*)\b"
)


def read_file_list() -> list[str]:
    """Read .v file list from _CoqProject (one per line, comments out)."""
    files = []
    for raw in COQPROJECT.read_text().splitlines():
        line = raw.strip()
        if not line or line.startswith("#") or line.startswith("-"):
            continue
        if line.endswith(".v"):
            files.append(line)
    return files


def strip_block_comments(text: str) -> str:
    """Remove non-coqdoc (* ... *) comments, preserving (** ... *) and newlines."""
    out = []
    i = 0
    n = len(text)
    while i < n:
        if text[i:i+3] == "(**":
            # Coqdoc comment: keep as-is, but we'll re-extract below.
            j = i
            depth = 1
            j += 3
            while j < n and depth > 0:
                if text[j:j+2] == "(*":
                    depth += 1
                    j += 2
                elif text[j] == "*" and j + 1 < n and text[j+1] == ")":
                    depth -= 1
                    j += 2
                else:
                    j += 1
            out.append(text[i:j])
            i = j
        elif text[i:i+2] == "(*":
            # Plain comment: strip but preserve newlines.
            j = i + 2
            depth = 1
            while j < n and depth > 0:
                if text[j:j+2] == "(*":
                    depth += 1
                    j += 2
                elif text[j] == "*" and j + 1 < n and text[j+1] == ")":
                    depth -= 1
                    j += 2
                else:
                    j += 1
            chunk = text[i:j]
            out.append("".join(c if c == "\n" else " " for c in chunk))
            i = j
        else:
            out.append(text[i])
            i += 1
    return "".join(out)


def parse_file(path: Path) -> list[dict]:
    """
    Parse a .v file and return a list of named-result records:
       {kind, name, line, docstring}
    The line is 1-indexed, pointing to the line with the keyword.
    The docstring is the most recent (** ... *) block ending immediately
    above the keyword (with only blank lines / Section/Variable/Implicit
    declarations between).
    """
    raw = path.read_text()
    lines = raw.splitlines()
    n = len(lines)

    # Find all (** ... *) blocks: (start_line, end_line, content)
    docstrings = []
    i = 0
    while i < n:
        line = lines[i]
        idx = line.find("(**")
        if idx >= 0:
            start = i
            content = []
            text = line[idx + 3:]
            while True:
                end = text.find("*)")
                if end >= 0:
                    content.append(text[:end])
                    end_line = i
                    break
                content.append(text)
                i += 1
                if i >= n:
                    end_line = n - 1
                    break
                text = lines[i]
            docstrings.append((start, end_line, "\n".join(content).strip()))
        i += 1

    # Strip plain comments to identify keyword positions.
    stripped = strip_block_comments(raw)
    stripped_lines = stripped.splitlines()

    # Track whether we're inside Proof. ... Qed.|Defined.|Admitted.
    proof_re = re.compile(r"\bProof\b")
    end_re = re.compile(r"\b(Qed|Defined|Admitted|Abort)\b")
    in_proof = False
    results = []
    for lineno, sline in enumerate(stripped_lines, start=1):
        proof_starts = bool(proof_re.search(sline))
        proof_ends = bool(end_re.search(sline))
        if not in_proof:
            m = KEYWORD_RE.match(sline)
            if m:
                kind = m.group(1)
                name = m.group(2)
                if not name.startswith("_") and name != "Implicit":
                    # Find the most recent docstring whose end line is just
                    # above this keyword, allowing only blank lines and
                    # ssreflect declarations in between.
                    doc = None
                    for _ds_start, ds_end, content in docstrings:
                        if ds_end >= lineno:
                            break
                        # gap = lines strictly between docstring end and keyword.
                        # ds_end is 0-indexed; lineno is 1-indexed.
                        gap_lines = lines[ds_end + 1:lineno - 1]
                        allowed = True
                        for gl in gap_lines:
                            gs = gl.strip()
                            if not gs:
                                continue
                            if gs.startswith(("Section ", "End ", "Variable",
                                               "Variables", "Hypothesis",
                                               "Implicit", "Open ", "Close ",
                                               "Set ", "Unset ", "From ",
                                               "Import ", "Module ", "(**",
                                               "Notation ", "Local ", "Reserved ",
                                               "Arguments ", "Hint ")):
                                continue
                            if gs == "*)":
                                continue
                            allowed = False
                            break
                        if allowed:
                            doc = content
                    results.append({
                        "kind": kind, "name": name, "line": lineno,
                        "docstring": doc,
                    })
            # Did the line both start AND end a proof in one go
            # (e.g. "Proof. by []. Qed.")?  If so, stay out of proof mode.
            if proof_starts and not proof_ends:
                in_proof = True
        else:
            if proof_ends:
                in_proof = False
    return results


def file_to_chapter_label(path: str, narration_hits: list[str]) -> str | None:
    """If any narrated result lives in this file, name the chapter section."""
    chapters = set()
    for name in narration_hits:
        label = NARRATION.get(name)
        if label:
            chapters.add(label.split(" ")[1])  # "Ch", "X" → "X"
    return None  # not used currently


def latex_escape(s: str) -> str:
    """Escape LaTeX special characters in the docstring text."""
    if not s:
        return ""
    # Coqdoc [bracketed] code becomes \texttt{...}.
    # Apply that first, before generic escaping (so that %, _ etc inside
    # [brackets] go into texttt unescaped — \texttt protects them).
    out = []
    i = 0
    n = len(s)
    while i < n:
        if s[i] == "[":
            # Find matching close bracket on the same logical scope.
            j = s.find("]", i + 1)
            if j > 0 and j - i < 120:
                code = s[i+1:j]
                # Wrap in \texttt + \detokenize so underscores, #, etc.
                # survive without catcode interpretation.  We still escape
                # closing brace which would terminate \detokenize itself.
                if "}" in code or "{" in code:
                    # Fall back to manual escaping (rare).
                    code = code.replace("\\", r"\textbackslash{}")
                    code = code.replace("_", r"\_")
                    code = code.replace("#", r"\#")
                    code = code.replace("%", r"\%")
                    code = code.replace("&", r"\&")
                    code = code.replace("~", r"\textasciitilde{}")
                    code = code.replace("^", r"\textasciicircum{}")
                    code = code.replace("$", r"\$")
                    code = code.replace("{", r"\{")
                    code = code.replace("}", r"\}")
                    out.append(r"\texttt{" + code + "}")
                else:
                    out.append(r"\texttt{\detokenize{" + code + "}}")
                i = j + 1
                continue
        c = s[i]
        if c == "\\":
            out.append(r"\textbackslash{}")
        elif c == "_":
            out.append(r"\_")
        elif c == "#":
            out.append(r"\#")
        elif c == "%":
            out.append(r"\%")
        elif c == "&":
            out.append(r"\&")
        elif c == "$":
            out.append(r"\$")
        elif c == "{":
            out.append(r"\{")
        elif c == "}":
            out.append(r"\}")
        elif c == "~":
            out.append(r"\textasciitilde{}")
        elif c == "^":
            out.append(r"\textasciicircum{}")
        else:
            out.append(c)
        i += 1
    return "".join(out)


def emit_latex(by_file: dict[str, list[dict]]) -> str:
    """Render the catalog into a single LaTeX appendix chapter."""
    parts = []
    parts.append(r"% Auto-generated by extract_catalog.py — do not edit by hand.")
    parts.append("")
    parts.append(r"% =====================================================================")
    parts.append(r"\chapter{Comprehensive lemma catalog}")
    parts.append(r"\label{app:catalog}")
    parts.append(r"% =====================================================================")
    parts.append("")
    parts.append(r"This appendix lists \emph{every} named result in the active build")
    parts.append(r"chain --- {} entries across {} files. Each entry shows the kind".format(
        sum(len(v) for v in by_file.values()),
        len(by_file),
    ))
    parts.append(r"(\texttt{Definition}, \texttt{Lemma}, \dots), the file:line")
    parts.append(r"location (clickable to GitHub), and the \texttt{coqdoc}")
    parts.append(r"docstring extracted from the source. Entries narrated in the")
    parts.append(r"main chapters of this document carry a chapter/section badge.")
    parts.append("")
    parts.append(r"This catalog is generated mechanically from the \texttt{.v}")
    parts.append(r"files; see \texttt{docs/formal/extract\_catalog.py}. Adding a")
    parts.append(r"docstring to a \texttt{.v} file improves both the catalog and")
    parts.append(r"the deployed coqdoc HTML at the same time.")
    parts.append("")

    for filename in sorted(by_file.keys()):
        results = by_file[filename]
        parts.append(r"% --------------------------------------------")
        parts.append(r"\section*{\texttt{" + latex_escape(filename) + "}}")
        parts.append(r"\addcontentsline{toc}{section}{\texttt{" + latex_escape(filename) + "}}")
        parts.append("")
        parts.append(r"\begin{description}")
        for r in results:
            # URL needs \detokenize to survive both # and _.  The visible
            # \texttt{...} body uses \detokenize{name} to print underscores
            # safely (see preamble's \rocqsource for the same pattern).
            url_path = f"{filename}#L{r['line']}"
            href = (
                r"\href{" + GITHUB_BASE + "/"
                + r"\detokenize{" + url_path + r"}"
                + r"}{\texttt{\detokenize{" + r["name"] + r"}}}"
            )
            badge = NARRATION.get(r["name"], None)
            badge_str = (
                r" \textsf{[" + (badge or "aux") + "]}"
            )
            kind_line = (
                r"\emph{" + r["kind"] + r", line " + str(r["line"]) + r"}."
                + badge_str
            )
            doc = r["docstring"] or "(no docstring)"
            doc_escaped = latex_escape(doc.replace("\n", " ").strip())
            parts.append(r"\item[" + href + r"] " + kind_line + r" \\")
            parts.append("  " + doc_escaped)
            parts.append("")
        parts.append(r"\end{description}")
        parts.append("")
    return "\n".join(parts)


def main() -> int:
    files = read_file_list()
    by_file: dict[str, list[dict]] = {}
    total = 0
    for fname in files:
        path = ROOT / fname
        if not path.exists():
            print(f"WARN: missing {fname}", file=sys.stderr)
            continue
        records = parse_file(path)
        if not records:
            continue
        by_file[fname] = records
        total += len(records)
    OUTPUT.write_text(emit_latex(by_file))
    print(f"Wrote {OUTPUT} with {total} entries across {len(by_file)} files.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
