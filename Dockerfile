# syntax=docker/dockerfile:1
#
# Self-contained image to run Claude Code on the mathcomp-eulerian Rocq
# refactor described in COMPILE_ALL_REFACTOR_PLAN.md.
#
# Toolchain matches the host snapshot in that plan:
#   Rocq 9.1.1, OCaml 5.2.x,
#   mathcomp-{ssreflect,fingroup,algebra} 2.5.0,
#   coq-lsp 0.2.5+9.1 (provides pet-server),
#   rocq-mcp from github.com/LLM4Rocq/rocq-mcp.
#
# Build:
#   docker build -t mathcomp-eulerian-claude .
#
# Run (autonomous Claude with rocq-mcp tools, project + login mounted):
#   docker run --rm -it \
#     -v "$(pwd)":/workspace \
#     -v "$HOME/.claude":/home/opam/.claude \
#     mathcomp-eulerian-claude
#
# The MCP config is baked into the image at /etc/claude/mcp.json and
# loaded via `claude --mcp-config` in the entrypoint. Nothing about MCP
# lives on the host disk, so host `claude` runs in this directory are
# unaffected. Do NOT mount your host `~/.claude.json` over the
# container's home — its global rocq-mcp entry references a host venv
# path that does not exist inside the image.
#
# Plain shell instead of Claude:
#   docker run --rm -it -v "$(pwd)":/workspace \
#     --entrypoint bash mathcomp-eulerian-claude

FROM ocaml/opam:debian-12-ocaml-5.2

# ----- system deps + Node.js (Claude Code) + Python 3.11 (rocq-mcp) ----
USER root
RUN apt-get update \
 && apt-get install -y --no-install-recommends \
      curl ca-certificates git make m4 pkg-config \
      libgmp-dev ripgrep \
      python3 python3-venv python3-pip \
 && curl -fsSL https://deb.nodesource.com/setup_20.x | bash - \
 && apt-get install -y --no-install-recommends nodejs \
 && rm -rf /var/lib/apt/lists/*

# ----- Claude Code CLI -------------------------------------------------
RUN npm install -g @anthropic-ai/claude-code

# ----- Rocq 9.1.1 + mathcomp 2.5.0 + coq-lsp 0.2.5+9.1 -----------------
# coq-lsp ships pet-server, which pytanque (and so rocq-mcp) shells out
# to. coq-core supplies the `coqc` shim that rocq-mcp expects by default.
USER opam
WORKDIR /home/opam

RUN opam update \
 && opam repo add coq-released https://coq.inria.fr/opam/released \
 && opam install -y \
      rocq-core.9.1.1 \
      coq-core.9.1.1 \
      rocq-mathcomp-ssreflect.2.5.0 \
      rocq-mathcomp-fingroup.2.5.0 \
      rocq-mathcomp-algebra.2.5.0 \
      rocq-mathcomp-classical.1.16.0 \
      coq-lsp.0.2.5+9.1 \
 && opam clean -a -c -s --logs

# Auto-load opam env for every shell, including the entrypoint's `bash -lc`.
# Claude inherits PATH from this shell, so rocq-mcp's subprocesses (pet-server,
# coqc, rocq) resolve without per-server env wiring.
RUN echo 'eval $(opam env)' >> /home/opam/.profile \
 && echo 'eval $(opam env)' >> /home/opam/.bashrc

# ----- rocq-mcp: clone + venv install ----------------------------------
USER root
RUN mkdir -p /opt/rocq-mcp && chown opam:opam /opt/rocq-mcp
USER opam
RUN git clone --depth 1 https://github.com/LLM4Rocq/rocq-mcp.git /opt/rocq-mcp \
 && python3 -m venv /opt/rocq-mcp/.venv \
 && /opt/rocq-mcp/.venv/bin/pip install --no-cache-dir --upgrade pip \
 && /opt/rocq-mcp/.venv/bin/pip install --no-cache-dir /opt/rocq-mcp

# ----- MCP config (image-resident; not in the bind-mounted /workspace) -
USER root
RUN mkdir -p /etc/claude
COPY <<'EOF' /etc/claude/mcp.json
{
  "mcpServers": {
    "rocq-mcp": {
      "type": "stdio",
      "command": "/opt/rocq-mcp/.venv/bin/rocq-mcp",
      "args": [],
      "env": {}
    }
  }
}
EOF

# ----- workspace -------------------------------------------------------
USER opam
WORKDIR /workspace

ENTRYPOINT ["/bin/bash", "-lc", "exec claude --mcp-config /etc/claude/mcp.json --dangerously-skip-permissions \"$@\"", "--"]
CMD []
