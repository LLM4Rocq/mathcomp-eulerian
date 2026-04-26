---
name: Apptainer environment constraints
description: Code runs inside an apptainer container with read-only $HOME; caches and writable paths must live under the project dir
type: project
originSessionId: c53b60b8-d16f-4402-a246-4ee738ea1611
---
Work in this repo runs inside an apptainer container. `$HOME` (`/home/lelarge`) is read-only, so anything that wants to write to `~/.cache`, `~/.config`, etc. will fail with "Read-only file system (os error 30)".

**Why:** user runs Claude Code / tooling from inside the container; host-side home isn't writable from within.

**How to apply:** when configuring tools that need cache/state dirs (uv, pip, npm, etc.), redirect them under `/scratch/lelarge/mathcomp-eulerian/` (typically `.cache/` inside the project) rather than `/scratch/lelarge/` or `$HOME`. Example: `UV_CACHE_DIR=/scratch/lelarge/mathcomp-eulerian/.cache/uv`, `XDG_CACHE_HOME=/scratch/lelarge/mathcomp-eulerian/.cache`. Don't suggest fixes that write outside the project directory.
