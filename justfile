# Machine settings such as LEAN_MATHLIB may be kept in a local .env file.
set dotenv-load

python := env("PYTHON", "python3")

default: build

# Validated PDF, with cached no-op when source files have not changed.
build:
    {{python}} scripts/project.py build

# CI gate: format, lint, PDF links/layout, tests, corrections.
check:
    {{python}} scripts/project.py check

# Formatter check, source rules and the evaluated document (T000-T099).
lint:
    {{python}} scripts/project.py lint

# Format the Typst sources in place (Typstyle with the Tinymist settings).
fmt:
    {{python}} scripts/project.py fmt

# Unit tests: corrections schema, labels, bibliography, numbering, lint rules.
test:
    {{python}} scripts/project.py test

# The reader's list of corrections: build/curtis-repr.1.corrections.pdf
corrections:
    {{python}} scripts/project.py corrections

# Remove build/ and the build cache (`cache` in config/project.json).
clean:
    {{python}} scripts/project.py clean

# Advisory prose check (Harper); dictionary and rules shared with VS Code.
check-prose:
    {{python}} scripts/check_prose.py

# Validate the PDF exported by the editor using the same Python setting.
editor-prepare:
    {{python}} scripts/project.py editor-prepare

editor-finish:
    {{python}} scripts/project.py editor-finish

# Exact algebra and finite-group checks with the installed SageMath.
check-sage:
    sage -python checks/sage/tensor-matrices.py
    sage -python checks/sage/quaternion-odd-component.py
    sage -python checks/sage/cover-and-indicator.py

# Compile and audit declarations using the pinned Lean environment.
check-lean:
    {{python}} checks/lean/check_axioms.py
