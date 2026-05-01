#!/usr/bin/env python3
"""End-to-end verification driver for examples/.

For each `examples/<name>.py` paired with `examples/<name>.lean`, this
script:

  1. Runs `monty --emit-ir <file.py>` to produce the prepared IR JSON.
  2. Runs `montyverification --codegen <ir.json> <out.lean>` to lower
     the IR to a Lean source file with concrete `def`s and an
     `«__module__»` term.
  3. Concatenates the codegen output with the matching `.lean`
     properties file. The properties file references names like
     `«__module__»`, `make_adder`, `task1`, etc. that the codegen
     introduces above it.
  4. Runs `lean` on the concatenated file. If every `example` /
     `theorem` discharges, the example is verified end-to-end.

Usage:
    uv run examples/run_examples.py            # run all examples
    uv run examples/run_examples.py closure_factory  # run one
    uv run examples/run_examples.py --verbose

Exit code is 0 iff every example verified.
"""

import argparse
import os
import shutil
import subprocess
import sys
import tempfile
from concurrent.futures import ProcessPoolExecutor, as_completed
from pathlib import Path

EXAMPLES_DIR = Path(__file__).parent
PROJECT_DIR = EXAMPLES_DIR.parent
MONTY_BIN = (
    PROJECT_DIR.parent / "monty" / "target" / "debug" / "monty"
)
MV_BIN = PROJECT_DIR / ".lake" / "build" / "bin" / "montyverification"


def find_lean_bin() -> Path:
    """Locate the `lean` executable used by the project's toolchain."""
    tc = (
        Path.home()
        / ".elan"
        / "toolchains"
        / "leanprover--lean4---v4.29.0"
        / "bin"
        / "lean"
    )
    if tc.exists():
        return tc
    elan = Path.home() / ".elan" / "bin" / "lean"
    if elan.exists():
        return elan
    found = shutil.which("lean")
    if found:
        return Path(found)
    raise FileNotFoundError("could not find `lean` binary in elan or PATH")


def get_lean_path() -> str:
    """Resolve LEAN_PATH by asking lake once."""
    result = subprocess.run(
        ["lake", "env", "bash", "-c", "echo $LEAN_PATH"],
        capture_output=True,
        text=True,
        cwd=str(PROJECT_DIR),
    )
    return result.stdout.strip()


def emit_ir(py_path: Path) -> str:
    """Run `monty --emit-ir <py_path>` and return the JSON as a string."""
    result = subprocess.run(
        [str(MONTY_BIN), "--emit-ir", str(py_path)],
        capture_output=True,
        text=True,
    )
    if result.returncode != 0:
        raise RuntimeError(
            f"monty --emit-ir failed for {py_path}:\n{result.stderr}"
        )
    return result.stdout


def codegen(ir_json: str, out_lean: Path, source_path: Path | None = None) -> None:
    """Pipe the IR JSON to `montyverification --codegen` to produce a Lean file.

    If `source_path` is provided, pass `--source <path>` so the codegen
    can scan the Python file for `# external: <name> <effects>`
    directives that extend the hardcoded externals table.
    """
    with tempfile.NamedTemporaryFile(
        mode="w", suffix=".json", delete=False
    ) as tmp:
        tmp.write(ir_json)
        tmp_path = tmp.name
    try:
        cmd = [str(MV_BIN), "--codegen", tmp_path, str(out_lean)]
        if source_path is not None:
            cmd.extend(["--source", str(source_path)])
        result = subprocess.run(cmd, capture_output=True, text=True)
        if result.returncode != 0:
            raise RuntimeError(
                f"montyverification --codegen failed:\n{result.stderr}"
            )
    finally:
        os.unlink(tmp_path)


def concat_files(generated: Path, props: Path) -> str:
    """Combine the codegen output with the properties file. The
    properties file is appended verbatim, so the names defined by the
    generated portion are in scope for the theorems."""
    return generated.read_text() + "\n\n" + props.read_text()


def run_lean(combined_path: Path, lean_bin: Path, lean_path: str) -> tuple[bool, str]:
    """Run `lean` on the combined file. Returns (passed, output)."""
    env = os.environ.copy()
    env["LEAN_PATH"] = lean_path
    result = subprocess.run(
        [str(lean_bin), str(combined_path)],
        capture_output=True,
        text=True,
        env=env,
    )
    return result.returncode == 0, (result.stdout + result.stderr)


def _extract_property_titles(props_text: str) -> list[str]:
    """Extract a one-line summary for each `example`/`theorem` in the
    properties file. The summary is the first sentence of the
    immediately-preceding `/-- ... -/` doc-comment, if one exists
    immediately above the declaration; otherwise "(unnamed)".
    Returns one entry per declaration in file order."""
    lines = props_text.splitlines()
    out: list[str] = []
    for i, ln in enumerate(lines):
        s = ln.lstrip()
        if not (s.startswith("example ") or s.startswith("example:") or
                s.startswith("theorem ")):
            continue
        # Walk backward at most 12 lines, skipping blank lines, looking
        # for a doc-comment that ends ON the line just above the decl.
        title = None
        j = i - 1
        # Skip blanks.
        while j >= 0 and not lines[j].strip():
            j -= 1
        if j < 0:
            out.append("(unnamed)")
            continue
        prev = lines[j].rstrip()
        if prev.endswith("-/") and "/--" in prev:
            # Single-line: `/-- foo -/`.
            inner = prev.split("/--", 1)[1]
            inner = inner.rsplit("-/", 1)[0].strip()
            title = inner
        elif prev.endswith("-/") and not prev.endswith("!-/"):
            # Multi-line ending here. Walk back to `/--`. Bail out if
            # we hit another declaration or a section marker before
            # finding it (the `-/` we saw belonged to something else).
            buf = [prev[:-2].strip()]
            k = j - 1
            found = False
            while k >= 0 and k > i - 12:
                line = lines[k]
                stripped_l = line.lstrip()
                if "/--" in line:
                    head = line.split("/--", 1)[1].strip()
                    buf.append(head)
                    found = True
                    break
                if stripped_l.startswith("/-!") or stripped_l.startswith("example") or \
                   stripped_l.startswith("theorem") or stripped_l.startswith("def "):
                    # Crossed a boundary; the `-/` wasn't a doc-comment for us.
                    break
                buf.append(line.strip())
                k -= 1
            if found:
                title = " ".join(reversed([b for b in buf if b])).strip()
        if not title:
            title = "(unnamed)"
        # Trim to first sentence.
        for sep in (". ", " — ", "."):
            if sep in title:
                title = title.split(sep, 1)[0]
                break
        out.append(title)
    return out


def run_example(name: str, lean_bin: Path, lean_path: str, verbose: bool,
                emit=None, list_properties: bool = False) -> bool:
    """Run a single example end-to-end. Returns True on success.

    `emit` is called with each progress line. Defaults to stdout, but
    parallel callers pass a buffering callback so output for each
    example stays grouped instead of interleaving across workers.
    """
    if emit is None:
        emit = lambda line: print(line, flush=True)

    py_path = EXAMPLES_DIR / f"{name}.py"
    props_path = EXAMPLES_DIR / f"{name}.lean"

    if not py_path.exists():
        emit(f"  [SKIP] {name}: no .py file at {py_path}")
        return False
    if not props_path.exists():
        emit(f"  [SKIP] {name}: no .lean properties file at {props_path}")
        return False

    emit(f"  [{name}] emitting IR...")
    try:
        ir_json = emit_ir(py_path)
    except RuntimeError as e:
        emit(f"  [FAIL] {name}: {e}")
        return False

    with tempfile.TemporaryDirectory(prefix=f"mv_example_{name}_") as td:
        td = Path(td)
        gen_lean = td / f"{name}_generated.lean"
        combined = td / f"{name}_combined.lean"

        emit(f"  [{name}] codegenning Lean...")
        try:
            codegen(ir_json, gen_lean, source_path=py_path)
        except RuntimeError as e:
            emit(f"  [FAIL] {name}: {e}")
            return False

        combined.write_text(concat_files(gen_lean, props_path))

        # Negative examples (expect-fail): if the .lean props file
        # contains a "-- EXPECT: type-error" marker, the example
        # passes iff Lean REJECTS the file. This is for demonstrating
        # protocol-violation cases that should be statically caught.
        props_text = props_path.read_text()
        expect_fail = "-- EXPECT: type-error" in props_text

        if verbose:
            emit(f"  [{name}] combined file: {combined}")
            emit(f"  [{name}] (showing first 80 lines)")
            for i, line in enumerate(combined.read_text().splitlines()[:80], 1):
                emit(f"    {i:3} {line}")

        emit(f"  [{name}] verifying with lean...")
        passed, output = run_lean(combined, lean_bin, lean_path)

        if expect_fail:
            if passed:
                emit(
                    f"  [FAIL] {name}: expected Lean to reject this file but it accepted it"
                )
                return False
            else:
                emit(
                    f"  [ OK ] {name}: Lean correctly rejected the file (expected failure)"
                )
                return True

        if passed:
            # Count `theorem`/`example` declarations in the **properties**
            # file (not the codegen output) so the reported number is the
            # user-facing count of verified propositions, not codegen
            # boilerplate. Lean's silent-on-success means a successful
            # compile witnesses that every declaration elaborated.
            theorems = 0
            for ln in props_path.read_text().splitlines():
                stripped = ln.lstrip()
                if stripped.startswith("theorem ") or stripped.startswith("example "):
                    theorems += 1
            tag = f"{theorems} verified" if theorems else "all properties verified"
            emit(f"  [ OK ] {name}: {tag}")
            if list_properties and theorems > 0:
                titles = _extract_property_titles(props_path.read_text())
                for i, title in enumerate(titles, 1):
                    short = title if len(title) <= 80 else title[:77] + "..."
                    emit(f"         [{i}] {short}")
            return True
        else:
            emit(f"  [FAIL] {name}: lean rejected the file")
            # Show only the error lines, not warnings
            for line in output.splitlines():
                if "error" in line.lower() and "warning" not in line.lower():
                    emit(f"         {line}")
            return False


def _run_one_buffered(args: tuple) -> tuple[str, bool, list[str]]:
    """Worker entry point for parallel mode. Buffers output so that
    stdout from concurrent workers doesn't interleave."""
    name, lean_bin, lean_path, verbose, list_properties = args
    buf: list[str] = []
    ok = run_example(name, lean_bin, lean_path, verbose, emit=buf.append,
                     list_properties=list_properties)
    return name, ok, buf


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "examples",
        nargs="*",
        help="specific example names to run (default: all examples in examples/)",
    )
    parser.add_argument(
        "-v", "--verbose", action="store_true", help="show combined file head"
    )
    parser.add_argument(
        "-j", "--jobs", type=int, default=os.cpu_count() or 4,
        help="parallel worker count (default: number of CPUs). Use -j 1 to run serially.",
    )
    parser.add_argument(
        "--watch", action="store_true",
        help="poll examples/*.py and *.lean for changes and re-run on edit",
    )
    parser.add_argument(
        "--list-properties", action="store_true",
        help="for each verified example, also print one bullet per `example`/`theorem` declaration",
    )
    args = parser.parse_args()

    # Sanity-check binaries.
    if not MONTY_BIN.exists():
        print(
            f"error: monty binary not found at {MONTY_BIN}\n"
            f"  Build with: cd {MONTY_BIN.parent.parent.parent} && cargo build",
            file=sys.stderr,
        )
        return 2
    if not MV_BIN.exists():
        print(
            f"error: montyverification binary not found at {MV_BIN}\n"
            f"  Build with: lake build",
            file=sys.stderr,
        )
        return 2

    lean_bin = find_lean_bin()
    lean_path = get_lean_path()

    # Discover examples: any .py file in examples/ that has a matching .lean.
    if args.examples:
        names = args.examples
    else:
        names = sorted(
            p.stem
            for p in EXAMPLES_DIR.glob("*.py")
            if (EXAMPLES_DIR / f"{p.stem}.lean").exists()
            and p.stem != "run_examples"
        )

    if not names:
        print("No examples found.", file=sys.stderr)
        return 1

    workers = max(1, min(args.jobs, len(names)))

    def run_pass() -> tuple[int, list[str]]:
        return _do_run(names, lean_bin, lean_path, args.verbose, workers,
                       args.list_properties)

    if args.watch:
        return _watch_loop(names, run_pass)

    print(
        f"Running {len(names)} examples through monty → codegen → lean "
        f"({workers} worker{'s' if workers > 1 else ''})"
    )
    passed, failed = run_pass()
    print()
    print(f"=== Examples: {passed} / {len(names)} verified ===")
    if failed:
        print("Failed:")
        for n in failed:
            print(f"  - {n}")
        return 1
    return 0


def _do_run(names: list[str], lean_bin: Path, lean_path: str, verbose: bool,
            workers: int, list_properties: bool = False) -> tuple[int, list[str]]:
    passed = 0
    failed: list[str] = []
    if workers <= 1:
        for name in names:
            if run_example(name, lean_bin, lean_path, verbose,
                           list_properties=list_properties):
                passed += 1
            else:
                failed.append(name)
    else:
        worker_args = [(n, lean_bin, lean_path, verbose, list_properties) for n in names]
        with ProcessPoolExecutor(max_workers=workers) as ex:
            futures = {ex.submit(_run_one_buffered, wa): wa[0] for wa in worker_args}
            for fut in as_completed(futures):
                name, ok, lines = fut.result()
                for line in lines:
                    print(line, flush=True)
                if ok:
                    passed += 1
                else:
                    failed.append(name)
    return passed, failed


def _watch_loop(names: list[str], run_pass) -> int:
    """Polling-based file watch. Re-runs `run_pass` whenever any of the
    `examples/<name>.py` or `<name>.lean` files (plus `run_examples.py`
    itself) changes mtime. Pure stdlib — no inotify dependency.
    """
    import time

    watched: list[Path] = []
    for n in names:
        for ext in (".py", ".lean"):
            p = EXAMPLES_DIR / f"{n}{ext}"
            if p.exists():
                watched.append(p)
    watched.append(EXAMPLES_DIR / "run_examples.py")

    def snapshot() -> dict[Path, float]:
        return {p: p.stat().st_mtime for p in watched if p.exists()}

    print(f"Watching {len(watched)} files for changes (Ctrl-C to exit)...")
    last = snapshot()
    # Initial run.
    passed, failed = run_pass()
    print()
    print(f"=== Examples: {passed} / {len(names)} verified ===")
    if failed:
        print("Failed:")
        for n in failed:
            print(f"  - {n}")
    print()
    print("Watching for changes...")
    try:
        while True:
            time.sleep(0.5)
            cur = snapshot()
            changed = [p for p in cur if cur[p] != last.get(p)]
            if changed:
                print()
                print(f"Change detected in: {', '.join(p.name for p in changed)}")
                last = cur
                passed, failed = run_pass()
                print()
                print(f"=== Examples: {passed} / {len(names)} verified ===")
                if failed:
                    print("Failed:")
                    for n in failed:
                        print(f"  - {n}")
                print()
                print("Watching for changes...")
    except KeyboardInterrupt:
        print()
        print("Stopped.")
        return 0


if __name__ == "__main__":
    sys.exit(main())
