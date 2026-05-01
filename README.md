# MontyVerification

Formal verification of Python programs in Lean 4. Given a Python
file, MontyVerification translates it to Lean source code where each
function's effect set (network, filesystem, environment, time) is
encoded in the type. If the generated file compiles, the effects are
correct. The system also extracts a symbolic AST that supports
machine-checked ordering proofs on tool calls — all without modifying
the Python source.

## What gets verified

| Property | How it works | Example |
|---|---|---|
| **Effect safety** | Each function's type carries its effect set. Lean's type checker rejects mismatches. | `agent_research_pipeline.py` |
| **Effect inference** | Unannotated functions get effects inferred from the call graph. No `Pure[]`/`Effect[]` needed. | `agent_no_annotations.py` |
| **Ordering invariants** | "approval before payment on every path" — decided by `native_decide` over the emitted `EffAST`. | `agent_payment_workflow.py` |
| **Bug detection** | A branch that skips a required step makes the ordering theorem provably false. | `agent_payment_buggy.py` |
| **Cross-function ordering** | `calledBeforeInter` inlines helper ASTs to verify ordering across function boundaries. | `agent_async_pipeline.py` |
| **Resource guarantees** | "every path calls `close_source`" via `eventuallyCalls`. | `agent_property_zoo.py` |
| **Exactly-once** | "no double-fetch" via `calledExactlyOnce`. | `agent_property_zoo.py` |
| **Computational reduction** | Pure functions actually execute in Lean's kernel. `trim("hello world", 5) = "hello"`. | `agent_no_annotations.py` |
| **Async / gather** | Pure coroutines composed via `asyncio.gather` reduce to concrete values. | `agent_async_orchestrator.py` |
| **Custom tool APIs** | Declare your own externals via `# external: name effects` comments. | `agent_custom_externals.py` |
| **Custom effect kinds** | Add domain-specific effects like `db`, `audit`, `gpu` beyond the built-in four. | `agent_custom_effects.py` |

## Quick start

### Prerequisites

- [Lean 4 / elan](https://leanprover.github.io/lean4/doc/setup.html) (the project uses `leanprover/lean4:v4.29.0`)
- Python 3.10+ (for the examples driver)
- The `monty` binary (Rust frontend, in the sibling `../monty/` directory)

### Build

```bash
cd MontyVerification
lake build
```

This compiles the Lean project including the codegen binary
(`montyverification`) used by the examples driver.

### Run the examples

```bash
python3 examples/run_examples.py -j 8
```

This finds every `examples/<name>.py` that has a matching
`examples/<name>.lean`, and for each one:

1. Runs `monty --emit-ir <file>.py` to produce the prepared IR (JSON).
2. Runs `montyverification --codegen <ir>.json <out>.lean` to translate
   the IR into typed Lean source.
3. Concatenates the generated Lean with the hand-written `.lean`
   properties file (which contains the theorems to check).
4. Runs `lean` on the result. If every `example`/`theorem` in the
   properties file compiles, the example is verified.

You can run a single example by name:

```bash
python3 examples/run_examples.py agent_payment_workflow
```

Or with `--verbose` to see the generated Lean:

```bash
python3 examples/run_examples.py agent_payment_workflow --verbose
```

## How to verify your own Python file

### Step 1: Write the Python

```python
# myagent.py
# external: search_web net
# external: send_email net

def research(topic):
    raw = search_web(topic)
    send_email("user@example.com", raw)
    return raw
```

The `# external:` comments at the top tell the codegen what effect
each tool call has. Without them, unknown functions are treated as
`Perms.top` (may do anything).

### Step 2: Generate the Lean

```bash
# Parse Python to IR
../monty/target/debug/monty --emit-ir myagent.py > /tmp/myagent.json

# Translate IR to Lean (pass --source so it reads the # external: directives)
.lake/build/bin/montyverification --codegen /tmp/myagent.json /tmp/myagent.lean \
    --source myagent.py
```

### Step 3: Write properties (optional)

Create a file with theorems about the generated code:

```lean
-- myagent_props.lean

-- Effect type is inferred as { net := true }
example :
    (research : PyVal → Eff (EffAST.permsOf __extEnv __env research__ast) PyVal)
      = research := rfl

-- search_web is called before send_email on every path
example :
    EffAST.calledBefore "ext_search_web" "ext_send_email"
        research__ast = true := by
  native_decide
```

### Step 4: Verify

```bash
# Concatenate generated code + properties and run Lean
cat /tmp/myagent.lean myagent_props.lean > /tmp/combined.lean
LEAN_PATH=$(lake env bash -c 'echo $LEAN_PATH') lean /tmp/combined.lean
```

If it compiles with no errors, the properties are verified.

## Understanding the examples

Each example is a pair: `examples/<name>.py` (the Python source) and
`examples/<name>.lean` (the properties to verify). The Python file is
ordinary Python — the verification happens entirely on the Lean side.

### Highlighted examples

**Effect inference without annotations** (`agent_no_annotations.py`):
Three functions with no `Pure[]`/`Effect[]` annotations. The codegen
infers `trim` is pure and `research_and_notify` has `{ net := true }`
from the call graph. The `.lean` file proves the inferred types match
via `rfl`.

**Ordering invariants** (`agent_payment_workflow.py`):
A payment pipeline where compliance requires approval before payment
before logging. The `.lean` file proves all three ordering invariants
by `native_decide` over the emitted `EffAST`. A companion file
(`agent_payment_buggy.py`) has a cached fast path that skips approval
— the same theorem is provably *false*.

**Interprocedural analysis** (`agent_async_pipeline.py`):
A document pipeline split across four helper functions. The `.lean`
file uses `calledBeforeInter` to verify ordering on the underlying
external calls across function boundaries — `fetch_document` before
`extract_entities` before `store_results` even though they live in
different functions.

**Interprocedural bug detection** (`agent_interprocedural_bug.py`):
A trading system where `fast_execute` skips input validation. The
interprocedural analysis catches the bug: `validate_input` is NOT
guaranteed before `execute_trade` because one branch skips it. But
authentication and auditing are proven sound on both branches.

**Async gather** (`agent_async_orchestrator.py`):
Pure async coroutines composed via `asyncio.gather`. The entire
module body — `gather(double(3), add_ten(5), greet("world"))` —
reduces to `[6, 15, "hello world"]` in Lean's kernel via
`native_decide`.

**Rich property language** (`agent_property_zoo.py`):
Demonstrates `calledBefore`, `eventuallyCalls`, `calledExactlyOnce`,
`calledAfter`, and `mutuallyExclusive` on a single ETL function.

**Custom externals** (`agent_custom_externals.py`):
Four user-declared tool APIs (`fetch_invoice`, `charge_card`,
`write_audit_log`, `read_secret`) with specific effect sets. No
modification to the codegen source needed.

### Example categories

| Prefix | What it demonstrates |
|---|---|
| `agent_*` | Realistic agent patterns with rich property files |
| `stress_*` | Edge-case Python shapes that stress the codegen |
| `async_*` | Async/await and asyncio.gather patterns |
| Others | Specific language features (closures, list comprehensions, slicing) |

## What's verified

The 49 worked examples in `examples/` exercise every property listed
in the table above end-to-end: Python source → IR → typed Lean →
theorems discharged. Run `python3 examples/run_examples.py` to verify
them — every example must compile clean.

## Further reading

- [`docs/walkthrough.md`](docs/walkthrough.md) — end-to-end tour on one example
- [`docs/soundness.md`](docs/soundness.md) — what the verification promises and doesn't
- [`docs/README.md`](docs/README.md) — full documentation index
