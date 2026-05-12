# Final Project Draft: Lists + Compiler Correctness

This folder is a standalone draft for a final project extension based on `RegMachine.lean`.
It does not modify your current code.

## Scope

1. Add list values and list expressions to the source language.
2. Define big-step correctness statements for list operations.
3. Extend compilation templates for lists.
4. State a simulation theorem from source semantics to machine semantics.
5. Add an x86-level correctness statement for the backend.


## Deliverables

- Extended language definitions.
- Compiler extension for lists.
- Correctness theorems with proofs (or partial proofs with clear TODO markers).
- Short report describing invariants and proof strategy.

## Progress Checklist

Use this as a lightweight team tracker.

### Part 1: Current Compiler Correctness

- [x] Basic machine, source language, and compiler are written.
- [x] Many helper lemmas are proved.
- [x] `compiler_expr_correct_succ` is proved.
- [x] `compiler_expr_correct_pred` is proved.
- [~] `compiler_correct_general` — scaffolded with `induction heval`; proven cases: `intr`, `nilr`, `boolr`, `varr`. Remaining (all `sorry`): `succr`, `predr`, `plusr`, `timesr`, `iftr`, `iffr`, `negtr`, `negfr`, `bindr`, `callr`, `pairr`, `fstr`, `sndr`, `consr`, `isnilt`, `isnilf`.
- [ ] `compile_prog_correct` — stubbed `sorry`; intended as a corollary of `compiler_correct_general`.

### Part 2: List Feature Design

- [x] Decided representation in `Val`: added `Val.nil`; `cons` evaluates to a `.pair v1 v2` rather than a dedicated cons value.
- [x] Decided supported list expressions: `nil`, `cons`, `is_nil`.
- [x] Decided lists are encoded through the existing pair / heap layout (no separate list cells).

### Part 3: Syntax and Semantics

- [x] Added `Expr.nil`, `Expr.cons`, `Expr.is_nil`.
- [x] Added `Val.nil`.
- [x] Added `Eval` rules: `nilr`, `consr`, `isnilt`, `isnilf`.
- [ ] Add small examples / sanity checks (none in the file yet).

### Part 4: Compiler Extension

- [x] Extended `compile_len` for `nil`, `cons`, `is_nil`.
- [x] Extended `compile` for `nil`, `cons`, `is_nil`.
- [ ] ⚠️ `is_nil` codegen looks broken: `[.movi .r9 0, .cmp .rax .r9, .movi .rax 0]` does the compare but then unconditionally writes `0` to `rax`, so the result is always `bool false`. Needs a conditional move based on `zf` (or an equivalent pattern) before `isnilt` can be proven.
- [ ] Confirm `compile_length` still holds for the new cases.

### Part 5: Representation and Invariants

- [x] Extended `Represents` with the `nil` case (`Represents .nil 0 h`).
- [ ] Add / re-use heap lemmas for the cons layout (currently piggybacks on pair, not yet verified through a proof).
- [ ] Update / extend freshness lemmas if needed for cons allocation.
- [ ] Update `Related`-style invariants if needed.

### Part 6: Correctness Proofs for Lists

- [ ] Prove helper lemmas for `consr`, `isnilt`, `isnilf`.
- [ ] Discharge the `consr`, `isnilt`, `isnilf` `sorry`s in `compiler_correct_general`.
- [ ] Re-check whole-program correctness statement (`compile_prog_correct`).

### Part 7: Report

- [ ] Write a short explanation of the machine/value representation.
- [ ] Explain the list design choice (pair-encoded, no dedicated cons value).
- [ ] Explain the main proof idea.
- [ ] Note what is fully complete and what is partial / future work.

