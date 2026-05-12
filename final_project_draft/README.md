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
- [x] `compiler_correct_general` — scaffolded with `induction heval`. **All 22 / 22 cases proven**: `intr`, `nilr`, `boolr`, `varr`, `succr`, `predr`, `negtr`, `negfr`, `plusr`, `timesr`, `fstr`, `sndr`, `bindr`, `pairr`, `iftr`, `iffr`, `consr`, `isnilt`, `isnilf`, `callr`. No `sorry`s remain. Added helpers: `Represents.int_inv`, `Represents.pair_inv`, `Represents.nil_inv`.
- ✅ `callr` unblocked (yunze): ~250-line proof chains 11 explicit states. (1) `compile_defns_split hlook` extracts `entry_nat := pre_defs.length + 1` with `Defns.entry ds f' = some entry_nat`. (2) `defns_in_place` + `code_at_*` lemmas locate the body code and the trailing `[pop r9, pop r9, jmpabs r9]` at `entry_nat + compile_len e_body`. (3) The match inside `compile (.call ...)` is concretized by rewriting with `hentry_eq`. (4) IH1 → s1 (arg evaluated, rax = i1). (5) movpc → s2 (r9 := s1.pc + 1). (6) addi 5 → s3 (r9 := retaddr). (7) push r9 → s4. (8) push rax → s5 (uses `hrax_s4` chain through writes). (9) movi → s6. (10) jmpabs → s7 (pc := entry_nat; needs `(Int.ofNat n).toNat = n` via `rfl`). (11) `hstart_eq` bridges into ih2 by `rfl`, giving s8. (12) pop r9 → s9 (discard arg). (13) pop r9 → s10 (r9 := retaddr). (14) jmpabs → s11 (pc := s1.pc + 6 = pc + compile_len e_arg + 6 = pc + compile_len (.call f e_arg)). Heap untouched after IH2, so `hext1 ∘ hext8` and `hfresh8` carry through.
- ✅ `isnilf` unblocked via Option A (yunze): strengthened `FreshFrom` to a structure carrying both `a ≥ 1` (`pos`) and the original lookup-none property (`lookup`), and added an `i ≥ 1` premise to the `Represents.pair` constructor. The invariant rides on `FreshFrom` through `compiler_correct_general` and is established in `compile_prog_correct` by initializing `rbx := 1` (was `0`). `pair_inv` now also exposes `i ≥ 1` as a final conjunct so `isnilf` can read off `rax ≥ 1` and conclude `(rax == 0) = false`.
- ⚠️ `is_nil` codegen was buggy and is now patched (yunze): old version (`.bnz 1` with both `movi`s) was a no-op + had the bool answers swapped. Now `[movi r9 0, cmp rax r9, movi rax 0, bnz 2, movi rax 1]` — bnz skips the trailing `movi rax 1` when rax was non-zero (pair), otherwise falls through to set rax = 1 (nil case).
- [x] `compile_prog_correct` — proved as a corollary of `compiler_correct_general` (uses the leading `.jmp`, then chains via `Steps.append`).

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
- [x] ✅ `is_nil` codegen patched (yunze): now `[movi r9 0, cmp rax r9, movi rax 0, bnz 2, movi rax 1]`. Both `isnilt` and `isnilf` proven against it.
- [x] `compile_length` covers the new cases (one `simp` line per constructor in `compile_length`).

### Part 5: Representation and Invariants

- [x] Extended `Represents` with the `nil` case (`Represents .nil 0 h`).
- [x] Add / re-use heap lemmas for the cons layout (currently piggybacks on pair, not yet verified through a proof).
- [x] Update / extend freshness lemmas if needed for cons allocation.
- [ ] Update `Related`-style invariants if needed.

### Part 6: Correctness Proofs for Lists

- [x] Prove helper lemmas for `consr`, `isnilt`, `isnilf` (`Represents.cons`, `Represents.nil_inv`, plus the `i ≥ 1` premise on `pair_inv`).
- [x] Discharge the `consr`, `isnilt`, `isnilf` `sorry`s in `compiler_correct_general`.
- [x] Re-checked `compile_prog_correct`: the public signature now initializes `rbx := 1` (was `0`) to satisfy the strengthened `FreshFrom`. Compiles end-to-end as a corollary of `compiler_correct_general`.

### Part 7: Report

- [ ] Write a short explanation of the machine/value representation.
- [ ] Explain the list design choice (pair-encoded, no dedicated cons value).
- [ ] Explain the main proof idea.
- [ ] Note what is fully complete and what is partial / future work.

