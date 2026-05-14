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
- ✅ `isnilf`(yunze): strengthened `FreshFrom` to a structure carrying both `a ≥ 1` (`pos`) and the original lookup-none property (`lookup`), and added an `i ≥ 1` premise to the `Represents.pair` constructor. The invariant rides on `FreshFrom` through `compiler_correct_general` and is established in `compile_prog_correct` by initializing `rbx := 1` (was `0`). `pair_inv` now also exposes `i ≥ 1` as a final conjunct so `isnilf` can read off `rax ≥ 1` and conclude `(rax == 0) = false`.
- [x] `compile_prog_correct` — proved as a corollary of `compiler_correct_general` (uses the leading `.jmp`, then chains via `Steps.append`).

### Part 2: List Feature Design

- [x] Decided representation in `Val`: added `Val.nil`; `cons` evaluates to a `.pair v1 v2` rather than a dedicated cons value.
- [x] Decided supported list expressions: `nil`, `cons`, `is_nil`.
- [x] Decided lists are encoded through the existing pair / heap layout (no separate list cells).

### Part 3: Syntax and Semantics

- [x] Added `Expr.nil`, `Expr.cons`, `Expr.is_nil`.
- [x] Added `Val.nil`.
- [x] Added `Eval` rules: `nilr`, `consr`, `isnilt`, `isnilf`.
- [x] Added `Expr.head`, `Expr.tail` with `Eval.headr` / `Eval.tailr` (Rachel). Both rules pattern-match on `.pair v1 v2`, so `head .nil` / `tail .nil` have no derivation (partial by design — matches typical strict-list semantics).
- [x] Add small examples / sanity checks (yunze): six `example` declarations right after the `Eval` definition exercise `nilr`, `consr`, `isnilt`, `isnilf` end-to-end at the source level — `nil ⇒ .nil`, `cons 1 nil ⇒ pair (int 1) nil`, `is_nil nil ⇒ true`, `is_nil (cons 1 nil) ⇒ false`, plus a nested two-element list and `is_nil` on it. Each is a one-liner using the constructors directly; they confirm the new rules compose without affecting any proofs.

### Part 4: Compiler Extension

- [x] Extended `compile_len` for `nil`, `cons`, `is_nil`.
- [x] Extended `compile` for `nil`, `cons`, `is_nil`.
- [x] Extended `compile_len` and `compile` for `head`, `tail` (Rachel). Both are one instruction past the subexpression — load `rax` from the heap cell pointed to by the pair address.
- [x] ✅ `is_nil` codegen patched (yunze): now `[movi r9 0, cmp rax r9, movi rax 0, bnz 2, movi rax 1]`. Both `isnilt` and `isnilf` proven against it.
- [x] `compile_length` covers the new cases (one `simp` line per constructor in `compile_length`).

### Part 5: Representation and Invariants

- [x] Extended `Represents` with the `nil` case (`Represents .nil 0 h`).
- [x] Add / re-use heap lemmas for the cons layout (currently piggybacks on pair, not yet verified through a proof).
- [x] Update / extend freshness lemmas if needed for cons allocation.
- [x] Update `Related`-style invariants if needed — **not needed**. `Related` is structural over `Stack`/`CEnv`/`Env` and delegates value-shape constraints to `Represents`, which already covers `.nil` and `.pair` (the cons encoding). All 22 cases of `compiler_correct_general` plus `compiler_expr_correct_head`/`_tail` closed without any change to `Related`.
- [x] Added `IsList : Val → Prop` predicate (Rachel): `IsList .nil` and `IsList (.pair _ v2) := IsList v2`, with helpers `IsList.nil`, `IsList.cons`, and `eval_cons_isList` proving that `Eval`-of-`cons` on a list tail yields a list value.

### Part 6: Correctness Proofs for Lists

- [x] Prove helper lemmas for `consr`, `isnilt`, `isnilf` (`Represents.cons`, `Represents.nil_inv`, plus the `i ≥ 1` premise on `pair_inv`).
- [x] Discharge the `consr`, `isnilt`, `isnilf` `sorry`s in `compiler_correct_general`.
- [x] Re-checked `compile_prog_correct`: the public signature now initializes `rbx := 1` (was `0`) to satisfy the strengthened `FreshFrom`. Compiles end-to-end as a corollary of `compiler_correct_general`.
- [x] `compiler_expr_correct_head` and `compiler_expr_correct_tail` (Rachel) — standalone correctness lemmas for the new ops, proven against the one-instruction load codegen.

### Part 6.5: Auxiliary metatheory (Rachel)

- [x] **`eval_deterministic`** : `Eval ds r e v1 → Eval ds r e v2 → v1 = v2`. Big case analysis with one branch per `Eval` constructor; uses `rename_i` to recover bound names and chains IHs to identify the values.
- [x] **Type system**: `inductive Ty`, `TyEnv := List (Var × Ty)`, `TyEnv.lookup`, `Typed : TyEnv → Expr → Ty → Prop` (well-typed expressions), `TypedVal : Val → Ty → Prop`, `TyRelated : TyEnv → Env → Prop` (env-level typing).
- [x] **Bridging lemmas**: `TypedVal.exists` (every value has some type — needed because pair forces deep inspection), `TypedVal.ofTy` (every type is inhabited), `TyRelated.TyEnv_exists`, `TyRelatedEnv_exists`, `TyRelated.lookup`.
- [x] **Type soundness** — `well_typed_implies_well_defined : Typed Γ e t → TyRelated Γ r → ∃ v, Eval ds r e v ∧ TypedVal v t`. Proves that well-typed expressions don't get stuck.

### Part 7: Report

- [ ] Write a short explanation of the machine/value representation.
- [ ] Explain the list design choice (pair-encoded, no dedicated cons value).
- [ ] Explain the main proof idea.
- [ ] Note what is fully complete and what is partial / future work.

