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
- [ ] `compiler_correct_general`
- [ ] `compile_prog_correct`

### Part 2: List Feature Design

- [ ] Decide how lists should be represented in `Val`.
- [ ] Decide what list expressions to support.
- [ ] Decide whether lists are direct values or encoded through existing pairs / heap layout.

### Part 3: Syntax and Semantics

- [ ] Add list constructors to `Expr`.
- [ ] Add list constructor(s) to `Val` if needed.
- [ ] Add `Eval` rules for the new list forms.
- [ ] Add small examples / sanity checks.

### Part 4: Compiler Extension

- [ ] Extend `compile_len`.
- [ ] Extend `compile`.
- [ ] Add any list-specific machine code templates.
- [ ] Check compiled code lengths still match proofs.

### Part 5: Representation and Invariants

- [ ] Extend `Represents` for lists.
- [ ] Add heap lemmas for the chosen list layout.
- [ ] Update / extend freshness lemmas if needed.
- [ ] Update `Related`-style invariants if needed.

### Part 6: Correctness Proofs for Lists

- [ ] Prove helper lemmas for each new list case.
- [ ] Extend `compiler_correct_general` to list forms.
- [ ] Re-check whole-program correctness statement.

### Part 7: Report

- [ ] Write a short explanation of the machine/value representation.
- [ ] Explain the list design choice.
- [ ] Explain the main proof idea.
- [ ] Note what is fully complete and what is partial / future work.

## Suggested Work Split

- Collaborator A:
  focus on the remaining current correctness proofs.
- Collaborator B:
  focus on list design, syntax, semantics, and compiler cases.
- Then both:
  connect the list extension back into the main correctness theorem and write the report.
