-- ═══════════════════════════════════════════════════════════════════════════
--  Final Project — Compiler Correctness for a Little Source Language
-- ═══════════════════════════════════════════════════════════════════════════
--
--  TABLE OF CONTENTS
--
--    1. Target machine                   line   42
--       (Regs / Heap / State / Instr / Step inductive)
--
--    2. Source language                   line  251
--       (Expr / Val / Env / Defns / Eval big-step)
--
--    3. Compiler                          line  371
--       (CEnv / compile_len / compile / compile_defns / compile_prog)
--
--    4. Representation relations          line  543
--       (Represents value↔heap, Related stack↔env, Steps closure)
--
--    5. Helper lemmas                     line  623
--       (list ops, Heap, FreshFrom, HeapExtends, inversion helpers,
--        compile_length, compile_defns_length)
--
--    6. `code_at` & program layout        line  920
--       (code_at_*, defns_in_place, compile_prog_*_code_at)
--
--    7. Per-instruction correctness       line 1086
--       (ExprPost, compiler_expr_correct_succ / _pred)
--
--    8. Main simulation theorem           line 1227
--       (`compiler_correct_general` — induction on Eval; one case per Expr)
--
--    9. Whole-program correctness         line 2155
--       (FinalState, compile_prog_correct)
--
--   10. Collaboration template / notes    line 2265
--
--  Line ranges are approximate — see the SECTION banners below for exact spots.
-- ═══════════════════════════════════════════════════════════════════════════


-- ═══════════════════════════════════════════════════════════════════════════
-- SECTION 1 — Target machine
-- ═══════════════════════════════════════════════════════════════════════════
-- A little register + stack + heap machine semantics.

structure Regs where
  rax : Int
  rbx : Int
  r9 : Int

inductive Reg where
  | rax | rbx | r9

def Reg.read : Reg -> Regs -> Int
  | .rax, rs => rs.rax
  | .rbx, rs => rs.rbx
  | .r9,  rs => rs.r9

def Reg.write : Reg -> Int -> Regs -> Regs
  | .rax, v, rs => { rs with rax := v }
  | .rbx, v, rs => { rs with rbx := v }
  | .r9,  v, rs => { rs with r9 := v }

def regs0 : Regs := { rax := 0, rbx := 0, r9 := 0}

abbrev Stack := List Int
abbrev Heap := List (Int × Int)

def Heap.lookup (h : Heap) (i : Int) : Option Int :=
  match h with
  | [] => none
  | (j,k) :: h =>
    if i = j then some k else Heap.lookup h i

def Heap.ext (h : Heap) (i j : Int) : Heap :=
  (i, j) :: h

structure State where
  pc : Nat
  regs : Regs
  stack : Stack
  zf : Bool
  heap : Heap

inductive Instr where
| movr (dst src : Reg) : Instr
| movi (dst : Reg) (imm : Int) : Instr
| movpc (dst : Reg) : Instr
| push (src : Reg) : Instr
| pop (dst : Reg) : Instr
| addr (dst src : Reg) : Instr
| addi (dst : Reg) (imm : Int) : Instr
| xor (dst src : Reg) : Instr
| bnz (i : Int) : Instr
| jmp (i : Int) : Instr
| jmpabs (r : Reg) : Instr
| cmp (r1 r2 : Reg) : Instr
| imul (r : Reg) : Instr
| load (dst addr : Reg) (offset : Nat) : Instr
| store (addr src : Reg) (offset : Nat) : Instr
| stackget (dst : Reg) (i : Nat) : Instr
| halt : Instr

inductive get {a} : List a -> Nat -> a -> Prop where
  | hd {x xs} : get (x :: xs) 0 x
  | tl {xs i x y} : get xs i x -> get (y :: xs) (i + 1) x

def instr_at (is : List Instr) (i : Nat) (ins : Instr) : Prop :=
  get is i ins

def headD {α} (default : α) : List α -> α
  | [] => default
  | x :: _ => x

def tailD {α} : List α -> List α
  | [] => []
  | _ :: xs => xs

-- semi-infinite two's complement XOR
def Int.xor (i1 i2 : Int) : Int :=
  let bits (i : Int) : Nat :=
    if i < 0 then
      (Int.natAbs i) - 1
    else
      Int.natAbs i
  let b1 := bits i1
  let b2 := bits i2
  let b := Nat.xor b1 b2
  if Bool.xor (i1 < 0) (i2 < 0) then
    - (Int.ofNat (b + 1))
  else
    Int.ofNat b

#eval decide (Int.xor 5 0 = 5)
#eval decide (Int.xor (-5) 0 = -5)
#eval decide (Int.xor 0 (-5) = -5)
#eval decide (Int.xor (-5) (-3) = 6)
#eval decide (Int.xor 1 (-5) = -6)

inductive Step (is : List Instr) : State -> State -> Prop where
| movr {r1 r2 s} :
  instr_at is s.pc (.movr r1 r2) ->
  Step is s
  { s with
    pc   := s.pc + 1
    regs := Reg.write r1 (Reg.read r2 s.regs) s.regs }
| movi {r i s} :
  instr_at is s.pc (.movi r i) ->
  Step is s
  { s with
    pc   := s.pc + 1
    regs := Reg.write r i s.regs }
| movpc {dst s} :
  instr_at is s.pc (.movpc dst) ->
  Step is s
  { s with
    pc   := s.pc + 1
    regs := Reg.write dst (Int.ofNat (s.pc + 1)) s.regs }
| push {r s} :
  instr_at is s.pc (.push r) ->
  Step is s
  { s with
    pc    := s.pc + 1
    stack := (Reg.read r s.regs) :: s.stack }
| pop {r s hd tl} :
  instr_at is s.pc (.pop r) ->
  s.stack = hd :: tl ->
  Step is s
  { s with
    pc    := s.pc + 1
    regs  := Reg.write r hd s.regs
    stack := tl }
| addr {r1 r2 s} :
  instr_at is s.pc (.addr r1 r2) ->
  Step is s
  { s with
    pc   := s.pc + 1
    regs := Reg.write r1 (Reg.read r1 s.regs + Reg.read r2 s.regs) s.regs }
| addi {r i s} :
  instr_at is s.pc (.addi r i) ->
  Step is s
  { s with
    pc   := s.pc + 1
    regs := Reg.write r (Reg.read r s.regs + i) s.regs }
| xor {r1 r2 s} :
  instr_at is s.pc (.xor r1 r2) ->
  Step is s
  { s with
    pc := s.pc + 1
    regs := Reg.write r1 (Int.xor (Reg.read r1 s.regs) (Reg.read r2 s.regs)) s.regs }
| cmp {r1 r2 s} :
  instr_at is s.pc (.cmp r1 r2) ->
  Step is s
  { s with
    pc := s.pc + 1
    zf := Reg.read r1 s.regs == Reg.read r2 s.regs }
| jmp {i s} :
  instr_at is s.pc (.jmp i) ->
  Step is s
  { s with
    pc := (Int.ofNat s.pc + i).toNat }
| jmpabs {src s} :
  instr_at is s.pc (.jmpabs src) ->
  Step is s
  { s with
    pc := (Reg.read src s.regs).toNat }
| bnzt {i s} :
  instr_at is s.pc (.bnz i) ->
  s.zf = false ->
  Step is s
  { s with
    pc := (Int.ofNat s.pc + i).toNat }
| bnzf {i s} :
  instr_at is s.pc (.bnz i) ->
  s.zf = true ->
  Step is s
  { s with
    pc := s.pc + 1 }
| imul {r s} :
  instr_at is s.pc (.imul r) ->
  Step is s
  { s with
    pc := s.pc + 1
    regs := { s.regs with rax := s.regs.rax * (Reg.read r s.regs) }}
| load {dst addr offset s a v} :
  instr_at is s.pc (.load dst addr offset) ->
  a = Reg.read addr s.regs ->
  Heap.lookup s.heap (a + offset) = some v ->
  Step is s
  { s with
    pc   := s.pc + 1
    regs := Reg.write dst v s.regs }
| store {addr offset src s a v} :
  instr_at is s.pc (.store addr src offset) ->
  a = Reg.read addr s.regs ->
  v = Reg.read src s.regs ->
  Step is s
  { s with
    pc   := s.pc + 1
    heap := Heap.ext s.heap (a + offset) v }
| stackget {dst i s v} :
  instr_at is s.pc (.stackget dst i) ->
  get s.stack i v ->
  Step is s
  { s with
    pc   := s.pc + 1
    regs := Reg.write dst v s.regs }


-- ═══════════════════════════════════════════════════════════════════════════
-- SECTION 2 — Source language
-- ═══════════════════════════════════════════════════════════════════════════
-- Syntax (`Expr`), values (`Val`), environments, top-level definitions,
-- and the big-step evaluation relation `Eval`.

abbrev Var := String

inductive Expr where
  | int (i : Int) : Expr
  | succ (e : Expr) : Expr
  | pred (e : Expr) : Expr
  | plus (e1 : Expr) (e2 : Expr) : Expr
  | times (e1 : Expr) (e3 : Expr) : Expr
  | ifte (e1 e2 e3 : Expr) : Expr
  | bool (b : Bool) : Expr
  | neg (e : Expr) : Expr
  | bind (x : Var) (e1 e2 : Expr) : Expr
  | var (x : Var) : Expr
  | call (f : Var) (e : Expr) : Expr
  | pair (e1 e2 : Expr) : Expr
  | fst (e : Expr) : Expr
  | snd (e : Expr) : Expr
  | nil : Expr
  | cons (e1 e2 : Expr) : Expr
  | is_nil (e : Expr) : Expr

inductive Defn where
  | defn (f x : Var) (e : Expr)

inductive Val where
  | int (i : Int) : Val
  | bool (b : Bool) : Val
  | pair (v1 v2 : Val) : Val
  | nil : Val

abbrev Env := List (Var × Val)

abbrev Defns := List Defn

def Env.lookup (r : Env) (x : Var) : Option Val :=
  match r with
  | [] => none
  | (y,v) :: r =>
    if x = y then some v else Env.lookup r x

def Defns.lookup (ds : Defns) (f : Var) : Option Defn :=
  match ds with
  | [] => none
  | ((.defn g y e) :: ds) =>
    if f = g then some (.defn g y e) else Defns.lookup ds f

inductive Eval : Defns -> Env -> Expr -> Val -> Prop where
  | intr {ds r} (i : Int) :
    Eval ds r (.int i) (.int i)
  | boolr {ds r} (b : Bool) :
    Eval ds r (.bool b) (.bool b)
  | succr {ds r e i} :
    Eval ds r e (.int i) ->
    Eval ds r (.succ e) (.int (i + 1))
  | predr {ds r e i} :
    Eval ds r e (.int i) ->
    Eval ds r (.pred e) (.int (i - 1))
  | plusr {ds r e1 i1 e2 i2} :
    Eval ds r e1 (.int i1) ->
    Eval ds r e2 (.int i2) ->
    Eval ds r (.plus e1 e2) (.int (i1 + i2))
  | timesr {ds r e1 i1 e2 i2} :
    Eval ds r e1 (.int i1) ->
    Eval ds r e2 (.int i2) ->
    Eval ds r (.times e1 e2) (.int (i1 * i2))
  | iftr {ds r e1 e2 v e3} :
    Eval ds r e1 (.bool true) ->
    Eval ds r e2 v ->
    Eval ds r (.ifte e1 e2 e3) v
  | iffr {ds r e1 e3 v e2} :
    Eval ds r e1 (.bool false) ->
    Eval ds r e3 v ->
    Eval ds r (.ifte e1 e2 e3) v
  | negtr {ds r e} :
    Eval ds r e (.bool true) ->
    Eval ds r (.neg e) (.bool false)
  | negfr {ds r e} :
    Eval ds r e (.bool false) ->
    Eval ds r (.neg e) (.bool true)
  | varr {ds r v x} :
    Env.lookup r x = some v ->
    Eval ds r (.var x) v
  | bindr {ds r e1 v1 x v e2} :
    Eval ds r e1 v1 ->
    Eval ds ((x, v1) :: r) e2 v ->
    Eval ds r (.bind x e1 e2) v
  | callr {ds r e v1 f x e' v} :
    Eval ds r e v1 ->
    Defns.lookup ds f = some (.defn f x e') ->
    Eval ds [(x,v1)] e' v ->
    Eval ds r (.call f e) v
  | pairr {ds r e1 v1 e2 v2} :
    Eval ds r e1 v1 ->
    Eval ds r e2 v2 ->
    Eval ds r (.pair e1 e2) (.pair v1 v2)
  | fstr {ds r e v1 v2} :
    Eval ds r e (.pair v1 v2) ->
    Eval ds r (.fst e) v1
  | sndr {ds r e v1 v2} :
    Eval ds r e (.pair v1 v2) ->
    Eval ds r (.snd e) v2
  | nilr {ds r} :
    Eval ds r (.nil) (.nil)
  | consr {ds r e1 v1 e2 v2} :
    Eval ds r e1 v1 ->
    Eval ds r e2 v2 ->
    Eval ds r (.cons e1 e2) (.pair v1 v2)
  | isnilt {ds r e} :
    Eval ds r e .nil ->
    Eval ds r (.is_nil e) (.bool true)
  | isnilf {ds r e v1 v2} :
    Eval ds r e (.pair v1 v2) ->
    Eval ds r (.is_nil e) (.bool false)

-- ───────────────────────────────────────────────────────────────────────────
-- Sanity-check examples for the list extension (yunze).
-- These are small `example`s that exercise the new `Eval` rules
-- `nilr`, `consr`, `isnilt`, `isnilf` end-to-end at the source level.
-- They do not affect any proofs; they just confirm the rules compose.
-- ───────────────────────────────────────────────────────────────────────────

-- `nil` evaluates to `Val.nil` under any defns / env.
example : Eval [] [] .nil .nil :=
  Eval.nilr

-- `cons 1 nil` evaluates to the pair-encoded list `pair (int 1) nil`.
example : Eval [] [] (.cons (.int 1) .nil) (.pair (.int 1) .nil) :=
  Eval.consr (Eval.intr 1) Eval.nilr

-- `is_nil nil` evaluates to `true`.
example : Eval [] [] (.is_nil .nil) (.bool true) :=
  Eval.isnilt Eval.nilr

-- `is_nil (cons 1 nil)` evaluates to `false` (the argument is a non-nil pair).
example : Eval [] [] (.is_nil (.cons (.int 1) .nil)) (.bool false) :=
  Eval.isnilf (Eval.consr (Eval.intr 1) Eval.nilr)

-- A two-element list `cons 1 (cons 2 nil)` evaluates to nested pairs,
-- confirming the right-associative pair encoding works through `consr`.
example :
    Eval [] [] (.cons (.int 1) (.cons (.int 2) .nil))
               (.pair (.int 1) (.pair (.int 2) .nil)) :=
  Eval.consr (Eval.intr 1) (Eval.consr (Eval.intr 2) Eval.nilr)

-- `is_nil` on a two-element list is still `false` — only the *outermost*
-- shape matters.
example :
    Eval [] [] (.is_nil (.cons (.int 1) (.cons (.int 2) .nil))) (.bool false) :=
  Eval.isnilf (Eval.consr (Eval.intr 1) (Eval.consr (Eval.intr 2) Eval.nilr))

-- ═══════════════════════════════════════════════════════════════════════════
-- SECTION 3 — Compiler
-- ═══════════════════════════════════════════════════════════════════════════
-- The compiler from `Expr` to `List Instr`, plus the wrapping
-- `compile_defn`, `compile_defns`, and `compile_prog`. `CEnv` tracks the
-- compile-time stack shape (where each source variable lives).

abbrev CEnv := List (Option Var)

def CEnv.lookup (c : CEnv) (x : Var) : Option Nat :=
  match c with
  | [] => none
  | some y :: c =>
    if x = y then some 0 else
      (CEnv.lookup c x).map .succ
  | none :: c =>
      (CEnv.lookup c x).map .succ

-- computes length (compile ds e c) for any (good) ds, c
-- be careful to update if you change the compiler
def compile_len (e : Expr) : Nat :=
  match e with
  | .int _
  | .bool _
  | .var _ => 1
  | .succ e
  | .pred e
  | .fst e
  | .snd e => compile_len e + 1
  | .plus e1 e2 =>
    compile_len e1 + compile_len e2 + 3
  | .ifte e1 e2 e3 =>
    compile_len e1 + compile_len e2 + compile_len e3 + 4
  | .neg e =>
    compile_len e + 2
  | .times e1 e2 =>
    compile_len e1 + compile_len e2 + 4
  | .bind _ e1 e2 =>
    compile_len e1 + compile_len e2 + 2
  | .pair e1 e2 =>
    compile_len e1 + compile_len e2 + 6
  | .call _ e =>
    compile_len e + 6
  | .nil => 1
  | .cons e1 e2 => compile_len e1 + compile_len e2 + 6
  | .is_nil e => compile_len e + 5

def compile_defn_len (d : Defn) : Nat :=
  match d with
  | .defn _ _ e =>
    compile_len e + 3

def compile_defns_len (ds : Defns) : Nat :=
  match ds with
  | [] => 0
  | d :: ds =>
    compile_defn_len d + compile_defns_len ds

def Defns.entry (ds : Defns) (f : Var) : Option Nat :=
  match ds with
  | [] => none
  | (.defn g x e) :: ds =>
    if f = g then
      some 1 -- start at 1 to skip first jump instruction
    else
      match Defns.entry ds f with
      | none => none
      | some i =>
        some (compile_defn_len (.defn g x e) + i)

def compile (ds : Defns) (c : CEnv) (e : Expr) : List Instr :=
  match e with
  | .int i  => [.movi Reg.rax i]
  | .bool b => [.movi Reg.rax (if b then 1 else 0)]
  | .succ e =>
    compile ds c e ++
    [.addi Reg.rax 1]
  | .pred e =>
    compile ds c e ++
    [.addi Reg.rax (-1)]
  | .plus e1 e2 =>
    compile ds c e1 ++
    [.push Reg.rax] ++
    compile ds (none :: c) e2 ++
    [.pop .r9, .addr .rax .r9]
  | .ifte e1 e2 e3 =>
    let is2 := compile ds c e2
    let is3 := compile ds c e3
    compile ds c e1 ++
    [.movi .r9 0, -- 0 = false
    .cmp .rax .r9,
    .bnz (List.length is3 + 2)] ++
    is3 ++
    [.jmp (List.length is2 + 1)] ++
    is2
  | .neg e =>
    compile ds c e ++
    [.movi .r9 1, .xor .rax .r9]
  | .times e1 e2 =>
    compile ds c e1 ++
    [.push Reg.rax] ++
    compile ds (none :: c) e2 ++
    [.movr .r9 .rax, .pop .rax, .imul .r9]
  | .var x =>
    match CEnv.lookup c x with
    | some n => [.stackget .rax n]
    | none => [.halt]
  | .bind x e1 e2 =>
    compile ds c e1 ++
    [.push .rax] ++
    compile ds (some x :: c) e2 ++
    [.pop .r9]
  | .pair e1 e2 =>
    compile ds c e1 ++
    [.push .rax] ++
    compile ds (none :: c) e2 ++
    [.store .rbx .rax 1,
     .pop .rax,
     .store .rbx .rax 0,
     .movr .rax .rbx,
     .addi .rbx 2]
  | .fst e =>
    compile ds c e ++
    [.load .rax .rax 0]
  | .snd e =>
    compile ds c e ++
    [.load .rax .rax 1]
  | .call f e =>
    compile ds c e ++
      [.movpc .r9,
       .addi .r9 5,
       .push .r9,
       .push .rax,
       match Defns.entry ds f with
       | none => .halt
       | some i => .movi .r9 i,
      .jmpabs .r9]
  | .nil => [.movi .rax 0]
  | .cons e1 e2 =>
    compile ds c e1 ++
    [.push .rax] ++
    compile ds (none :: c) e2 ++
    [.store .rbx .rax 1,
     .pop .rax,
     .store .rbx .rax 0,
     .movr .rax .rbx,
     .addi .rbx 2]
  | .is_nil e =>
    -- yunze: two bugs in the prior version:
    --   (1) `.bnz 1` is a no-op — `Step.bnzf` already sets pc := s.pc + 1,
    --       so both branch-taken and fallthrough land at pc+1.
    --   (2) Even with `.bnz 2` the semantics were inverted: bnz fires on
    --       `zf = false` (rax ≠ 0, i.e. pair), so the branch *taken* path
    --       must be the pair (false) answer, not the nil (true) answer.
    -- Fix: swap the two `movi` constants. After `cmp`, set rax to the
    -- *false* answer (0) as default; on `zf = false` (pair) the bnz skips
    -- past the trailing `movi rax 1` so rax stays 0; on `zf = true` (nil)
    -- the bnzf falls through and `movi rax 1` overwrites rax to true.
    compile ds c e ++
    [ .movi .r9 0,
      .cmp .rax .r9,
      .movi .rax 0,   -- default: false  (pair answer)
      .bnz 2,         -- if rax was non-zero (pair), skip the `movi rax 1`
      .movi .rax 1    -- nil case: set to true
    ]

def compile_defn (ds : Defns) (d : Defn) : List Instr :=
  match d with
  | .defn _ x e =>
    compile ds [some x] e ++
    [.pop .r9, -- discard argument
     .pop .r9, -- pop return pointer
     .jmpabs .r9]

def compile_defns' (ds : Defns) (ds' : Defns) : List Instr :=
  match ds' with
  | [] => []
  | d :: ds' =>
    compile_defn ds d ++
    compile_defns' ds ds'

def compile_defns (ds : Defns) : List Instr :=
  compile_defns' ds ds

def compile_prog (ds : Defns) (e : Expr) : List Instr :=
  [.jmp (compile_defns_len ds + 1)] ++ compile_defns ds ++ compile ds [] e ++ [.halt]

-- ═══════════════════════════════════════════════════════════════════════════
-- SECTION 4 — Representation relations
-- ═══════════════════════════════════════════════════════════════════════════
-- `Represents v i h` — source value `v` is encoded as machine word `i` under
--                      heap `h` (ints/bools/nil inline, pairs via two cells).
-- `Related s c r h`  — the machine stack `s` matches the compile-time CEnv
--                      `c` and source env `r` under heap `h`.
-- `Steps`            — reflexive-transitive closure of `Step`.

inductive Represents : Val -> Int -> Heap -> Prop where
  | int {i h} : Represents (.int i) i h
  | bool {b h} : Represents (.bool b) (if b then 1 else 0) h
  | nil {h} : Represents .nil 0 h  -- added this line for nil
  -- yunze: added `i ≥ 1` premise. This rules out pair-address 0, which would
  -- otherwise collide with the nil encoding and break `is_nil` for pairs
  -- allocated at address 0.
  | pair {v1 i1 h v2 i2 i} :
    Represents v1 i1 h ->
    Represents v2 i2 h ->
    Heap.lookup h (i+0) = some i1 -> -- added "some" here to ensure "some" is used for Option
    Heap.lookup h (i+1) = some i2 -> -- added "some" here to ensure "some" is used for Option
    i ≥ 1 ->
    Represents (.pair v1 v2) i h

inductive Related : Stack -> CEnv -> Env -> Heap -> Prop where
  | mt {s h} : Related s [] [] h
  | push {s c r i h} :
    Related s c r h ->
    Related (i :: s) (none :: c) r h
  | bind {s c r x v h i} :
    Related s c r h ->
    Represents v i h ->
    Related (i :: s) ((some x) :: c) ((x,v) :: r) h

theorem Related.lookup {s c r x v h} :
  Related s c r h ->
  Env.lookup r x = some v ->
  ∃ n i,
    CEnv.lookup c x = some n /\
    s[n]? = some i /\
    Represents v i h := by

  intros hrel hlook
  induction hrel with
  | mt => cases hlook
  | push hrel' ih =>
    rcases ih hlook with ⟨n, i, hidx, hstk⟩
    refine ⟨n+1, i, ?_, ?_⟩
    · simp [CEnv.lookup, hidx]
    · simp [hstk]
  | bind hrel' hrep ih =>
    rename_i s i' r y v' h i
    by_cases hxy : x = y
    · subst hxy
      simp [Env.lookup] at hlook
      subst hlook
      refine ⟨0, i, ?_, ?_⟩
      · simp [CEnv.lookup]
      · simpa
    · rename_i r'
      simp [Env.lookup, hxy] at hlook
      rcases ih hlook with ⟨n, j, hidx, hstk⟩
      refine ⟨n+1, j, ?_, ?_⟩
      · simp [CEnv.lookup, hxy, hidx]
      · simp [hstk]

inductive Steps (is : List Instr) : State -> State -> Prop where
  | refl {s} : Steps is s s
  | trans {s s' s''} :
    Steps is s s' ->
    Step is s' s'' ->
    Steps is s s''

theorem Steps.append {is s s' s''} :
  Steps is s s' ->
  Steps is s' s'' ->
  Steps is s s'' := by
  intro h1 h2
  induction h2 generalizing s with
  | refl =>
    exact h1
  | trans h2 hstep ih =>
    exact Steps.trans (ih h1) hstep

-- ═══════════════════════════════════════════════════════════════════════════
-- SECTION 5 — Helper lemmas
-- ═══════════════════════════════════════════════════════════════════════════
-- General-purpose lemmas about `get`, `Heap.lookup`/`Heap.store`, `FreshFrom`,
-- `HeapExtends`, `Represents.mono`, `Related.mono`/`push`/`bind`, and
-- inversion helpers like `Represents.int_inv` / `Represents.pair_inv`.

theorem get_append_left {α} {xs ys : List α} {i : Nat} {x : α} :
  get xs i x ->
  get (xs ++ ys) i x := by
  intro h
  induction h with
  | hd =>
    exact get.hd
  | tl h ih =>
    exact get.tl ih

theorem get_append_right {α} {xs ys : List α} {i : Nat} {x : α} :
  get ys i x ->
  get (xs ++ ys) (xs.length + i) x := by
  intro h
  induction xs generalizing i with
  | nil =>
    simpa using h
  | cons y xs ih =>
    simpa [Nat.add_assoc, Nat.succ_eq_add_one, Nat.add_left_comm, Nat.add_comm] using get.tl (ih h)

theorem get_of_getElem? {α} {xs : List α} {i : Nat} {x : α} :
  xs[i]? = some x ->
  get xs i x := by
  intro h
  induction xs generalizing i with
  | nil =>
    cases h
  | cons y ys ih =>
    cases i with
    | zero =>
      simp at h
      subst h
      exact get.hd
    | succ i =>
      simp at h
      exact get.tl (ih h)

def maxAbsIntList (xs : List Int) : Nat :=
  xs.foldl (fun m x => Nat.max m (Int.natAbs x)) 0

def dom (h : Heap) : List Int := h.map Prod.fst

theorem le_foldl_maxAbs (acc : Nat) (xs : List Int) :
  acc ≤ xs.foldl (fun m x => Nat.max m (Int.natAbs x)) acc := by
  induction xs generalizing acc with
  | nil =>
    simp
  | cons x xs ih =>
    simp [List.foldl]
    exact Nat.le_trans
      (Nat.le_max_left acc (Int.natAbs x))
      (ih (Nat.max acc (Int.natAbs x)))

theorem natAbs_le_maxAbsIntList_of_mem {a : Int} {xs : List Int} :
  a ∈ xs ->
  Int.natAbs a ≤ maxAbsIntList xs := by
  intro hmem
  have aux :
      ∀ (acc : Nat), a ∈ xs ->
      Int.natAbs a ≤ xs.foldl (fun m x => Nat.max m (Int.natAbs x)) acc := by
    intro acc hmem
    induction xs generalizing acc with
    | nil =>
      cases hmem
    | cons x xs ih =>
      simp [List.foldl]
      simp at hmem
      rcases hmem with rfl | hmem'
      · exact Nat.le_trans
          (Nat.le_max_right acc (Int.natAbs a))
          (le_foldl_maxAbs (acc := .max acc (Int.natAbs a)) (xs := xs))
      · apply ih hmem'
        assumption
  simpa [maxAbsIntList] using aux 0 hmem

-- Added these to prove that writing to fresh addr preserves existing lookup
-- Lemmas: lookup_ext_same, lookup_ext_diff
theorem lookup_ext_same (h : Heap) (a v : Int) :
  Heap.lookup (Heap.ext h a v) a = some v := by
  simp [Heap.lookup, Heap.ext]

theorem lookup_ext_diff (h : Heap) (a b v : Int) (h_ne : b ≠ a) :
  Heap.lookup (Heap.ext h a v) b = Heap.lookup h b := by
  simp [Heap.lookup, Heap.ext, h_ne]

theorem lookup_some_mem_dom {h : Heap} {a v : Int} :
  Heap.lookup h a = some v ->
  a ∈ dom h := by
  intro hlook
  induction h with
  | nil =>
    simp [Heap.lookup] at hlook
  | cons p h ih =>
    rcases p with ⟨j, k⟩
    by_cases haj : a = j
    · subst haj
      simp [dom]
    · have : Heap.lookup h a = some v := by
        simpa [Heap.lookup, haj] using hlook
      have hmem : a ∈ dom h := ih this
      simpa [dom] using List.mem_cons_of_mem j hmem

-- yunze: strengthened FreshFrom to also require `a ≥ 1`. This is the
-- invariant that unblocks the `isnilf` case: when we compare a pair address
-- against `0`, we need to know the address is non-zero. We carry the
-- positivity through the simulation alongside the existing freshness facts.
structure FreshFrom (h : Heap) (a : Int) : Prop where
  pos    : a ≥ 1
  lookup : ∀ k : Nat, Heap.lookup h (a + k) = none

theorem exists_freshFrom (h : Heap) :
  ∃ a : Int, FreshFrom h a := by
  let M : Nat := maxAbsIntList (dom h)
  refine ⟨Int.ofNat (M + 1), ?_, ?_⟩
  -- yunze: pos field — `Int.ofNat (M + 1) ≥ 1` since `M + 1 ≥ 1`.
  · show (Int.ofNat (M + 1) : Int) ≥ 1
    have h1 : (1 : Nat) ≤ M + 1 := Nat.succ_le_succ (Nat.zero_le M)
    have : (Int.ofNat 1 : Int) ≤ Int.ofNat (M + 1) := Int.ofNat_le.mpr h1
    simpa using this
  -- ! lookup field — the original freshness proof.
  · intro k
    cases hL : Heap.lookup h (Int.ofNat (M + 1) + Int.ofNat k) with
    | none =>
      rfl
    | some v =>
      have hmem : (Int.ofNat (M + 1) + Int.ofNat k) ∈ dom h :=
        lookup_some_mem_dom (by simpa [hL])
      have hbound : Int.natAbs (Int.ofNat (M + 1) + Int.ofNat k) ≤ M := by
        simpa [M] using natAbs_le_maxAbsIntList_of_mem hmem
      have hadd : Int.ofNat (M + 1) + Int.ofNat k = Int.ofNat (M + 1 + k) := by
        simpa [Nat.add_assoc] using (Int.ofNat_add_ofNat (M + 1) k)
      have hbad : M + 1 + k ≤ M := by
        simpa [hadd] using hbound
      have : M + 1 ≤ M := Nat.le_trans (Nat.le_add_right (M + 1) k) hbad
      exact (Nat.not_succ_le_self M this).elim

def HeapExtends (h h' : Heap) : Prop :=
  ∀ a v, Heap.lookup h a = some v -> Heap.lookup h' a = some v

theorem HeapExtends.refl {h : Heap} : HeapExtends h h := by
  intro a v hlook
  exact hlook

theorem HeapExtends.trans {h h' h'' : Heap} :
  HeapExtends h h' ->
  HeapExtends h' h'' ->
  HeapExtends h h'' := by
  intro h1 h2 a v hlook
  exact h2 _ _ (h1 _ _ hlook)

theorem HeapExtends.write {h : Heap} {a v : Int} :
  Heap.lookup h a = none ->
  HeapExtends h (Heap.ext h a v) := by
  intro hnone a' v' hlook
  by_cases haa : a' = a
  · subst haa
    rw [hnone] at hlook
    contradiction
  · simpa [Heap.lookup, Heap.ext, haa] using hlook

theorem Represents.mono {v i h h'} :
  Represents v i h ->
  HeapExtends h h' ->
  Represents v i h' := by
  intro hrep hext
  induction hrep with
  | int =>
    exact .int
  | bool =>
    exact .bool
  | nil =>
    exact .nil
  | pair h1 h2 hlook1 hlook2 hpos ih1 ih2 =>
    -- yunze: thread the new `i ≥ 1` field through mono.
    exact .pair (ih1 hext) (ih2 hext) (hext _ _ hlook1) (hext _ _ hlook2) hpos

theorem Represents.bool_inv {b i h} :
  Represents (.bool b) i h ->
  i = if b then 1 else 0 := by
  intro hrep
  cases hrep with
  | bool =>
      rfl

-- Helper for checking that after is_nil compiles and puts 1 or 0 in rax
-- theorem proves that ints correctly represent .bool true or .bool false
theorem Represents.bool_of_int {i : Int} :
  (i = 1 ∨ i = 0) -> Represents (.bool (i = 1)) i h := by
  intro h
  rcases h with rfl | rfl
  · simp; exact .bool
  · simp; exact .bool

-- ? Yunze: I added a few more helper functions here
-- ! Inversion helper for `int`: lets us read off `s.regs.rax = i` from
-- ! `Represents (.int i) s.regs.rax h` (the direct `cases` tactic fails when
-- ! the encoded value is a projection rather than a free variable).
theorem Represents.int_inv {i j h} :
  Represents (.int i) j h ->
  j = i := by
  intro hrep
  cases hrep with
  | int => rfl

-- ! Inversion helper for `pair`: same motivation as `int_inv` /`bool_inv` —
-- ! when the address `i` is a projection like `s.regs.rax`, we cannot `cases`
-- ! the hypothesis directly. This lemma packages the four pieces explicitly.
-- yunze: extended `pair_inv` to also expose the new `i ≥ 1` premise as the
-- final existential conjunct. Use sites that don't need it can ignore it
-- with `_`.
theorem Represents.pair_inv {v1 v2 i h} :
  Represents (.pair v1 v2) i h ->
  ∃ i1 i2,
    Represents v1 i1 h ∧
    Represents v2 i2 h ∧
    Heap.lookup h (i+0) = some i1 ∧
    Heap.lookup h (i+1) = some i2 ∧
    i ≥ 1 := by
  intro hrep
  cases hrep with
  | pair h1 h2 l1 l2 hpos =>
    rename_i i1 i2
    exact ⟨i1, i2, h1, h2, l1, l2, hpos⟩

-- ! Inversion helper for `is_nil`
theorem Represents.nil_inv {i h} :
  Represents .nil i h -> i = 0 := by
  intro h; cases h; rfl

-- Lemma verifies that if we store two values at b and b+1
-- Represent a pair/cons at address b
-- yunze: switched the freshness uses to `.lookup` projections (FreshFrom is now
-- a structure), and supplied the new `b ≥ 1` constructor field from `h_fresh.pos`.
theorem Represents.cons {h : Heap} {v1 v2 : Val} {i1 i2 b : Int}
  (h_fresh : FreshFrom h b)
  (h1 : Represents v1 i1 h)
  (h2 : Represents v2 i2 h) :
  Represents (.pair v1 v2) b ((h.ext (b + 1) i2).ext b i1) := by
  let h_mid := h.ext (b + 1) i2
  let h_fin := h_mid.ext b i1
  apply Represents.pair
  · apply Represents.mono h1
    apply HeapExtends.trans (h' := h_mid)
    · apply HeapExtends.write
      have hf1 := h_fresh.lookup 1
      simpa using hf1
    · apply HeapExtends.write
      simp [h_mid, Heap.lookup, Heap.ext]
      have hne : b ≠ b + 1 := by omega
      simp [hne]
      have hf0 := h_fresh.lookup 0
      simpa using hf0
  · apply Represents.mono h2
    apply HeapExtends.trans (h' := h_mid)
    · apply HeapExtends.write
      have hf1 := h_fresh.lookup 1
      simpa using hf1
    · apply HeapExtends.write
      simp [h_mid, Heap.lookup, Heap.ext]
      have hne : b ≠ b + 1 := by omega
      simp [hne]
      have hf0 := h_fresh.lookup 0
      simpa using hf0
  · simp [Heap.lookup, Heap.ext]
  · have h_ne : b + 1 ≠ b := by omega
    simp [Heap.lookup, Heap.ext, h_ne]
  · -- yunze: new `b ≥ 1` field on Represents.pair, supplied from h_fresh.pos.
    exact h_fresh.pos

theorem Related.mono {s c r h h'} :
  Related s c r h ->
  HeapExtends h h' ->
  Related s c r h' := by
  intro hrel hext
  induction hrel with
  | mt =>
    exact .mt
  | push hrel ih =>
    exact .push (ih hext)
  | bind hrel hrep ih =>
    exact .bind (ih hext) (Represents.mono hrep hext)

theorem Related.push_mono {s c r h h' i} :
  Related s c r h ->
  HeapExtends h h' ->
  Related (i :: s) (none :: c) r h' := by
  intro hrel hext
  exact Related.push (i := i) (Related.mono hrel hext)

theorem Related.pop {s c r h i} :
  Related (i :: s) (none :: c) r h ->
  Related s c r h := by
  intro hrel
  cases hrel with
  | push h => exact h

theorem Related.bind_mono {s c r x v h h' i} :
  Related s c r h ->
  Represents v i h ->
  HeapExtends h h' ->
  Related (i :: s) (some x :: c) ((x, v) :: r) h' := by
  intro hrel hrep hext
  apply Related.bind
  · exact Related.mono hrel hext
  · exact Represents.mono hrep hext

theorem ext_lookup_of_ne {h : Heap} {a b i : Int} (hba : b ≠ a) :
  Heap.lookup (Heap.ext h a i) b = Heap.lookup h b := by
  simp [Heap.lookup, Heap.ext, hba]

-- ! If `a` was fresh before, then after writing at `a` and `a+1`,
-- ! everything from `a+2` onward is still fresh.
theorem FreshFrom.step {h : Heap} {a i1 i2 : Int} :
  FreshFrom h a ->
  FreshFrom ((h.ext (a + 1) i2).ext a i1) (a + 2) := by
  intro hfresh
  refine ⟨?_, ?_⟩
  -- yunze: pos field — `a ≥ 1` implies `a + 2 ≥ 3 ≥ 1`.
  · have hpos : a ≥ 1 := hfresh.pos
    show a + 2 ≥ 1
    omega
  -- ! lookup field — original argument.
  · intro k
    -- ? Expand the two heap writes and check the queried address is not `a`.
    have hne1 : a + 2 + k ≠ a := by
      omega
    -- ? Check it is also not `a + 1`.
    have hne2 : a + 2 + k ≠ a + 1 := by
      omega
    rw [ext_lookup_of_ne hne1, ext_lookup_of_ne hne2]
    -- ? Now we can use the original freshness from `a`.
    have := hfresh.lookup (k + 2)
    simpa [Int.add_assoc, Int.add_left_comm, Int.add_comm] using this

-- ! The compiler always produces exactly `compile_len e` instructions.
theorem compile_length (ds : Defns) (c : CEnv) (e : Expr) :
  (compile ds c e).length = compile_len e := by
  induction e generalizing c with
  | int i =>
    simp [compile, compile_len]
  | bool b =>
    simp [compile, compile_len]
  | succ e ih =>
    simp [compile, compile_len, ih, List.length_append]
  | pred e ih =>
    simp [compile, compile_len, ih, List.length_append]
  | plus e1 e2 ih1 ih2 =>
    simp [compile, compile_len, ih1, ih2, List.length_append, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
  | times e1 e2 ih1 ih2 =>
    simp [compile, compile_len, ih1, ih2, List.length_append, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
  | ifte e1 e2 e3 ih1 ih2 ih3 =>
    simp [compile, compile_len, ih1, ih2, ih3, List.length_append, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
  | neg e ih =>
    simp [compile, compile_len, ih, List.length_append]
  | bind x e1 e2 ih1 ih2 =>
    simp [compile, compile_len, ih1, ih2, List.length_append, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
  | var x =>
    simp [compile, compile_len]
    split <;> simp
  | call f e ih =>
    simp [compile, compile_len, ih, List.length_append]
  | pair e1 e2 ih1 ih2 =>
    simp [compile, compile_len, ih1, ih2, List.length_append, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
  | fst e ih =>
    simp [compile, compile_len, ih, List.length_append]
  | snd e ih =>
    simp [compile, compile_len, ih, List.length_append]
  | nil =>
    simp [compile, compile_len]
  | cons e1 e2 ih1 ih2 =>
    simp [compile, compile_len, ih1, ih2, List.length_append, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
  | is_nil e ih =>
    simp [compile, compile_len, ih, List.length_append]

-- ! A compiled function body has the expected fixed extra instructions at the end.
theorem compile_defn_length (ds : Defns) (d : Defn) :
  (compile_defn ds d).length = compile_defn_len d := by
  cases d with
  | defn f x e =>
    simp [compile_defn, compile_defn_len, compile_length, List.length_append]

theorem compile_defns'_length (ds : Defns) (ds' : Defns) :
  (compile_defns' ds ds').length = compile_defns_len ds' := by
  induction ds' with
  | nil =>
    simp [compile_defns', compile_defns_len]
  | cons d ds' ih =>
    simp [compile_defns', compile_defns_len, compile_defn_length, ih, List.length_append]

-- ! The total compiled definitions length matches the sum described by `compile_defns_len`.
theorem compile_defns_length (ds : Defns) :
  (compile_defns ds).length = compile_defns_len ds := by
  simpa [compile_defns] using compile_defns'_length ds ds

-- ═══════════════════════════════════════════════════════════════════════════
-- SECTION 6 — `code_at` and program layout
-- ═══════════════════════════════════════════════════════════════════════════
-- `code_at is pc code` says that `code` appears as a contiguous block starting
-- at position `pc` inside `is`. Combined with the prefix lemmas below, this
-- lets us thread "this sub-expression's code lives here" through the proof.

def code_at (is : List Instr) (pc : Nat) (code : List Instr) : Prop :=
  ∃ pre post,
    is = pre ++ code ++ post ∧
    pc = pre.length

theorem code_at_refl {code : List Instr} :
  code_at code 0 code := by
  refine ⟨[], [], ?_, rfl⟩
  simp

theorem code_at_head {is : List Instr} {pc : Nat} {i : Instr} {code : List Instr} :
  code_at is pc (i :: code) ->
  instr_at is pc i := by
  intro hcode
  rcases hcode with ⟨pre, post, rfl, rfl⟩
  simpa [Nat.add_comm] using
    (get_append_right (xs := pre) (ys := i :: code ++ post) get.hd)

theorem code_at_tail {is : List Instr} {pc : Nat} {i : Instr} {code : List Instr} :
  code_at is pc (i :: code) ->
  code_at is (pc + 1) code := by
  intro hcode
  rcases hcode with ⟨pre, post, his, hpc⟩
  refine ⟨pre ++ [i], post, ?_, ?_⟩
  · rw [his]
    simp [List.append_assoc]
  · rw [hpc]
    simp

theorem code_at_app_left {is : List Instr} {pc : Nat} {c1 c2 : List Instr} :
  code_at is pc (c1 ++ c2) ->
  code_at is pc c1 := by
  intro hcode
  rcases hcode with ⟨pre, post, his, hpc⟩
  refine ⟨pre, c2 ++ post, ?_, hpc⟩
  simpa [List.append_assoc] using his

theorem code_at_app_right {is : List Instr} {pc : Nat} {c1 c2 : List Instr} :
  code_at is pc (c1 ++ c2) ->
  code_at is (pc + c1.length) c2 := by
  intro hcode
  rcases hcode with ⟨pre, post, his, hpc⟩
  refine ⟨pre ++ c1, post, ?_, ?_⟩
  · simpa [List.append_assoc] using his
  · rw [hpc, List.length_append]

theorem code_at_app_right2 {is : List Instr} {pc : Nat} {c1 c2 c3 : List Instr} :
  code_at is pc (c1 ++ c2 ++ c3) ->
  code_at is (pc + c1.length) c2 := by
  intro hcode
  exact code_at_app_right (code_at_app_left (is := is) (pc := pc) (c1 := c1 ++ c2) (c2 := c3) hcode)

theorem code_at_compile_left {ds : Defns} {c : CEnv} {e : Expr} {is : List Instr} {pc : Nat} {tail : List Instr} :
  code_at is pc (compile ds c e ++ tail) ->
  code_at is pc (compile ds c e) := by
  intro hcode
  exact code_at_app_left (c2 := tail) hcode

-- ? super helpful
theorem code_at_after_compile_prefix
    {ds : Defns} {c : CEnv} {e : Expr} {is : List Instr} {pc : Nat}
    {pfx : List Instr} {mid : List Instr} {sfx : List Instr} :
  code_at is pc (compile ds c e ++ pfx ++ mid ++ sfx) ->
  code_at is (pc + compile_len e + pfx.length) mid := by
  intro hcode
  have hcode' :
      code_at is pc ((compile ds c e ++ pfx) ++ mid ++ sfx) := by
    simpa [List.append_assoc] using hcode
  have htail := code_at_app_right2 (is := is) (pc := pc)
    (c1 := compile ds c e ++ pfx) (c2 := mid) (c3 := sfx) hcode'
  have hlen : (compile ds c e ++ pfx).length = compile_len e + pfx.length := by
    simp [compile_length]
  simpa [hlen, Nat.add_assoc] using htail

theorem code_at_after_two_compiles {ds c e1 e2 is pc pfx1 pfx2 mid sfx} :
  code_at is pc (compile ds c e1 ++ pfx1 ++ compile ds (none :: c) e2 ++ pfx2 ++ mid ++ sfx) ->
  code_at is (pc + compile_len e1 + pfx1.length + compile_len e2 + pfx2.length) mid := by
  intro h
  have h1 : code_at is (pc + compile_len e1 + pfx1.length) (compile ds (none :: c) e2 ++ pfx2 ++ mid) := by
    have h_split : code_at is pc (compile ds c e1 ++ pfx1 ++ (compile ds (none :: c) e2 ++ pfx2 ++ mid) ++ sfx) := by
      simpa [List.append_assoc] using h
    apply code_at_after_compile_prefix h_split
  have h2 : code_at is (pc + compile_len e1 + pfx1.length + compile_len e2 + pfx2.length) mid := by
    have h_split2 : code_at is (pc + compile_len e1 + pfx1.length) (compile ds (none :: c) e2 ++ pfx2 ++ mid ++ []) := by
      simpa using h1
    apply code_at_after_compile_prefix h_split2
  simpa [Nat.add_assoc] using h2

theorem code_at_nil {is : List Instr} {pc : Nat} {code : List Instr} :
  code_at is pc code ->
  code_at is pc [] := by
  intro hcode
  rcases hcode with ⟨pre, post, his, hpc⟩
  refine ⟨pre, code ++ post, ?_, hpc⟩
  simpa [List.append_assoc] using his

theorem instr_at_middle {pre code post : List Instr} {i : Nat} {ins : Instr} :
  instr_at code i ins ->
  instr_at (pre ++ code ++ post) (pre.length + i) ins := by
  intro h
  simpa [List.append_assoc] using
    (get_append_right (xs := pre) (ys := code ++ post) (get_append_left h))

theorem instr_at_of_code_at {is code : List Instr} {pc i : Nat} {ins : Instr} :
  code_at is pc code ->
  instr_at code i ins ->
  instr_at is (pc + i) ins := by
  intro hcode hins
  rcases hcode with ⟨pre, post, his, hpc⟩
  rw [his, hpc]
  exact instr_at_middle (pre := pre) (code := code) (post := post) hins

theorem compile_defns'_split {ds ds' : Defns} {f x : Var} {e : Expr} :
  Defns.lookup ds' f = some (.defn f x e) ->
  ∃ pre post,
    compile_defns' ds ds' = pre ++ compile_defn ds (.defn f x e) ++ post /\
    Defns.entry ds' f = some (pre.length + 1) := by
  intro hlook
  induction ds' with
  | nil =>
    simp [Defns.lookup] at hlook
  | cons d ds' ih =>
    cases d with
    | defn g y e' =>
      by_cases hfg : f = g
      · subst hfg
        simp [Defns.lookup] at hlook
        cases hlook
        subst y
        subst e'
        refine ⟨[], compile_defns' ds ds', ?_, ?_⟩
        · simp [compile_defns']
        · simp [Defns.entry]
      · simp [Defns.lookup, hfg] at hlook
        rcases ih hlook with ⟨pre, post, hcomp, hentry⟩
        refine ⟨compile_defn ds (.defn g y e') ++ pre, post, ?_, ?_⟩
        · simp [compile_defns', hcomp, List.append_assoc]
        · simp [Defns.entry, hfg, hentry, compile_defn_length, Nat.add_assoc]

-- ! If a function is found in `ds`, then its compiled code appears as a block
-- ! inside `compile_defns ds`, and its entry points to the start of that block.
theorem compile_defns_split {ds : Defns} {f x : Var} {e : Expr} :
  Defns.lookup ds f = some (.defn f x e) ->
  ∃ pre post,
    compile_defns ds = pre ++ compile_defn ds (.defn f x e) ++ post /\
    Defns.entry ds f = some (pre.length + 1) := by
  intro hlook
  simpa [compile_defns] using compile_defns'_split (ds := ds) (ds' := ds) hlook

def defns_in_place (is : List Instr) (ds : Defns) : Prop :=
  ∀ {f x e},
    Defns.lookup ds f = some (.defn f x e) ->
    code_at is (Defns.entry ds f |>.getD 0) (compile_defn ds (.defn f x e))

theorem compile_prog_defns_in_place {ds : Defns} {e : Expr} :
  defns_in_place (compile_prog ds e) ds := by
  intro f x e' hlook
  rcases compile_defns_split hlook with ⟨pre, post, hsplit, hentry⟩
  refine ⟨[.jmp (compile_defns_len ds + 1)] ++ pre, post ++ compile ds [] e ++ [.halt], ?_, ?_⟩
  · simp [compile_prog, hsplit, List.append_assoc]
  · simp [hentry]

-- ! The main program expression starts right after the compiled function block.
theorem compile_prog_main_code_at {ds : Defns} {e : Expr} :
  code_at (compile_prog ds e) (compile_defns_len ds + 1) (compile ds [] e ++ [.halt]) := by
  refine ⟨[.jmp (compile_defns_len ds + 1)] ++ compile_defns ds, [], ?_, ?_⟩
  · simp [compile_prog, List.append_assoc]
  · simp [compile_defns_length]

-- ! The expression code itself is also at that same start position.
theorem compile_prog_expr_code_at {ds : Defns} {e : Expr} :
  code_at (compile_prog ds e) (compile_defns_len ds + 1) (compile ds [] e) := by
  exact code_at_compile_left (tail := [.halt]) compile_prog_main_code_at

-- ═══════════════════════════════════════════════════════════════════════════
-- SECTION 7 — Per-instruction correctness (postcondition shape)
-- ═══════════════════════════════════════════════════════════════════════════
-- `ExprPost e pc stk k h v s'` is the postcondition we want each compiled
-- expression to satisfy: the pc has advanced past the compiled code, the
-- stack is restored modulo a continuation `k`, the heap only grows, and
-- the result value `v` is represented in `rax` of the final state `s'`.

def ExprPost (e : Expr) (pc : Nat) (stk k : Stack) (h : Heap) (v : Val) (s' : State) : Prop :=
  s'.pc = pc + compile_len e ∧
  s'.stack = stk ++ k ∧
  Represents v s'.regs.rax s'.heap ∧
  HeapExtends h s'.heap

theorem compiler_expr_correct_succ
    {ds c e i is pc stk k rs zf h}
    (hcode : code_at is pc (compile ds c (.succ e)))
    (hih :
      ∃ s',
        Steps is { pc := pc, regs := rs, stack := stk ++ k, zf := zf, heap := h } s' ∧
        ExprPost e pc stk k h (.int i) s' ∧
        FreshFrom s'.heap s'.regs.rbx) :
    ∃ s',
      Steps is { pc := pc, regs := rs, stack := stk ++ k, zf := zf, heap := h } s' ∧
      ExprPost (.succ e) pc stk k h (.int (i + 1)) s' ∧
      FreshFrom s'.heap s'.regs.rbx := by
      rcases hih with ⟨s1, hs1, hpost1, hfresh1⟩
      rcases hpost1 with ⟨hpc1, hstack1, hrepr1, hext1⟩
      have hcode_e : code_at is pc (compile ds c e) := by
        exact code_at_compile_left (tail := [.addi Reg.rax 1]) hcode
      have hcode_addi : instr_at is (pc + compile_len e) (.addi Reg.rax 1) := by
        have hmid : code_at is (pc + compile_len e) [.addi Reg.rax 1] := by
          simpa using
            (code_at_after_compile_prefix
              (ds := ds) (c := c) (e := e) (is := is) (pc := pc)
              (pfx := []) (mid := [.addi Reg.rax 1]) (sfx := []) (by simpa using hcode))
        exact code_at_head hmid
      have hrepr_int : s1.regs.rax = i := by
        cases hrepr1 with
        | int =>
          rfl
      let s2 : State :=
        { s1 with
          pc := s1.pc + 1
          regs := Reg.write Reg.rax (Reg.read Reg.rax s1.regs + 1) s1.regs }
      refine ⟨s2, ?_, ?_, hfresh1⟩
      · have hcode_addi' : instr_at is s1.pc (.addi Reg.rax 1) := by
          simpa [hpc1] using hcode_addi
        exact Steps.trans hs1 (Step.addi (s := s1) hcode_addi')
      · constructor
        · -- ? The `succ` code adds one more instruction after `e`.
          simp [s2, hpc1, compile_len, Nat.add_assoc]
        · constructor
          · -- ? The stack is unchanged by `addi`.
            simp [s2, hstack1]
          · constructor
            · -- ? The result in `rax` is now `i + 1`.
              simpa [s2, hrepr_int, Reg.read, Reg.write] using (Represents.int (i := i + 1) (h := s1.heap))
            · exact hext1

theorem compiler_expr_correct_pred
    {ds c e i is pc stk k rs zf h}
    (hcode : code_at is pc (compile ds c (.pred e)))
    (hih :
      ∃ s',
        Steps is { pc := pc, regs := rs, stack := stk ++ k, zf := zf, heap := h } s' ∧
        ExprPost e pc stk k h (.int i) s' ∧
        FreshFrom s'.heap s'.regs.rbx) :
    ∃ s',
      Steps is { pc := pc, regs := rs, stack := stk ++ k, zf := zf, heap := h } s' ∧
      ExprPost (.pred e) pc stk k h (.int (i - 1)) s' ∧
      FreshFrom s'.heap s'.regs.rbx := by
  rcases hih with ⟨s1, hs1, hpost1, hfresh1⟩
  rcases hpost1 with ⟨hpc1, hstack1, hrepr1, hext1⟩
  have hcode_e : code_at is pc (compile ds c e) := by
    exact code_at_compile_left
      (tail := [.addi Reg.rax (-1)])
      hcode
  have haddi :
      instr_at is (pc + compile_len e) (.addi Reg.rax (-1)) := by
    have hmid :
        code_at is (pc + compile_len e)
          [.addi Reg.rax (-1)] := by
      simpa using
        (code_at_after_compile_prefix
          (ds := ds)
          (c := c)
          (e := e)
          (is := is)
          (pc := pc)
          (pfx := [])
          (mid := [.addi Reg.rax (-1)])
          (sfx := [])
          (by simpa [compile] using hcode))
    exact code_at_head hmid
  have hrepr_int : s1.regs.rax = i := by
    cases hrepr1 with
    | int =>
      rfl
  let s2 : State :=
    { s1 with
      pc := s1.pc + 1
      regs := Reg.write Reg.rax
        (Reg.read Reg.rax s1.regs - 1)
        s1.regs }
  refine ⟨s2, ?_, ?_, hfresh1⟩
  · have haddi' :
        instr_at is s1.pc (.addi .rax (-1)) := by
      simpa [hpc1] using haddi
    exact
      Steps.trans
        hs1
        (Step.addi (s := s1) haddi')
  · constructor
    · simp [s2, hpc1, compile_len, Nat.add_assoc]
    · constructor
      · simp [s2, hstack1]
      · constructor
        ·
          simpa [s2, hrepr_int, Reg.read, Reg.write] using (Represents.int (i := i - 1) (h := s1.heap))
        · exact hext1

-- ═══════════════════════════════════════════════════════════════════════════
-- SECTION 8 — Main simulation theorem
-- ═══════════════════════════════════════════════════════════════════════════
-- The heart of the proof: source-level evaluation `Eval ds r e v` is simulated
-- by the compiled code starting from any state `s` that is `Related` to `r`,
-- ending in some `s'` satisfying `ExprPost`. Proved by induction on `heval`
-- with one case per `Eval` constructor.

-- ! This is the main simulation theorem:
-- ! if the source expression evaluates to `v`, then the compiled code
-- ! takes a related machine state to a state representing `v`.
theorem compiler_correct_general
    {ds c r e v is pc stk k rs zf h}
    (hdefs : defns_in_place is ds)
    (hcode : code_at is pc (compile ds c e))
    (hrel : Related stk c r h)
    (heval : Eval ds r e v)
    (hfresh : FreshFrom h rs.rbx) :
    ∃ s',
      Steps is { pc := pc, regs := rs, stack := stk ++ k, zf := zf, heap := h } s' ∧
      ExprPost e pc stk k h v s' ∧
      FreshFrom s'.heap s'.regs.rbx := by
  induction heval generalizing pc stk rs zf h k c with

  | intr i =>
    let s' : State := { pc := pc + 1, regs := Reg.write .rax i rs, stack := stk ++ k, zf := zf, heap := h }
    refine ⟨s', ?_, ⟨?_, ?_, ?_, ?_⟩, hfresh⟩
    · apply Steps.trans Steps.refl
      apply Step.movi (s := { pc := pc, regs := rs, stack := stk ++ k, zf := zf, heap := h })
      exact code_at_head hcode
    · rfl
    · rfl
    · exact Represents.int
    · exact HeapExtends.refl

  | nilr =>
    let s' : State := {
      pc := pc + 1,
      regs := Reg.write .rax 0 rs,
      stack := stk ++ k,
      zf := zf,
      heap := h
    }
    refine ⟨s', ?_, ?_, hfresh⟩
    · apply Steps.trans Steps.refl
      apply Step.movi
        (s := {
          pc := pc,
          regs := rs,
          stack := stk ++ k,
          zf := zf,
          heap := h
        })
      exact code_at_head hcode
    · refine ⟨?_, ?_, ?_, ?_⟩
      · simp [s', compile_len]
      · rfl
      · exact Represents.nil
      · exact HeapExtends.refl

  | boolr b =>
    let s' : State := {
      pc := pc + 1,
      regs := Reg.write .rax (if b then 1 else 0) rs,
      stack := stk ++ k,
      zf := zf,
      heap := h
    }
    refine ⟨s', ?_, ?_, hfresh⟩
    · apply Steps.trans Steps.refl
      apply Step.movi
        (s := {
          pc := pc,
          regs := rs,
          stack := stk ++ k,
          zf := zf,
          heap := h
        })
      exact code_at_head hcode
    · refine ⟨?_, ?_, ?_, ?_⟩
      · simp [s', compile_len]
      · rfl
      · exact Represents.bool
      · exact HeapExtends.refl

  | varr hlook =>
    rename_i r v x
    rcases Related.lookup hrel hlook with
      ⟨n, i, hcenv, hstackget, hrep⟩
    have hcode_var :
        compile ds c (.var x) = [.stackget .rax n] := by
      simp [compile]
      rw [hcenv]
    have hcode_at :
        code_at is pc ([.stackget .rax n]) := by
      simpa [hcode_var] using hcode
    have hinst :
        instr_at is pc (.stackget .rax n) := by
      exact code_at_head hcode_at
    have hget : get stk n i :=
      get_of_getElem? hstackget
    let s' : State := {
      pc := pc + 1,
      regs := Reg.write .rax i rs,
      stack := stk ++ k,
      zf := zf,
      heap := h
    }
    refine ⟨s', ?_, ?_, hfresh⟩
    · exact
        Steps.trans
          Steps.refl
          (Step.stackget hinst (get_append_left hget))
    · constructor
      · simp [s', compile_len]
      · constructor
        · rfl
        · constructor
          · exact hrep
          · exact HeapExtends.refl

  | succr _ ih =>
    -- ! `succ e` compiles to `compile e` followed by a single `addi rax 1`.
    -- ! Peel off the prefix code for `e`, hand the IH to the dedicated helper
    -- ! `compiler_expr_correct_succ`, and let it deal with the trailing `addi`.
    have hcode_e : code_at is pc (compile ds c _) :=
      code_at_compile_left
        (tail := [.addi Reg.rax 1])
        (by simpa [compile] using hcode)
    exact compiler_expr_correct_succ hcode (ih hcode_e hrel hfresh)

  | predr _ ih =>
    -- ! Mirror image of the `succr` case
    have hcode_e : code_at is pc (compile ds c _) :=
      code_at_compile_left
        (tail := [.addi Reg.rax (-1)])
        (by simpa [compile] using hcode)
    exact compiler_expr_correct_pred hcode (ih hcode_e hrel hfresh)

  -- TODO(remaining cases): the same overall recipe applies to every binary or
  -- unary form below, but each one needs a small dedicated helper (or some
  -- careful inline reasoning) for the trailing machine-code template.
  -- Strategy notes for each are kept short, so you can knock them out one at
  -- a time without re-deriving the plan every time.

  | plusr _ _ ih1 ih2 =>
    -- ! `plus e1 e2` compiles to:
    -- !     compile e1 ++ [push rax] ++ compile e2 ++ [pop r9, addr rax r9]
    -- ! Flow:
    -- !   IH1 → rax = i1.   push rax   →   stack has i1 on top.
    -- !   IH2 on extended stack (c gains a `none` frame) → rax = i2.
    -- !   pop r9 → r9 = i1, stack restored.   addr rax r9 → rax = i2 + i1.
    rename_i r' e1_sub i1_val e2_sub i2_val _hev1 _hev2
    -- ! 1) Locate all the sub-pieces inside `is`.
    have hcode_e1 : code_at is pc (compile ds c e1_sub) :=
      code_at_compile_left
        (tail := [.push .rax] ++ compile ds (none :: c) e2_sub ++ [.pop .r9, .addr .rax .r9])
        (by simpa [compile, List.append_assoc] using hcode)
    have hpush_at_abs : instr_at is (pc + compile_len e1_sub) (.push .rax) := by
      have hmid : code_at is (pc + compile_len e1_sub) [.push .rax] := by
        simpa using
          (code_at_after_compile_prefix
            (pfx := []) (mid := [.push .rax])
            (sfx := compile ds (none :: c) e2_sub ++ [.pop .r9, .addr .rax .r9])
            (by simpa [compile, List.append_assoc] using hcode))
      exact code_at_head hmid
    have hcode_e2_abs :
        code_at is (pc + compile_len e1_sub + 1) (compile ds (none :: c) e2_sub) := by
      simpa using
        (code_at_after_compile_prefix
          (pfx := [.push .rax]) (mid := compile ds (none :: c) e2_sub)
          (sfx := [.pop .r9, .addr .rax .r9])
          (by simpa [compile, List.append_assoc] using hcode))
    have hpop_addr_abs :
        code_at is (pc + compile_len e1_sub + 1 + compile_len e2_sub)
          [.pop .r9, .addr .rax .r9] := by
      have h : code_at is (pc + compile_len e1_sub + 1)
          (compile ds (none :: c) e2_sub ++ [.pop .r9, .addr .rax .r9]) := by
        simpa [List.append_assoc] using
          (code_at_after_compile_prefix
            (pfx := [.push .rax])
            (mid := compile ds (none :: c) e2_sub ++ [.pop .r9, .addr .rax .r9])
            (sfx := [])
            (by simpa [compile, List.append_assoc] using hcode))
      have h2 : code_at is
          ((pc + compile_len e1_sub + 1) + (compile ds (none :: c) e2_sub).length)
          [.pop .r9, .addr .rax .r9] :=
        code_at_app_right
          (c1 := compile ds (none :: c) e2_sub) (c2 := [.pop .r9, .addr .rax .r9]) h
      have hlen : (compile ds (none :: c) e2_sub).length = compile_len e2_sub :=
        compile_length _ _ _
      rw [hlen] at h2
      exact h2
    have hpop_at_abs :
        instr_at is (pc + compile_len e1_sub + 1 + compile_len e2_sub) (.pop .r9) :=
      code_at_head hpop_addr_abs
    have haddr_at_abs :
        instr_at is (pc + compile_len e1_sub + 1 + compile_len e2_sub + 1) (.addr .rax .r9) :=
      code_at_head (code_at_tail hpop_addr_abs)
    -- ! 2) IH1 → s1.
    rcases ih1 hcode_e1 hrel hfresh with
      ⟨s1, hs1, ⟨hpc1, hstack1, hrepr1, hext1⟩, hfresh1⟩
    have hrax1 : s1.regs.rax = i1_val := Represents.int_inv hrepr1
    -- ! 3) push rax at pc s1.pc → s2.
    let s2 : State :=
      { pc := s1.pc + 1, regs := s1.regs,
        stack := s1.regs.rax :: (stk ++ k),
        zf := s1.zf, heap := s1.heap }
    have hpush' : instr_at is s1.pc (.push .rax) := by
      simpa [hpc1] using hpush_at_abs
    have hstep_push : Step is s1 s2 := by
      have hraw := Step.push (s := s1) hpush'
      have hstack_eq : s1.regs.rax :: s1.stack = s1.regs.rax :: (stk ++ k) := by
        rw [hstack1]
      simpa [s2, Reg.read, hstack_eq] using hraw
    -- ! 4) Set up IH2 inputs.
    have hrel2 : Related (s1.regs.rax :: stk) (none :: c) r' s2.heap := by
      have hheap : s2.heap = s1.heap := by rfl
      rw [hheap]
      exact Related.push (Related.mono hrel hext1)
    have hfresh2 : FreshFrom s2.heap s2.regs.rbx := by
      have hheap : s2.heap = s1.heap := by rfl
      have hrbx : s2.regs.rbx = s1.regs.rbx := by rfl
      rw [hheap, hrbx]
      exact hfresh1
    have hcode_e2 : code_at is s2.pc (compile ds (none :: c) e2_sub) := by
      have hpc2eq : s2.pc = pc + compile_len e1_sub + 1 := by
        show s1.pc + 1 = pc + compile_len e1_sub + 1
        rw [hpc1]
      rw [hpc2eq]
      exact hcode_e2_abs
    -- ! Apply IH2.
    rcases ih2 (pc := s2.pc) (stk := s1.regs.rax :: stk) (k := k)
               (rs := s2.regs) (zf := s2.zf) (h := s2.heap) (c := none :: c)
               hcode_e2 hrel2 hfresh2 with
      ⟨s3, hs3_raw, ⟨hpc3, hstack3, hrepr3, hext3⟩, hfresh3⟩
    have hrax3 : s3.regs.rax = i2_val := Represents.int_inv hrepr3
    -- ! IH2's start state is exactly s2 (after `(_ :: stk) ++ k = _ :: (stk ++ k)`).
    have hstart_eq :
        ({ pc := s2.pc, regs := s2.regs, stack := (s1.regs.rax :: stk) ++ k,
           zf := s2.zf, heap := s2.heap } : State) = s2 := by
      show ({ pc := s2.pc, regs := s2.regs, stack := s1.regs.rax :: (stk ++ k),
              zf := s2.zf, heap := s2.heap } : State) = s2
      rfl
    have hs2_to_s3 : Steps is s2 s3 := hstart_eq ▸ hs3_raw
    -- ! 5) pop .r9 at s3 → s4. The stack top is exactly i1 we pushed earlier.
    have hstack3' : s3.stack = s1.regs.rax :: (stk ++ k) := by
      rw [hstack3]; rfl
    let s4 : State :=
      { pc := s3.pc + 1,
        regs := Reg.write .r9 s1.regs.rax s3.regs,
        stack := stk ++ k,
        zf := s3.zf,
        heap := s3.heap }
    have hpop' : instr_at is s3.pc (.pop .r9) := by
      have hpc3eq : s3.pc = pc + compile_len e1_sub + 1 + compile_len e2_sub := by
        have : s3.pc = s2.pc + compile_len e2_sub := hpc3
        rw [this]
        show s1.pc + 1 + compile_len e2_sub = _
        rw [hpc1]
      rw [hpc3eq]
      exact hpop_at_abs
    have hstep_pop : Step is s3 s4 := by
      have hraw := Step.pop (s := s3) (hd := s1.regs.rax) (tl := stk ++ k) hpop' hstack3'
      exact hraw
    -- ! 6) addr .rax .r9 at s4 → s5.   rax becomes i2 + i1.
    let s5 : State :=
      { s4 with
        pc := s4.pc + 1
        regs := Reg.write .rax (Reg.read .rax s4.regs + Reg.read .r9 s4.regs) s4.regs }
    have haddr' : instr_at is s4.pc (.addr .rax .r9) := by
      have hpc4eq : s4.pc = pc + compile_len e1_sub + 1 + compile_len e2_sub + 1 := by
        show s3.pc + 1 = _
        have hpc3eq : s3.pc = pc + compile_len e1_sub + 1 + compile_len e2_sub := by
          have : s3.pc = s2.pc + compile_len e2_sub := hpc3
          rw [this]
          show s1.pc + 1 + compile_len e2_sub = _
          rw [hpc1]
        rw [hpc3eq]
      rw [hpc4eq]
      exact haddr_at_abs
    have hstep_addr : Step is s4 s5 := Step.addr (s := s4) haddr'
    -- ! 7) Package everything.
    refine ⟨s5, ?_, ?_, ?_⟩
    · -- ? chain: initial →* s1 (IH1), s1 → s2 (push), s2 →* s3 (IH2),
      -- ?         s3 → s4 (pop), s4 → s5 (addr).
      have h_s1_to_s2 : Steps is s1 s2 := Steps.trans Steps.refl hstep_push
      have h_s1_to_s3 : Steps is s1 s3 := Steps.append h_s1_to_s2 hs2_to_s3
      have h_s1_to_s4 : Steps is s1 s4 := Steps.trans h_s1_to_s3 hstep_pop
      have h_s1_to_s5 : Steps is s1 s5 := Steps.trans h_s1_to_s4 hstep_addr
      exact Steps.append hs1 h_s1_to_s5
    · refine ⟨?_, ?_, ?_, ?_⟩
      · -- ? pc bookkeeping: 4 extra instrs beyond compile e1 ++ compile e2  →  +3 from compile_len.
        show s5.pc = pc + compile_len (.plus e1_sub e2_sub)
        have hpc3eq : s3.pc = pc + compile_len e1_sub + 1 + compile_len e2_sub := by
          have : s3.pc = s2.pc + compile_len e2_sub := hpc3
          rw [this]; show s1.pc + 1 + compile_len e2_sub = _; rw [hpc1]
        show s4.pc + 1 = pc + compile_len (.plus e1_sub e2_sub)
        show s3.pc + 1 + 1 = pc + compile_len (.plus e1_sub e2_sub)
        rw [hpc3eq]
        simp [compile_len]
        omega
      · -- ? stack restored to stk ++ k (the pop matches the earlier push).
        show s5.stack = stk ++ k
        rfl
      · -- ? rax = i2 + i1 ; result expected to be `i1 + i2`. Commutativity.
        show Represents (.int (i1_val + i2_val)) s5.regs.rax s5.heap
        have hrax5 : s5.regs.rax = i2_val + i1_val := by
          show (Reg.write .rax (Reg.read .rax s4.regs + Reg.read .r9 s4.regs) s4.regs).rax
                 = i2_val + i1_val
          simp [Reg.write, Reg.read, s4, hrax3, hrax1]
        rw [hrax5, Int.add_comm i1_val i2_val]
        exact Represents.int (i := i2_val + i1_val) (h := s5.heap)
      · -- ? heap unchanged after s3; chain extends.
        have hheap5 : s5.heap = s3.heap := by rfl
        rw [hheap5]
        exact HeapExtends.trans hext1 hext3
    · -- ? FreshFrom: rbx untouched by push/pop/addr; heap untouched by all of them past s3.
      have hheap : s5.heap = s3.heap := by rfl
      have hrbx : s5.regs.rbx = s3.regs.rbx := by
        show (Reg.write .rax _ s4.regs).rbx = s3.regs.rbx
        simp [Reg.write, s4]
      rw [hheap, hrbx]
      exact hfresh3

  | timesr _ _ ih1 ih2 =>
    -- ! `times e1 e2` compiles to:
    -- !     compile e1 ++ [push rax] ++ compile e2 ++ [movr .r9 .rax, pop .rax, imul .r9]
    -- ! Flow:
    -- !   IH1 → rax = i1.   push rax pushes i1.
    -- !   IH2 on extended stack → rax = i2 (stack still has i1 on top).
    -- !   movr .r9 .rax  → r9 = i2.   pop .rax → rax = i1, stack restored.
    -- !   imul .r9       → rax = rax * r9 = i1 * i2.
    rename_i r' e1_sub i1_val e2_sub i2_val _hev1 _hev2
    -- ! 1) Locate sub-pieces.
    have hcode_e1 : code_at is pc (compile ds c e1_sub) :=
      code_at_compile_left
        (tail := [.push .rax] ++ compile ds (none :: c) e2_sub ++
                 [.movr .r9 .rax, .pop .rax, .imul .r9])
        (by simpa [compile, List.append_assoc] using hcode)
    have hpush_at_abs : instr_at is (pc + compile_len e1_sub) (.push .rax) := by
      have hmid : code_at is (pc + compile_len e1_sub) [.push .rax] := by
        simpa using
          (code_at_after_compile_prefix
            (pfx := []) (mid := [.push .rax])
            (sfx := compile ds (none :: c) e2_sub ++
                    [.movr .r9 .rax, .pop .rax, .imul .r9])
            (by simpa [compile, List.append_assoc] using hcode))
      exact code_at_head hmid
    have hcode_e2_abs :
        code_at is (pc + compile_len e1_sub + 1) (compile ds (none :: c) e2_sub) := by
      simpa using
        (code_at_after_compile_prefix
          (pfx := [.push .rax]) (mid := compile ds (none :: c) e2_sub)
          (sfx := [.movr .r9 .rax, .pop .rax, .imul .r9])
          (by simpa [compile, List.append_assoc] using hcode))
    have htail_at :
        code_at is (pc + compile_len e1_sub + 1 + compile_len e2_sub)
          [.movr .r9 .rax, .pop .rax, .imul .r9] := by
      have h : code_at is (pc + compile_len e1_sub + 1)
          (compile ds (none :: c) e2_sub ++ [.movr .r9 .rax, .pop .rax, .imul .r9]) := by
        simpa [List.append_assoc] using
          (code_at_after_compile_prefix
            (pfx := [.push .rax])
            (mid := compile ds (none :: c) e2_sub ++ [.movr .r9 .rax, .pop .rax, .imul .r9])
            (sfx := [])
            (by simpa [compile, List.append_assoc] using hcode))
      have h2 := code_at_app_right
        (c1 := compile ds (none :: c) e2_sub)
        (c2 := [.movr .r9 .rax, .pop .rax, .imul .r9]) h
      have hlen : (compile ds (none :: c) e2_sub).length = compile_len e2_sub :=
        compile_length _ _ _
      rw [hlen] at h2
      exact h2
    have hmovr_at_abs :
        instr_at is (pc + compile_len e1_sub + 1 + compile_len e2_sub) (.movr .r9 .rax) :=
      code_at_head htail_at
    have hpop_at_abs :
        instr_at is (pc + compile_len e1_sub + 1 + compile_len e2_sub + 1) (.pop .rax) :=
      code_at_head (code_at_tail htail_at)
    have himul_at_abs :
        instr_at is (pc + compile_len e1_sub + 1 + compile_len e2_sub + 1 + 1) (.imul .r9) :=
      code_at_head (code_at_tail (code_at_tail htail_at))
    -- ! 2) IH1 → s1.
    rcases ih1 hcode_e1 hrel hfresh with
      ⟨s1, hs1, ⟨hpc1, hstack1, hrepr1, hext1⟩, hfresh1⟩
    have hrax1 : s1.regs.rax = i1_val := Represents.int_inv hrepr1
    -- ! 3) push rax → s2.
    let s2 : State :=
      { pc := s1.pc + 1, regs := s1.regs,
        stack := s1.regs.rax :: (stk ++ k),
        zf := s1.zf, heap := s1.heap }
    have hpush' : instr_at is s1.pc (.push .rax) := by
      simpa [hpc1] using hpush_at_abs
    have hstep_push : Step is s1 s2 := by
      have hraw := Step.push (s := s1) hpush'
      have hstack_eq : s1.regs.rax :: s1.stack = s1.regs.rax :: (stk ++ k) := by
        rw [hstack1]
      simpa [s2, Reg.read, hstack_eq] using hraw
    -- ! 4) IH2 from s2.
    have hrel2 : Related (s1.regs.rax :: stk) (none :: c) r' s2.heap := by
      have hheap : s2.heap = s1.heap := by rfl
      rw [hheap]
      exact Related.push (Related.mono hrel hext1)
    have hfresh2 : FreshFrom s2.heap s2.regs.rbx := by
      have hheap : s2.heap = s1.heap := by rfl
      have hrbx : s2.regs.rbx = s1.regs.rbx := by rfl
      rw [hheap, hrbx]
      exact hfresh1
    have hcode_e2 : code_at is s2.pc (compile ds (none :: c) e2_sub) := by
      have hpc2eq : s2.pc = pc + compile_len e1_sub + 1 := by
        show s1.pc + 1 = pc + compile_len e1_sub + 1
        rw [hpc1]
      rw [hpc2eq]
      exact hcode_e2_abs
    rcases ih2 (pc := s2.pc) (stk := s1.regs.rax :: stk) (k := k)
               (rs := s2.regs) (zf := s2.zf) (h := s2.heap) (c := none :: c)
               hcode_e2 hrel2 hfresh2 with
      ⟨s3, hs3_raw, ⟨hpc3, hstack3, hrepr3, hext3⟩, hfresh3⟩
    have hrax3 : s3.regs.rax = i2_val := Represents.int_inv hrepr3
    have hstart_eq :
        ({ pc := s2.pc, regs := s2.regs, stack := (s1.regs.rax :: stk) ++ k,
           zf := s2.zf, heap := s2.heap } : State) = s2 := by
      show ({ pc := s2.pc, regs := s2.regs, stack := s1.regs.rax :: (stk ++ k),
              zf := s2.zf, heap := s2.heap } : State) = s2
      rfl
    have hs2_to_s3 : Steps is s2 s3 := hstart_eq ▸ hs3_raw
    -- ! 5) movr .r9 .rax at s3 → s4. r9 takes the current i2 in rax.
    have hpc3eq : s3.pc = pc + compile_len e1_sub + 1 + compile_len e2_sub := by
      have : s3.pc = s2.pc + compile_len e2_sub := hpc3
      rw [this]; show s1.pc + 1 + compile_len e2_sub = _; rw [hpc1]
    let s4 : State :=
      { s3 with
        pc := s3.pc + 1
        regs := Reg.write .r9 (Reg.read .rax s3.regs) s3.regs }
    have hmovr' : instr_at is s3.pc (.movr .r9 .rax) := by
      rw [hpc3eq]; exact hmovr_at_abs
    have hstep_movr : Step is s3 s4 := Step.movr (s := s3) hmovr'
    -- ! 6) pop .rax at s4 → s5. The stack top is i1 (pushed earlier).
    have hstack4 : s4.stack = s1.regs.rax :: (stk ++ k) := by
      show s3.stack = s1.regs.rax :: (stk ++ k)
      rw [hstack3]; rfl
    let s5 : State :=
      { pc := s4.pc + 1,
        regs := Reg.write .rax s1.regs.rax s4.regs,
        stack := stk ++ k,
        zf := s4.zf,
        heap := s4.heap }
    have hpop' : instr_at is s4.pc (.pop .rax) := by
      show instr_at is (s3.pc + 1) (.pop .rax)
      rw [hpc3eq]; exact hpop_at_abs
    have hstep_pop : Step is s4 s5 :=
      Step.pop (s := s4) (hd := s1.regs.rax) (tl := stk ++ k) hpop' hstack4
    -- ! 7) imul .r9 at s5 → s6. rax becomes rax * r9 = i1 * i2.
    let s6 : State :=
      { s5 with
        pc := s5.pc + 1
        regs := { s5.regs with rax := s5.regs.rax * (Reg.read .r9 s5.regs) } }
    have himul' : instr_at is s5.pc (.imul .r9) := by
      show instr_at is (s4.pc + 1) (.imul .r9)
      show instr_at is (s3.pc + 1 + 1) (.imul .r9)
      rw [hpc3eq]; exact himul_at_abs
    have hstep_imul : Step is s5 s6 := Step.imul (s := s5) himul'
    -- ! 8) Package everything.
    refine ⟨s6, ?_, ?_, ?_⟩
    · have h_s1_to_s2 : Steps is s1 s2 := Steps.trans Steps.refl hstep_push
      have h_s1_to_s3 : Steps is s1 s3 := Steps.append h_s1_to_s2 hs2_to_s3
      have h_s1_to_s4 : Steps is s1 s4 := Steps.trans h_s1_to_s3 hstep_movr
      have h_s1_to_s5 : Steps is s1 s5 := Steps.trans h_s1_to_s4 hstep_pop
      have h_s1_to_s6 : Steps is s1 s6 := Steps.trans h_s1_to_s5 hstep_imul
      exact Steps.append hs1 h_s1_to_s6
    · refine ⟨?_, ?_, ?_, ?_⟩
      · -- ? pc = pc + compile_len e1 + 1 + compile_len e2 + 1 + 1 + 1 = pc + (e1 + e2 + 4).
        show s6.pc = pc + compile_len (.times e1_sub e2_sub)
        show s5.pc + 1 = pc + compile_len (.times e1_sub e2_sub)
        show s4.pc + 1 + 1 = pc + compile_len (.times e1_sub e2_sub)
        show s3.pc + 1 + 1 + 1 = pc + compile_len (.times e1_sub e2_sub)
        rw [hpc3eq]
        simp [compile_len]
        omega
      · -- ? stack restored.
        show s6.stack = stk ++ k
        rfl
      · -- ? rax = i1 * i2.
        show Represents (.int (i1_val * i2_val)) s6.regs.rax s6.heap
        have hrax6 : s6.regs.rax = i1_val * i2_val := by
          show (({ s5.regs with rax := s5.regs.rax * (Reg.read .r9 s5.regs) }).rax) = _
          -- s5.regs.rax = s1.regs.rax = i1_val (just popped).
          -- s5.regs.r9 = s4.regs.r9 = s3.regs.rax = i2_val (set by movr).
          simp [Reg.write, Reg.read, s5, s4, hrax1, hrax3]
        rw [hrax6]
        exact Represents.int (i := i1_val * i2_val) (h := s6.heap)
      · -- ? heap unchanged after IH2.
        have hheap6 : s6.heap = s3.heap := by rfl
        rw [hheap6]
        exact HeapExtends.trans hext1 hext3
    · -- ? FreshFrom unchanged: only rax, r9 touched by movr/pop/imul; heap untouched after s3.
      have hheap : s6.heap = s3.heap := by rfl
      have hrbx : s6.regs.rbx = s3.regs.rbx := by
        show ({ s5.regs with rax := _ } : Regs).rbx = s3.regs.rbx
        simp [s5, s4, Reg.write]
      rw [hheap, hrbx]
      exact hfresh3

  | iftr _ _ ih1 ih2 =>
    -- ! `ifte e1 e2 e3` compiles e1, then branches. The `iftr` case took the
    -- ! `then` branch, so e1 evaluated to `true` (= 1). After `cmp rax r9`
    -- ! (with r9 = 0), zf = false, so `bnz (L3 + 2)` jumps past compile e3
    -- ! and the trailing `jmp`, landing at compile e2. Apply IH2 there.
    rename_i r' e1_sub e2_sub v_val e3_sub _hev1 _hev2
    -- ! 1) Locate sub-pieces. Layout:
    -- !    compile e1 ++ [movi r9 0, cmp, bnz (L3+2)] ++ compile e3 ++
    -- !    [jmp (L2+1)] ++ compile e2
    have hcode_e1 : code_at is pc (compile ds c e1_sub) :=
      code_at_compile_left
        (tail := [.movi .r9 0, .cmp .rax .r9,
                  .bnz ((compile ds c e3_sub).length + 2 : Nat)] ++
                 compile ds c e3_sub ++
                 [.jmp ((compile ds c e2_sub).length + 1 : Nat)] ++
                 compile ds c e2_sub)
        (by simpa [compile, List.append_assoc] using hcode)
    have hmovi_at_abs : instr_at is (pc + compile_len e1_sub) (.movi .r9 0) := by
      have hmid : code_at is (pc + compile_len e1_sub) [.movi .r9 0] := by
        simpa using
          (code_at_after_compile_prefix
            (pfx := []) (mid := [.movi .r9 0])
            (sfx := [.cmp .rax .r9, .bnz ((compile ds c e3_sub).length + 2 : Nat)] ++
                    compile ds c e3_sub ++
                    [.jmp ((compile ds c e2_sub).length + 1 : Nat)] ++
                    compile ds c e2_sub)
            (by simpa [compile, List.append_assoc] using hcode))
      exact code_at_head hmid
    have hcmp_at_abs : instr_at is (pc + compile_len e1_sub + 1) (.cmp .rax .r9) := by
      have hmid : code_at is (pc + compile_len e1_sub + 1) [.cmp .rax .r9] := by
        simpa using
          (code_at_after_compile_prefix
            (pfx := [.movi .r9 0]) (mid := [.cmp .rax .r9])
            (sfx := [.bnz ((compile ds c e3_sub).length + 2 : Nat)] ++
                    compile ds c e3_sub ++
                    [.jmp ((compile ds c e2_sub).length + 1 : Nat)] ++
                    compile ds c e2_sub)
            (by simpa [compile, List.append_assoc] using hcode))
      exact code_at_head hmid
    have hbnz_at_abs :
        instr_at is (pc + compile_len e1_sub + 2)
          (.bnz ((compile ds c e3_sub).length + 2 : Nat)) := by
      have hmid : code_at is (pc + compile_len e1_sub + 2)
          [.bnz ((compile ds c e3_sub).length + 2 : Nat)] := by
        simpa using
          (code_at_after_compile_prefix
            (pfx := [.movi .r9 0, .cmp .rax .r9])
            (mid := [.bnz ((compile ds c e3_sub).length + 2 : Nat)])
            (sfx := compile ds c e3_sub ++
                    [.jmp ((compile ds c e2_sub).length + 1 : Nat)] ++
                    compile ds c e2_sub)
            (by simpa [compile, List.append_assoc] using hcode))
      exact code_at_head hmid
    have hL3eq : (compile ds c e3_sub).length = compile_len e3_sub := compile_length _ _ _
    have hL2eq : (compile ds c e2_sub).length = compile_len e2_sub := compile_length _ _ _
    -- ! compile e2 sits after compile e1 ++ [3 trivial] ++ compile e3 ++ [jmp].
    have hcode_e2_abs :
        code_at is (pc + compile_len e1_sub + compile_len e3_sub + 4)
          (compile ds c e2_sub) := by
      have h := code_at_after_compile_prefix
        (pfx := [.movi .r9 0, .cmp .rax .r9,
                 .bnz ((compile ds c e3_sub).length + 2 : Nat)] ++
                compile ds c e3_sub ++
                [.jmp ((compile ds c e2_sub).length + 1 : Nat)])
        (mid := compile ds c e2_sub)
        (sfx := [])
        (by simpa [compile, List.append_assoc] using hcode)
      have hpfx_len :
          (([.movi .r9 0, .cmp .rax .r9,
            .bnz ((compile ds c e3_sub).length + 2 : Nat)] : List Instr) ++
           compile ds c e3_sub ++
           ([.jmp ((compile ds c e2_sub).length + 1 : Nat)] : List Instr)).length
          = compile_len e3_sub + 4 := by
        simp [List.length_append, hL3eq]
      rw [hpfx_len] at h
      have heq : pc + compile_len e1_sub + (compile_len e3_sub + 4)
               = pc + compile_len e1_sub + compile_len e3_sub + 4 := by omega
      rw [heq] at h
      exact h
    -- ! 2) IH1 → s1, rax = 1 (true)
    rcases ih1 hcode_e1 hrel hfresh with
      ⟨s1, hs1, ⟨hpc1, hstack1, hrepr1, hext1⟩, hfresh1⟩
    have hrax1 : s1.regs.rax = 1 := by
      have h := Represents.bool_inv hrepr1
      simpa using h
    -- ! 3) movi r9 0 at s1 → s2
    let s2 : State :=
      { s1 with
        pc := s1.pc + 1
        regs := Reg.write .r9 0 s1.regs }
    have hmovi' : instr_at is s1.pc (.movi .r9 0) := by simpa [hpc1] using hmovi_at_abs
    have hstep_movi : Step is s1 s2 := Step.movi (s := s1) hmovi'
    -- ! 4) cmp rax r9 at s2 → s3. After this, zf = (rax == r9) = (1 == 0) = false.
    let s3 : State :=
      { s2 with
        pc := s2.pc + 1
        zf := (Reg.read .rax s2.regs == Reg.read .r9 s2.regs) }
    have hcmp' : instr_at is s2.pc (.cmp .rax .r9) := by
      show instr_at is (s1.pc + 1) (.cmp .rax .r9)
      have hh : (s1.pc + 1 : Nat) = pc + compile_len e1_sub + 1 := by rw [hpc1]
      rw [hh]; exact hcmp_at_abs
    have hstep_cmp : Step is s2 s3 := Step.cmp (s := s2) hcmp'
    have hzf3 : s3.zf = false := by
      show (Reg.read .rax s2.regs == Reg.read .r9 s2.regs) = false
      have hr9 : Reg.read .r9 s2.regs = 0 := by
        show (Reg.write .r9 0 s1.regs).r9 = 0
        simp [Reg.write]
      have hax : Reg.read .rax s2.regs = 1 := by
        show (Reg.write .r9 0 s1.regs).rax = 1
        show s1.regs.rax = 1
        exact hrax1
      rw [hax, hr9]; decide
    -- ! 5) bnz (L3 + 2) at s3 → s4. zf = false, so bnzt jumps to pc + L1 + L3 + 4.
    let s4 : State :=
      { s3 with
        pc := (Int.ofNat s3.pc +
               ((compile ds c e3_sub).length + 2 : Nat)).toNat }
    have hbnz' : instr_at is s3.pc
        (.bnz ((compile ds c e3_sub).length + 2 : Nat)) := by
      show instr_at is (s2.pc + 1) _
      show instr_at is (s1.pc + 1 + 1) _
      have hh : (s1.pc + 1 + 1 : Nat) = pc + compile_len e1_sub + 2 := by rw [hpc1]
      rw [hh]; exact hbnz_at_abs
    have hstep_bnz : Step is s3 s4 := Step.bnzt (s := s3) hbnz' hzf3
    -- ! Compute s4.pc.
    have hpc3eq : s3.pc = pc + compile_len e1_sub + 2 := by
      show s2.pc + 1 = _
      show s1.pc + 1 + 1 = _
      rw [hpc1]
    have hpc4 : s4.pc = pc + compile_len e1_sub + compile_len e3_sub + 4 := by
      show (Int.ofNat s3.pc +
            ((compile ds c e3_sub).length + 2 : Nat)).toNat = _
      rw [hpc3eq, hL3eq]
      -- (Int.ofNat (pc + L1 + 2) + Int.ofNat (L3 + 2)).toNat
      -- reduces by defeq to (pc + L1 + 2) + (L3 + 2)
      show pc + compile_len e1_sub + 2 + (compile_len e3_sub + 2)
         = pc + compile_len e1_sub + compile_len e3_sub + 4
      omega
    -- ! 6) IH2 from s4: compile e2 lives at s4.pc.
    have hcode_e2_at_s4 : code_at is s4.pc (compile ds c e2_sub) := by
      rw [hpc4]; exact hcode_e2_abs
    have hheap_s4 : s4.heap = s1.heap := by
      show s3.heap = s1.heap; show s2.heap = s1.heap; rfl
    have hrel4 : Related stk c r' s4.heap := by
      rw [hheap_s4]; exact Related.mono hrel hext1
    have hrbx_s4 : s4.regs.rbx = s1.regs.rbx := by
      show s3.regs.rbx = s1.regs.rbx
      show s2.regs.rbx = s1.regs.rbx
      show (Reg.write .r9 0 s1.regs).rbx = s1.regs.rbx
      simp [Reg.write]
    have hfresh4 : FreshFrom s4.heap s4.regs.rbx := by
      rw [hheap_s4, hrbx_s4]; exact hfresh1
    rcases ih2 (pc := s4.pc) (stk := stk) (k := k)
               (rs := s4.regs) (zf := s4.zf) (h := s4.heap) (c := c)
               hcode_e2_at_s4 hrel4 hfresh4 with
      ⟨s5, hs5_raw, ⟨hpc5, hstack5, hrepr5, hext5⟩, hfresh5⟩
    -- ! Bridge: IH2's start state vs our s4. Stack must match.
    have hstack_s4 : s4.stack = stk ++ k := by
      show s3.stack = stk ++ k
      show s2.stack = stk ++ k
      show s1.stack = stk ++ k
      exact hstack1
    have hstart_eq :
        ({ pc := s4.pc, regs := s4.regs, stack := stk ++ k,
           zf := s4.zf, heap := s4.heap } : State) = s4 := by
      rw [← hstack_s4]
    have hs4_to_s5 : Steps is s4 s5 := hstart_eq ▸ hs5_raw
    refine ⟨s5, ?_, ?_, ?_⟩
    · -- ! Chain: initial →* s1 (IH1), s1 → s2 → s3 → s4 (trivial steps), s4 →* s5 (IH2).
      have h_s1_to_s2 : Steps is s1 s2 := Steps.trans Steps.refl hstep_movi
      have h_s1_to_s3 : Steps is s1 s3 := Steps.trans h_s1_to_s2 hstep_cmp
      have h_s1_to_s4 : Steps is s1 s4 := Steps.trans h_s1_to_s3 hstep_bnz
      have h_s1_to_s5 : Steps is s1 s5 := Steps.append h_s1_to_s4 hs4_to_s5
      exact Steps.append hs1 h_s1_to_s5
    · refine ⟨?_, ?_, ?_, ?_⟩
      · -- ! Final pc: s5.pc = s4.pc + L2 = pc + L1 + L3 + 4 + L2 = pc + compile_len.
        show s5.pc = pc + compile_len (.ifte e1_sub e2_sub e3_sub)
        rw [hpc5, hpc4]
        simp [compile_len]; omega
      · -- ! stack: IH2 promises s5.stack = stk ++ k.
        exact hstack5
      · -- ! rax represents v_val (output of IH2).
        exact hrepr5
      · -- ! Heap chain: hext1 ∘ hext5 (no intermediate stores).
        have hheap_s5_extends_s4 : HeapExtends s4.heap s5.heap := hext5
        rw [hheap_s4] at hheap_s5_extends_s4
        exact HeapExtends.trans hext1 hheap_s5_extends_s4
    · -- ! FreshFrom: directly from hfresh5 (IH2 preserves it).
      exact hfresh5

  | iffr _ _ ih1 ih2 =>
    -- ! Mirror of `iftr`: e1 → false (= 0), so zf = (0 == 0) = true after `cmp`.
    -- ! `bnz (L3+2)` falls through (bnzf), running compile e3, then `jmp (L2+1)`
    -- ! skips over compile e2 to the end.
    rename_i r' e1_sub e3_sub v_val e2_sub _hev1 _hev2
    -- ! Locate sub-pieces (same layout as iftr).
    have hcode_e1 : code_at is pc (compile ds c e1_sub) :=
      code_at_compile_left
        (tail := [.movi .r9 0, .cmp .rax .r9,
                  .bnz ((compile ds c e3_sub).length + 2 : Nat)] ++
                 compile ds c e3_sub ++
                 [.jmp ((compile ds c e2_sub).length + 1 : Nat)] ++
                 compile ds c e2_sub)
        (by simpa [compile, List.append_assoc] using hcode)
    have hmovi_at_abs : instr_at is (pc + compile_len e1_sub) (.movi .r9 0) := by
      have hmid : code_at is (pc + compile_len e1_sub) [.movi .r9 0] := by
        simpa using
          (code_at_after_compile_prefix
            (pfx := []) (mid := [.movi .r9 0])
            (sfx := [.cmp .rax .r9, .bnz ((compile ds c e3_sub).length + 2 : Nat)] ++
                    compile ds c e3_sub ++
                    [.jmp ((compile ds c e2_sub).length + 1 : Nat)] ++
                    compile ds c e2_sub)
            (by simpa [compile, List.append_assoc] using hcode))
      exact code_at_head hmid
    have hcmp_at_abs : instr_at is (pc + compile_len e1_sub + 1) (.cmp .rax .r9) := by
      have hmid : code_at is (pc + compile_len e1_sub + 1) [.cmp .rax .r9] := by
        simpa using
          (code_at_after_compile_prefix
            (pfx := [.movi .r9 0]) (mid := [.cmp .rax .r9])
            (sfx := [.bnz ((compile ds c e3_sub).length + 2 : Nat)] ++
                    compile ds c e3_sub ++
                    [.jmp ((compile ds c e2_sub).length + 1 : Nat)] ++
                    compile ds c e2_sub)
            (by simpa [compile, List.append_assoc] using hcode))
      exact code_at_head hmid
    have hbnz_at_abs :
        instr_at is (pc + compile_len e1_sub + 2)
          (.bnz ((compile ds c e3_sub).length + 2 : Nat)) := by
      have hmid : code_at is (pc + compile_len e1_sub + 2)
          [.bnz ((compile ds c e3_sub).length + 2 : Nat)] := by
        simpa using
          (code_at_after_compile_prefix
            (pfx := [.movi .r9 0, .cmp .rax .r9])
            (mid := [.bnz ((compile ds c e3_sub).length + 2 : Nat)])
            (sfx := compile ds c e3_sub ++
                    [.jmp ((compile ds c e2_sub).length + 1 : Nat)] ++
                    compile ds c e2_sub)
            (by simpa [compile, List.append_assoc] using hcode))
      exact code_at_head hmid
    have hL3eq : (compile ds c e3_sub).length = compile_len e3_sub := compile_length _ _ _
    have hL2eq : (compile ds c e2_sub).length = compile_len e2_sub := compile_length _ _ _
    -- ! compile e3 starts at pc + L1 + 3.
    have hcode_e3_abs :
        code_at is (pc + compile_len e1_sub + 3) (compile ds c e3_sub) := by
      have h := code_at_after_compile_prefix
        (pfx := [.movi .r9 0, .cmp .rax .r9,
                 .bnz ((compile ds c e3_sub).length + 2 : Nat)])
        (mid := compile ds c e3_sub)
        (sfx := [.jmp ((compile ds c e2_sub).length + 1 : Nat)] ++
                compile ds c e2_sub)
        (by simpa [compile, List.append_assoc] using hcode)
      simpa using h
    -- ! The trailing `jmp` lives at pc + L1 + 3 + L3.
    have hjmp_at_abs :
        instr_at is (pc + compile_len e1_sub + 3 + compile_len e3_sub)
          (.jmp ((compile ds c e2_sub).length + 1 : Nat)) := by
      have hmid : code_at is (pc + compile_len e1_sub + 3 + compile_len e3_sub)
          [.jmp ((compile ds c e2_sub).length + 1 : Nat)] := by
        have h := code_at_after_compile_prefix
          (pfx := [.movi .r9 0, .cmp .rax .r9,
                   .bnz ((compile ds c e3_sub).length + 2 : Nat)] ++
                  compile ds c e3_sub)
          (mid := [.jmp ((compile ds c e2_sub).length + 1 : Nat)])
          (sfx := compile ds c e2_sub)
          (by simpa [compile, List.append_assoc] using hcode)
        have hpfx_len :
            (([.movi .r9 0, .cmp .rax .r9,
              .bnz ((compile ds c e3_sub).length + 2 : Nat)] : List Instr) ++
             compile ds c e3_sub).length
            = compile_len e3_sub + 3 := by
          simp [hL3eq]
        rw [hpfx_len] at h
        have heq : pc + compile_len e1_sub + (compile_len e3_sub + 3)
                 = pc + compile_len e1_sub + 3 + compile_len e3_sub := by omega
        rw [heq] at h
        exact h
      exact code_at_head hmid
    -- ! 2) IH1 → s1, rax = 0 (false)
    rcases ih1 hcode_e1 hrel hfresh with
      ⟨s1, hs1, ⟨hpc1, hstack1, hrepr1, hext1⟩, hfresh1⟩
    have hrax1 : s1.regs.rax = 0 := by
      have h := Represents.bool_inv hrepr1
      simpa using h
    -- ! 3) movi r9 0 at s1 → s2
    let s2 : State :=
      { s1 with
        pc := s1.pc + 1
        regs := Reg.write .r9 0 s1.regs }
    have hmovi' : instr_at is s1.pc (.movi .r9 0) := by simpa [hpc1] using hmovi_at_abs
    have hstep_movi : Step is s1 s2 := Step.movi (s := s1) hmovi'
    -- ! 4) cmp rax r9 at s2 → s3. zf = (0 == 0) = true.
    let s3 : State :=
      { s2 with
        pc := s2.pc + 1
        zf := (Reg.read .rax s2.regs == Reg.read .r9 s2.regs) }
    have hcmp' : instr_at is s2.pc (.cmp .rax .r9) := by
      show instr_at is (s1.pc + 1) (.cmp .rax .r9)
      have hh : (s1.pc + 1 : Nat) = pc + compile_len e1_sub + 1 := by rw [hpc1]
      rw [hh]; exact hcmp_at_abs
    have hstep_cmp : Step is s2 s3 := Step.cmp (s := s2) hcmp'
    have hzf3 : s3.zf = true := by
      show (Reg.read .rax s2.regs == Reg.read .r9 s2.regs) = true
      have hr9 : Reg.read .r9 s2.regs = 0 := by
        show (Reg.write .r9 0 s1.regs).r9 = 0
        simp [Reg.write]
      have hax : Reg.read .rax s2.regs = 0 := by
        show (Reg.write .r9 0 s1.regs).rax = 0
        show s1.regs.rax = 0
        exact hrax1
      rw [hax, hr9]; decide
    -- ! 5) bnz (L3 + 2) at s3 → s4. zf = true, so bnzf falls through (pc + 1).
    let s4 : State :=
      { s3 with
        pc := s3.pc + 1 }
    have hbnz' : instr_at is s3.pc
        (.bnz ((compile ds c e3_sub).length + 2 : Nat)) := by
      show instr_at is (s2.pc + 1) _
      show instr_at is (s1.pc + 1 + 1) _
      have hh : (s1.pc + 1 + 1 : Nat) = pc + compile_len e1_sub + 2 := by rw [hpc1]
      rw [hh]; exact hbnz_at_abs
    have hstep_bnz : Step is s3 s4 := Step.bnzf (s := s3) hbnz' hzf3
    -- ! Compute s4.pc = pc + L1 + 3.
    have hpc3eq : s3.pc = pc + compile_len e1_sub + 2 := by
      show s2.pc + 1 = _
      show s1.pc + 1 + 1 = _
      rw [hpc1]
    have hpc4 : s4.pc = pc + compile_len e1_sub + 3 := by
      show s3.pc + 1 = _
      rw [hpc3eq]
    -- ! 6) IH2 (which is on e3 for iffr, since the second Eval premise is on e3) → s5.
    have hheap_s4 : s4.heap = s1.heap := by
      show s3.heap = s1.heap; show s2.heap = s1.heap; rfl
    have hrbx_s4 : s4.regs.rbx = s1.regs.rbx := by
      show s3.regs.rbx = s1.regs.rbx
      show s2.regs.rbx = s1.regs.rbx
      show (Reg.write .r9 0 s1.regs).rbx = s1.regs.rbx
      simp [Reg.write]
    have hcode_e3_at_s4 : code_at is s4.pc (compile ds c e3_sub) := by
      rw [hpc4]; exact hcode_e3_abs
    have hrel4 : Related stk c r' s4.heap := by
      rw [hheap_s4]; exact Related.mono hrel hext1
    have hfresh4 : FreshFrom s4.heap s4.regs.rbx := by
      rw [hheap_s4, hrbx_s4]; exact hfresh1
    rcases ih2 (pc := s4.pc) (stk := stk) (k := k)
               (rs := s4.regs) (zf := s4.zf) (h := s4.heap) (c := c)
               hcode_e3_at_s4 hrel4 hfresh4 with
      ⟨s5, hs5_raw, ⟨hpc5, hstack5, hrepr5, hext5⟩, hfresh5⟩
    have hstack_s4 : s4.stack = stk ++ k := by
      show s3.stack = stk ++ k
      show s2.stack = stk ++ k
      show s1.stack = stk ++ k
      exact hstack1
    have hstart_eq :
        ({ pc := s4.pc, regs := s4.regs, stack := stk ++ k,
           zf := s4.zf, heap := s4.heap } : State) = s4 := by
      rw [← hstack_s4]
    have hs4_to_s5 : Steps is s4 s5 := hstart_eq ▸ hs5_raw
    -- ! 7) jmp (L2 + 1) at s5 → s6.
    let s6 : State :=
      { s5 with
        pc := (Int.ofNat s5.pc +
               ((compile ds c e2_sub).length + 1 : Nat)).toNat }
    have hpc5eq : s5.pc = pc + compile_len e1_sub + 3 + compile_len e3_sub := by
      have h : s5.pc = s4.pc + compile_len e3_sub := hpc5
      rw [h, hpc4]
    have hjmp' : instr_at is s5.pc
        (.jmp ((compile ds c e2_sub).length + 1 : Nat)) := by
      rw [hpc5eq]; exact hjmp_at_abs
    have hstep_jmp : Step is s5 s6 := Step.jmp (s := s5) hjmp'
    -- ! Compute s6.pc = pc + L1 + L2 + L3 + 4.
    have hpc6 : s6.pc = pc + compile_len e1_sub + compile_len e2_sub + compile_len e3_sub + 4 := by
      show (Int.ofNat s5.pc +
            ((compile ds c e2_sub).length + 1 : Nat)).toNat = _
      rw [hpc5eq, hL2eq]
      show pc + compile_len e1_sub + 3 + compile_len e3_sub + (compile_len e2_sub + 1)
         = pc + compile_len e1_sub + compile_len e2_sub + compile_len e3_sub + 4
      omega
    refine ⟨s6, ?_, ?_, ?_⟩
    · -- ! Chain: initial →* s1, s1 → s2 → s3 → s4 (trivial), s4 →* s5 (IH2), s5 → s6 (jmp).
      have h_s1_to_s2 : Steps is s1 s2 := Steps.trans Steps.refl hstep_movi
      have h_s1_to_s3 : Steps is s1 s3 := Steps.trans h_s1_to_s2 hstep_cmp
      have h_s1_to_s4 : Steps is s1 s4 := Steps.trans h_s1_to_s3 hstep_bnz
      have h_s1_to_s5 : Steps is s1 s5 := Steps.append h_s1_to_s4 hs4_to_s5
      have h_s1_to_s6 : Steps is s1 s6 := Steps.trans h_s1_to_s5 hstep_jmp
      exact Steps.append hs1 h_s1_to_s6
    · refine ⟨?_, ?_, ?_, ?_⟩
      · -- ! Final pc: s6.pc = pc + compile_len(.ifte e1 e2 e3).
        show s6.pc = pc + compile_len (.ifte e1_sub e2_sub e3_sub)
        rw [hpc6]
        simp [compile_len]; omega
      · -- ! Stack: s6.stack = s5.stack = stk ++ k (by IH2).
        show s6.stack = stk ++ k
        show s5.stack = stk ++ k
        exact hstack5
      · -- ! rax: IH2 gave Represents v_val s5.regs.rax s5.heap; s6 doesn't touch rax/heap.
        show Represents v_val s6.regs.rax s6.heap
        show Represents v_val s5.regs.rax s5.heap
        exact hrepr5
      · -- ! Heap chain.
        show HeapExtends h s6.heap
        have hheap_s6 : s6.heap = s5.heap := by rfl
        rw [hheap_s6]
        have : HeapExtends s4.heap s5.heap := hext5
        rw [hheap_s4] at this
        exact HeapExtends.trans hext1 this
    · -- ! FreshFrom: s6 doesn't touch rbx or heap relative to s5.
      show FreshFrom s6.heap s6.regs.rbx
      have hheap_s6 : s6.heap = s5.heap := by rfl
      have hrbx_s6 : s6.regs.rbx = s5.regs.rbx := by rfl
      rw [hheap_s6, hrbx_s6]
      exact hfresh5

  | negtr _ ih =>
    -- ! `neg e` compiles to `compile e ++ [movi r9 1, xor rax r9]`.
    -- ! When `e` evaluates to `true`, rax = 1 after the IH; xor with 1 gives 0 = false.
    rename_i _r_sub e_sub _hev
    have hcode_e : code_at is pc (compile ds c e_sub) :=
      code_at_compile_left
        (tail := [.movi .r9 1, .xor .rax .r9])
        (by simpa [compile] using hcode)
    rcases ih hcode_e hrel hfresh with ⟨s1, hs1, hpost1, hfresh1⟩
    rcases hpost1 with ⟨hpc1, hstack1, hrepr1, hext1⟩
    -- After the IH, rax holds 1 (the encoding of `bool true`).
    have hrax1 : s1.regs.rax = 1 := by
      have h := Represents.bool_inv hrepr1
      simpa using h
    -- Locate the two trailing instructions in `is`.
    have hmovi_at : instr_at is (pc + compile_len e_sub) (.movi .r9 1) := by
      have hmid : code_at is (pc + compile_len e_sub) [.movi .r9 1] :=
        by simpa using
          (code_at_after_compile_prefix
            (pfx := []) (mid := [.movi .r9 1]) (sfx := [.xor .rax .r9])
            (by simpa [compile] using hcode))
      exact code_at_head hmid
    have hxor_at : instr_at is (pc + compile_len e_sub + 1) (.xor .rax .r9) := by
      have hmid : code_at is (pc + compile_len e_sub + 1) [.xor .rax .r9] :=
        by simpa using
          (code_at_after_compile_prefix
            (pfx := [.movi .r9 1]) (mid := [.xor .rax .r9]) (sfx := [])
            (by simpa [compile] using hcode))
      exact code_at_head hmid
    -- Define the two follow-up states.
    let s2 : State :=
      { s1 with
        pc := s1.pc + 1
        regs := Reg.write .r9 1 s1.regs }
    let s3 : State :=
      { s2 with
        pc := s2.pc + 1
        regs := Reg.write .rax
          (Int.xor (Reg.read .rax s2.regs) (Reg.read .r9 s2.regs)) s2.regs }
    refine ⟨s3, ?_, ?_, ?_⟩
    · -- Chain the IH steps with `movi r9 1` and then `xor rax r9`.
      have hmovi' : instr_at is s1.pc (.movi .r9 1) := by
        simpa [hpc1] using hmovi_at
      have hxor' : instr_at is s2.pc (.xor .rax .r9) := by
        show instr_at is (s1.pc + 1) (.xor .rax .r9)
        have heq : s1.pc + 1 = pc + compile_len e_sub + 1 := by rw [hpc1]
        rw [heq]; exact hxor_at
      exact Steps.trans (Steps.trans hs1 (Step.movi (s := s1) hmovi'))
        (Step.xor (s := s2) hxor')
    · refine ⟨?_, ?_, ?_, ?_⟩
      · -- s3.pc = pc + compile_len (.neg e_sub) = pc + compile_len e_sub + 2
        simp [s3, s2, hpc1, compile_len]; omega
      · -- stack unchanged
        simp [s3, s2, hstack1]
      · -- rax = Int.xor 1 1 = 0, which represents `bool false`.
        have hrax3 : s3.regs.rax = 0 := by
          show (Reg.write .rax
                 (Int.xor (Reg.read .rax s2.regs) (Reg.read .r9 s2.regs))
                 s2.regs).rax = 0
          simp [Reg.write, Reg.read, s2, hrax1]
          decide
        show Represents (.bool false) s3.regs.rax s3.heap
        rw [hrax3]
        exact (Represents.bool (b := false) (h := s3.heap))
      · -- heap unchanged
        simp [s3, s2]; exact hext1
    · -- rbx unchanged; heap unchanged.
      have hheap : s3.heap = s1.heap := by simp [s3, s2]
      have hrbx : s3.regs.rbx = s1.regs.rbx := by
        simp [s3, s2, Reg.write]
      rw [hheap, hrbx]; exact hfresh1

  | negfr _ ih =>
    -- ! Mirror of `negtr`: e evaluates to `false` (rax = 0), xor with 1 gives 1 = true.
    rename_i _r_sub e_sub _hev
    have hcode_e : code_at is pc (compile ds c e_sub) :=
      code_at_compile_left
        (tail := [.movi .r9 1, .xor .rax .r9])
        (by simpa [compile] using hcode)
    rcases ih hcode_e hrel hfresh with ⟨s1, hs1, hpost1, hfresh1⟩
    rcases hpost1 with ⟨hpc1, hstack1, hrepr1, hext1⟩
    have hrax1 : s1.regs.rax = 0 := by
      have h := Represents.bool_inv hrepr1
      simpa using h
    have hmovi_at : instr_at is (pc + compile_len e_sub) (.movi .r9 1) := by
      have hmid : code_at is (pc + compile_len e_sub) [.movi .r9 1] :=
        by simpa using
          (code_at_after_compile_prefix
            (pfx := []) (mid := [.movi .r9 1]) (sfx := [.xor .rax .r9])
            (by simpa [compile] using hcode))
      exact code_at_head hmid
    have hxor_at : instr_at is (pc + compile_len e_sub + 1) (.xor .rax .r9) := by
      have hmid : code_at is (pc + compile_len e_sub + 1) [.xor .rax .r9] :=
        by simpa using
          (code_at_after_compile_prefix
            (pfx := [.movi .r9 1]) (mid := [.xor .rax .r9]) (sfx := [])
            (by simpa [compile] using hcode))
      exact code_at_head hmid
    let s2 : State :=
      { s1 with
        pc := s1.pc + 1
        regs := Reg.write .r9 1 s1.regs }
    let s3 : State :=
      { s2 with
        pc := s2.pc + 1
        regs := Reg.write .rax
          (Int.xor (Reg.read .rax s2.regs) (Reg.read .r9 s2.regs)) s2.regs }
    refine ⟨s3, ?_, ?_, ?_⟩
    · have hmovi' : instr_at is s1.pc (.movi .r9 1) := by
        simpa [hpc1] using hmovi_at
      have hxor' : instr_at is s2.pc (.xor .rax .r9) := by
        show instr_at is (s1.pc + 1) (.xor .rax .r9)
        have heq : s1.pc + 1 = pc + compile_len e_sub + 1 := by rw [hpc1]
        rw [heq]; exact hxor_at
      exact Steps.trans (Steps.trans hs1 (Step.movi (s := s1) hmovi'))
        (Step.xor (s := s2) hxor')
    · refine ⟨?_, ?_, ?_, ?_⟩
      · simp [s3, s2, hpc1, compile_len]; omega
      · simp [s3, s2, hstack1]
      · have hrax3 : s3.regs.rax = 1 := by
          show (Reg.write .rax
                 (Int.xor (Reg.read .rax s2.regs) (Reg.read .r9 s2.regs))
                 s2.regs).rax = 1
          simp [Reg.write, Reg.read, s2, hrax1]
          decide
        show Represents (.bool true) s3.regs.rax s3.heap
        rw [hrax3]
        exact (Represents.bool (b := true) (h := s3.heap))
      · simp [s3, s2]; exact hext1
    · have hheap : s3.heap = s1.heap := by simp [s3, s2]
      have hrbx : s3.regs.rbx = s1.regs.rbx := by
        simp [s3, s2, Reg.write]
      rw [hheap, hrbx]; exact hfresh1

  | bindr _ _ ih1 ih2 =>
    -- ! `bind x e1 e2` compiles to:
    -- !     compile e1 ++ [push rax] ++ compile (some x :: c) e2 ++ [pop r9]
    -- ! Run IH1, push the value onto the stack, extend `Related` with `Related.bind`
    -- ! (which both bumps the CEnv with `some x` and extends the env with `(x, v1)`),
    -- ! run IH2 on the extended state, then the final `pop r9` restores the stack
    -- ! and leaves rax (the e2 result) untouched.
    rename_i r' e1_sub v1_val x_var _v_inner e2_sub _hev1 _hev2
    -- ! 1) Locate the sub-pieces.
    have hcode_e1 : code_at is pc (compile ds c e1_sub) :=
      code_at_compile_left
        (tail := [.push .rax] ++ compile ds (some x_var :: c) e2_sub ++ [.pop .r9])
        (by simpa [compile, List.append_assoc] using hcode)
    have hpush_at_abs : instr_at is (pc + compile_len e1_sub) (.push .rax) := by
      have hmid : code_at is (pc + compile_len e1_sub) [.push .rax] := by
        simpa using
          (code_at_after_compile_prefix
            (pfx := []) (mid := [.push .rax])
            (sfx := compile ds (some x_var :: c) e2_sub ++ [.pop .r9])
            (by simpa [compile, List.append_assoc] using hcode))
      exact code_at_head hmid
    have hcode_e2_abs :
        code_at is (pc + compile_len e1_sub + 1) (compile ds (some x_var :: c) e2_sub) := by
      simpa using
        (code_at_after_compile_prefix
          (pfx := [.push .rax]) (mid := compile ds (some x_var :: c) e2_sub)
          (sfx := [.pop .r9])
          (by simpa [compile, List.append_assoc] using hcode))
    have hpop_at_abs :
        instr_at is (pc + compile_len e1_sub + 1 + compile_len e2_sub) (.pop .r9) := by
      have hmid : code_at is (pc + compile_len e1_sub + 1 + compile_len e2_sub) [.pop .r9] := by
        have h : code_at is (pc + compile_len e1_sub + 1)
            (compile ds (some x_var :: c) e2_sub ++ [.pop .r9]) := by
          simpa [List.append_assoc] using
            (code_at_after_compile_prefix
              (pfx := [.push .rax])
              (mid := compile ds (some x_var :: c) e2_sub ++ [.pop .r9])
              (sfx := [])
              (by simpa [compile, List.append_assoc] using hcode))
        have h2 := code_at_app_right
          (c1 := compile ds (some x_var :: c) e2_sub)
          (c2 := [.pop .r9]) h
        have hlen : (compile ds (some x_var :: c) e2_sub).length = compile_len e2_sub :=
          compile_length _ _ _
        rw [hlen] at h2
        exact h2
      exact code_at_head hmid
    -- ! 2) IH1 → s1.   rax = some encoding of v1_val.
    rcases ih1 hcode_e1 hrel hfresh with
      ⟨s1, hs1, ⟨hpc1, hstack1, hrepr1, hext1⟩, hfresh1⟩
    -- ! 3) push .rax → s2.
    let s2 : State :=
      { pc := s1.pc + 1, regs := s1.regs,
        stack := s1.regs.rax :: (stk ++ k),
        zf := s1.zf, heap := s1.heap }
    have hpush' : instr_at is s1.pc (.push .rax) := by
      simpa [hpc1] using hpush_at_abs
    have hstep_push : Step is s1 s2 := by
      have hraw := Step.push (s := s1) hpush'
      have hstack_eq : s1.regs.rax :: s1.stack = s1.regs.rax :: (stk ++ k) := by
        rw [hstack1]
      simpa [s2, Reg.read, hstack_eq] using hraw
    -- ! 4) IH2 setup: extend stack and Related with the new `(x_var, v1_val)` binding.
    have hrel2 :
        Related (s1.regs.rax :: stk) (some x_var :: c) ((x_var, v1_val) :: r') s2.heap := by
      have hheap : s2.heap = s1.heap := by rfl
      rw [hheap]
      exact Related.bind (Related.mono hrel hext1) hrepr1
    have hfresh2 : FreshFrom s2.heap s2.regs.rbx := by
      have h1 : s2.heap = s1.heap := by rfl
      have h2 : s2.regs.rbx = s1.regs.rbx := by rfl
      rw [h1, h2]; exact hfresh1
    have hcode_e2 : code_at is s2.pc (compile ds (some x_var :: c) e2_sub) := by
      have hpc2eq : s2.pc = pc + compile_len e1_sub + 1 := by
        show s1.pc + 1 = _; rw [hpc1]
      rw [hpc2eq]; exact hcode_e2_abs
    rcases ih2 (pc := s2.pc) (stk := s1.regs.rax :: stk) (k := k)
               (rs := s2.regs) (zf := s2.zf) (h := s2.heap) (c := some x_var :: c)
               hcode_e2 hrel2 hfresh2 with
      ⟨s3, hs3_raw, ⟨hpc3, hstack3, hrepr3, hext3⟩, hfresh3⟩
    have hstart_eq :
        ({ pc := s2.pc, regs := s2.regs, stack := (s1.regs.rax :: stk) ++ k,
           zf := s2.zf, heap := s2.heap } : State) = s2 := by
      show ({ pc := s2.pc, regs := s2.regs, stack := s1.regs.rax :: (stk ++ k),
              zf := s2.zf, heap := s2.heap } : State) = s2
      rfl
    have hs2_to_s3 : Steps is s2 s3 := hstart_eq ▸ hs3_raw
    -- ! 5) pop .r9 at s3 → s4. The stack-top is exactly the i we pushed; rax untouched.
    have hpc3eq : s3.pc = pc + compile_len e1_sub + 1 + compile_len e2_sub := by
      have : s3.pc = s2.pc + compile_len e2_sub := hpc3
      rw [this]; show s1.pc + 1 + compile_len e2_sub = _; rw [hpc1]
    have hstack3' : s3.stack = s1.regs.rax :: (stk ++ k) := by
      rw [hstack3]; rfl
    let s4 : State :=
      { pc := s3.pc + 1,
        regs := Reg.write .r9 s1.regs.rax s3.regs,
        stack := stk ++ k,
        zf := s3.zf,
        heap := s3.heap }
    have hpop' : instr_at is s3.pc (.pop .r9) := by
      rw [hpc3eq]; exact hpop_at_abs
    have hstep_pop : Step is s3 s4 :=
      Step.pop (s := s3) (hd := s1.regs.rax) (tl := stk ++ k) hpop' hstack3'
    -- ! 6) Package everything.
    refine ⟨s4, ?_, ?_, ?_⟩
    · have h_s1_to_s2 : Steps is s1 s2 := Steps.trans Steps.refl hstep_push
      have h_s1_to_s3 : Steps is s1 s3 := Steps.append h_s1_to_s2 hs2_to_s3
      have h_s1_to_s4 : Steps is s1 s4 := Steps.trans h_s1_to_s3 hstep_pop
      exact Steps.append hs1 h_s1_to_s4
    · refine ⟨?_, ?_, ?_, ?_⟩
      · -- ? pc: bind = compile_len e1 + compile_len e2 + 2, we're at +compile_len e1 + 1 + compile_len e2 + 1.
        show s4.pc = pc + compile_len (.bind x_var e1_sub e2_sub)
        show s3.pc + 1 = _
        rw [hpc3eq]; simp [compile_len]; omega
      · -- ? stack restored.
        show s4.stack = stk ++ k
        rfl
      · -- ? rax (e2 result) is preserved by the pop into r9.
        show Represents _ s4.regs.rax s4.heap
        have hrax : s4.regs.rax = s3.regs.rax := by
          show (Reg.write .r9 s1.regs.rax s3.regs).rax = s3.regs.rax
          simp [Reg.write]
        have hheap : s4.heap = s3.heap := by rfl
        rw [hrax, hheap]; exact hrepr3
      · -- ? heap extension is transitive across IH1 and IH2.
        have : s4.heap = s3.heap := by rfl
        rw [this]; exact HeapExtends.trans hext1 hext3
    · -- ? rbx unchanged by push/pop; heap unchanged after IH2.
      have hheap : s4.heap = s3.heap := by rfl
      have hrbx : s4.regs.rbx = s3.regs.rbx := by
        show (Reg.write .r9 _ s3.regs).rbx = s3.regs.rbx
        simp [Reg.write]
      rw [hheap, hrbx]; exact hfresh3

  | callr _hev_arg hlook _hev_body ih1 ih2 =>
    -- ! yunze: full proof of the call case.
    -- ! Layout: compile e_arg ++ [movpc r9, addi r9 5, push r9, push rax, movi r9 entry, jmpabs r9]
    -- ! Function body lives at `entry_nat` via `defns_in_place`, followed by
    -- ! [pop r9, pop r9, jmpabs r9] (discard arg, pop retaddr, return).
    -- ! Trace: IH1 → s1 (rax = i1 ≈ v1). movpc+addi puts retaddr = pc + L + 6 in r9.
    -- ! push r9 / push rax leaves stack = [i1, retaddr] ++ caller. movi+jmpabs lands
    -- ! at entry_nat. IH2 on body → s8 with rax representing v and stack restored.
    -- ! Two pops + jmpabs return to retaddr = pc + compile_len (.call f e_arg).
    rename_i r' e_arg v1_val f' x' e_body v_val

    -- ! 0) `hlook` ⇒ `Defns.entry ds f' = some entry_nat`.
    rcases compile_defns_split hlook with ⟨pre_defs, _post_defs, _hsplit, hentry_eq⟩
    let entry_nat : Nat := pre_defs.length + 1

    -- ! 1) `defns_in_place` gives us the body code at `entry_nat`.
    have hdefn_at : code_at is entry_nat (compile_defn ds (.defn f' x' e_body)) := by
      have h := hdefs hlook
      rw [hentry_eq] at h
      simpa using h
    have hcode_body : code_at is entry_nat (compile ds [some x'] e_body) :=
      code_at_compile_left
        (tail := [.pop .r9, .pop .r9, .jmpabs .r9])
        (by simpa [compile_defn] using hdefn_at)
    have hreturn_at :
        code_at is (entry_nat + compile_len e_body)
          [.pop .r9, .pop .r9, .jmpabs .r9] := by
      simpa using
        (code_at_after_compile_prefix
          (ds := ds) (c := [some x']) (e := e_body) (is := is) (pc := entry_nat)
          (pfx := []) (mid := [.pop .r9, .pop .r9, .jmpabs .r9]) (sfx := [])
          (by simpa [compile_defn] using hdefn_at))
    have hpop1_body_at : instr_at is (entry_nat + compile_len e_body) (.pop .r9) :=
      code_at_head hreturn_at
    have hpop2_body_at : instr_at is (entry_nat + compile_len e_body + 1) (.pop .r9) :=
      code_at_head (code_at_tail hreturn_at)
    have hjmpabs_body_at : instr_at is (entry_nat + compile_len e_body + 2) (.jmpabs .r9) :=
      code_at_head (code_at_tail (code_at_tail hreturn_at))

    -- ! 2) Concretize the call codegen by replacing the inner `match` using `hentry_eq`.
    have hcode' : code_at is pc (
        compile ds c e_arg ++
          [.movpc .r9, .addi .r9 5, .push .r9, .push .rax,
           .movi .r9 (Int.ofNat entry_nat), .jmpabs .r9]) := by
      have h1 : compile ds c (.call f' e_arg) =
          compile ds c e_arg ++
            [.movpc .r9, .addi .r9 5, .push .r9, .push .rax,
             (match Defns.entry ds f' with | none => Instr.halt | some i => .movi .r9 i),
             .jmpabs .r9] := rfl
      rw [h1, hentry_eq] at hcode
      exact hcode

    -- ! 3) Slice the call code into sub-pieces.
    have hcode_e_arg : code_at is pc (compile ds c e_arg) :=
      code_at_compile_left
        (tail := [.movpc .r9, .addi .r9 5, .push .r9, .push .rax,
                  .movi .r9 (Int.ofNat entry_nat), .jmpabs .r9])
        hcode'
    have htail_at : code_at is (pc + compile_len e_arg)
        [.movpc .r9, .addi .r9 5, .push .r9, .push .rax,
         .movi .r9 (Int.ofNat entry_nat), .jmpabs .r9] := by
      simpa using
        (code_at_after_compile_prefix
          (ds := ds) (c := c) (e := e_arg) (is := is) (pc := pc)
          (pfx := [])
          (mid := [.movpc .r9, .addi .r9 5, .push .r9, .push .rax,
                   .movi .r9 (Int.ofNat entry_nat), .jmpabs .r9])
          (sfx := []) (by simpa using hcode'))
    have hmovpc_at_abs : instr_at is (pc + compile_len e_arg) (.movpc .r9) :=
      code_at_head htail_at
    have haddi_at_abs : instr_at is (pc + compile_len e_arg + 1) (.addi .r9 5) :=
      code_at_head (code_at_tail htail_at)
    have hpush_r9_at_abs : instr_at is (pc + compile_len e_arg + 2) (.push .r9) :=
      code_at_head (code_at_tail (code_at_tail htail_at))
    have hpush_rax_at_abs : instr_at is (pc + compile_len e_arg + 3) (.push .rax) :=
      code_at_head (code_at_tail (code_at_tail (code_at_tail htail_at)))
    have hmovi_at_abs : instr_at is (pc + compile_len e_arg + 4) (.movi .r9 (Int.ofNat entry_nat)) :=
      code_at_head (code_at_tail (code_at_tail (code_at_tail (code_at_tail htail_at))))
    have hjmpabs_at_abs : instr_at is (pc + compile_len e_arg + 5) (.jmpabs .r9) :=
      code_at_head (code_at_tail (code_at_tail (code_at_tail (code_at_tail (code_at_tail htail_at)))))

    -- ! 4) IH1 → s1: argument evaluated, rax = i1 represents v1_val.
    rcases ih1 hcode_e_arg hrel hfresh with
      ⟨s1, hs1, ⟨hpc1, hstack1, hrepr1, hext1⟩, hfresh1⟩

    -- ! 5) movpc .r9 at s1 → s2: r9 := s1.pc + 1.
    let s2 : State :=
      { pc := s1.pc + 1
        regs := Reg.write .r9 (Int.ofNat (s1.pc + 1)) s1.regs
        stack := stk ++ k
        zf := s1.zf
        heap := s1.heap }
    have hmovpc' : instr_at is s1.pc (.movpc .r9) := by
      simpa [hpc1] using hmovpc_at_abs
    have hstep_movpc : Step is s1 s2 := by
      have hraw := Step.movpc (s := s1) hmovpc'
      simpa [s2, hstack1] using hraw

    -- ! 6) addi .r9 5 at s2 → s3: r9 := s1.pc + 1 + 5 = s1.pc + 6 (the retaddr).
    let retaddr : Int := Int.ofNat (s1.pc + 1) + 5
    let s3 : State :=
      { pc := s2.pc + 1
        regs := Reg.write .r9 retaddr s2.regs
        stack := stk ++ k
        zf := s2.zf
        heap := s2.heap }
    have haddi' : instr_at is s2.pc (.addi .r9 5) := by
      show instr_at is (s1.pc + 1) (.addi .r9 5)
      have hh : (s1.pc + 1 : Nat) = pc + compile_len e_arg + 1 := by rw [hpc1]
      rw [hh]; exact haddi_at_abs
    have hstep_addi : Step is s2 s3 := by
      have hraw := Step.addi (s := s2) haddi'
      have hr9_s2 : Reg.read .r9 s2.regs = Int.ofNat (s1.pc + 1) := by
        show (Reg.write .r9 (Int.ofNat (s1.pc + 1)) s1.regs).r9 = _
        simp [Reg.write]
      simpa [s3, retaddr, hr9_s2] using hraw

    -- ! 7) push .r9 at s3 → s4: stack := retaddr :: (stk ++ k).
    let s4 : State :=
      { pc := s3.pc + 1
        regs := s3.regs
        stack := retaddr :: (stk ++ k)
        zf := s3.zf
        heap := s3.heap }
    have hpush_r9' : instr_at is s3.pc (.push .r9) := by
      show instr_at is (s2.pc + 1) (.push .r9)
      show instr_at is (s1.pc + 1 + 1) (.push .r9)
      have hh : (s1.pc + 1 + 1 : Nat) = pc + compile_len e_arg + 2 := by rw [hpc1]
      rw [hh]; exact hpush_r9_at_abs
    have hstep_push_r9 : Step is s3 s4 := by
      have hraw := Step.push (s := s3) hpush_r9'
      have hr9_s3 : Reg.read .r9 s3.regs = retaddr := by
        show (Reg.write .r9 retaddr s2.regs).r9 = _
        simp [Reg.write]
      simpa [s4, hr9_s3] using hraw

    -- ! 8) push .rax at s4 → s5: stack := i1 :: retaddr :: (stk ++ k).
    have hrax_s4 : s4.regs.rax = s1.regs.rax := by
      show s3.regs.rax = s1.regs.rax
      show (Reg.write .r9 retaddr s2.regs).rax = s1.regs.rax
      show s2.regs.rax = s1.regs.rax
      show (Reg.write .r9 (Int.ofNat (s1.pc + 1)) s1.regs).rax = s1.regs.rax
      simp [Reg.write]
    let s5 : State :=
      { pc := s4.pc + 1
        regs := s4.regs
        stack := s1.regs.rax :: retaddr :: (stk ++ k)
        zf := s4.zf
        heap := s4.heap }
    have hpush_rax' : instr_at is s4.pc (.push .rax) := by
      show instr_at is (s3.pc + 1) (.push .rax)
      show instr_at is (s2.pc + 1 + 1) (.push .rax)
      show instr_at is (s1.pc + 1 + 1 + 1) (.push .rax)
      have hh : (s1.pc + 1 + 1 + 1 : Nat) = pc + compile_len e_arg + 3 := by rw [hpc1]
      rw [hh]; exact hpush_rax_at_abs
    have hstep_push_rax : Step is s4 s5 := by
      have hraw := Step.push (s := s4) hpush_rax'
      simpa [s5, hrax_s4] using hraw

    -- ! 9) movi .r9 (Int.ofNat entry_nat) at s5 → s6: r9 := entry_nat (as Int).
    let s6 : State :=
      { pc := s5.pc + 1
        regs := Reg.write .r9 (Int.ofNat entry_nat) s5.regs
        stack := s1.regs.rax :: retaddr :: (stk ++ k)
        zf := s5.zf
        heap := s5.heap }
    have hmovi' : instr_at is s5.pc (.movi .r9 (Int.ofNat entry_nat)) := by
      show instr_at is (s4.pc + 1) (.movi .r9 (Int.ofNat entry_nat))
      show instr_at is (s3.pc + 1 + 1) (.movi .r9 (Int.ofNat entry_nat))
      show instr_at is (s2.pc + 1 + 1 + 1) (.movi .r9 (Int.ofNat entry_nat))
      show instr_at is (s1.pc + 1 + 1 + 1 + 1) (.movi .r9 (Int.ofNat entry_nat))
      have hh : (s1.pc + 1 + 1 + 1 + 1 : Nat) = pc + compile_len e_arg + 4 := by rw [hpc1]
      rw [hh]; exact hmovi_at_abs
    have hstep_movi : Step is s5 s6 := by
      have hraw := Step.movi (s := s5) hmovi'
      simpa [s6] using hraw

    -- ! 10) jmpabs .r9 at s6 → s7: pc := entry_nat.
    let s7 : State :=
      { pc := entry_nat
        regs := s6.regs
        stack := s1.regs.rax :: retaddr :: (stk ++ k)
        zf := s6.zf
        heap := s6.heap }
    have hjmpabs' : instr_at is s6.pc (.jmpabs .r9) := by
      show instr_at is (s5.pc + 1) (.jmpabs .r9)
      show instr_at is (s4.pc + 1 + 1) (.jmpabs .r9)
      show instr_at is (s3.pc + 1 + 1 + 1) (.jmpabs .r9)
      show instr_at is (s2.pc + 1 + 1 + 1 + 1) (.jmpabs .r9)
      show instr_at is (s1.pc + 1 + 1 + 1 + 1 + 1) (.jmpabs .r9)
      have hh : (s1.pc + 1 + 1 + 1 + 1 + 1 : Nat) = pc + compile_len e_arg + 5 := by rw [hpc1]
      rw [hh]; exact hjmpabs_at_abs
    have hstep_jmpabs : Step is s6 s7 := by
      have hraw := Step.jmpabs (s := s6) (src := .r9) hjmpabs'
      have hr9_s6 : Reg.read .r9 s6.regs = (Int.ofNat entry_nat : Int) := by
        show (Reg.write .r9 (Int.ofNat entry_nat) s5.regs).r9 = _
        simp [Reg.write]
      have hpc_eq : (Reg.read .r9 s6.regs).toNat = entry_nat := by
        rw [hr9_s6]; rfl
      simpa [s7, hpc_eq] using hraw

    -- ! 11) Set up IH2 at s7. Stack form: [i1] ++ (retaddr :: stk ++ k).
    have hheap_s7 : s7.heap = s1.heap := by
      show s5.heap = s1.heap
      show s4.heap = s1.heap
      show s3.heap = s1.heap
      show s2.heap = s1.heap
      rfl
    have hrbx_s7 : s7.regs.rbx = s1.regs.rbx := by
      show s6.regs.rbx = s1.regs.rbx
      show (Reg.write .r9 (Int.ofNat entry_nat) s5.regs).rbx = s1.regs.rbx
      show s5.regs.rbx = s1.regs.rbx
      show s4.regs.rbx = s1.regs.rbx
      show s3.regs.rbx = s1.regs.rbx
      show (Reg.write .r9 retaddr s2.regs).rbx = s1.regs.rbx
      show s2.regs.rbx = s1.regs.rbx
      show (Reg.write .r9 (Int.ofNat (s1.pc + 1)) s1.regs).rbx = s1.regs.rbx
      simp [Reg.write]
    have hcode_body_at_s7 : code_at is s7.pc (compile ds [some x'] e_body) := by
      show code_at is entry_nat (compile ds [some x'] e_body)
      exact hcode_body
    have hrel_body : Related [s1.regs.rax] [some x'] [(x', v1_val)] s7.heap := by
      rw [hheap_s7]
      exact Related.bind (Related.mt) hrepr1
    have hfresh_s7 : FreshFrom s7.heap s7.regs.rbx := by
      rw [hheap_s7, hrbx_s7]
      exact hfresh1

    -- ! 12) Apply IH2.
    rcases ih2 (pc := s7.pc) (stk := [s1.regs.rax]) (k := retaddr :: (stk ++ k))
               (rs := s7.regs) (zf := s7.zf) (h := s7.heap) (c := [some x'])
               hcode_body_at_s7 hrel_body hfresh_s7 with
      ⟨s8, hs8_raw, ⟨hpc8, hstack8, hrepr8, hext8⟩, hfresh8⟩
    -- ! Bridge: IH2's start state matches s7 by definitional equality.
    have hstart_eq :
        ({ pc := s7.pc, regs := s7.regs, stack := [s1.regs.rax] ++ (retaddr :: (stk ++ k)),
           zf := s7.zf, heap := s7.heap } : State) = s7 := by
      show ({ pc := s7.pc, regs := s7.regs,
              stack := s1.regs.rax :: retaddr :: (stk ++ k),
              zf := s7.zf, heap := s7.heap } : State) = s7
      rfl
    have hs7_to_s8 : Steps is s7 s8 := hstart_eq ▸ hs8_raw

    -- ! Useful facts after IH2.
    have hpc8_eq : s8.pc = entry_nat + compile_len e_body := by
      have h : s8.pc = s7.pc + compile_len e_body := hpc8
      exact h
    have hstack8_eq : s8.stack = s1.regs.rax :: retaddr :: (stk ++ k) := by
      -- ih2 promises stack = [s1.regs.rax] ++ (retaddr :: (stk ++ k)).
      show s8.stack = _
      simpa using hstack8

    -- ! 13) pop .r9 at s8 → s9: discard arg, stack := retaddr :: (stk ++ k).
    let s9 : State :=
      { pc := s8.pc + 1
        regs := Reg.write .r9 s1.regs.rax s8.regs
        stack := retaddr :: (stk ++ k)
        zf := s8.zf
        heap := s8.heap }
    have hpop1' : instr_at is s8.pc (.pop .r9) := by
      rw [hpc8_eq]; exact hpop1_body_at
    have hstep_pop1 : Step is s8 s9 :=
      Step.pop (s := s8) (hd := s1.regs.rax) (tl := retaddr :: (stk ++ k))
        hpop1' hstack8_eq

    -- ! 14) pop .r9 at s9 → s10: r9 := retaddr, stack := stk ++ k.
    let s10 : State :=
      { pc := s9.pc + 1
        regs := Reg.write .r9 retaddr s9.regs
        stack := stk ++ k
        zf := s9.zf
        heap := s9.heap }
    have hpop2' : instr_at is s9.pc (.pop .r9) := by
      show instr_at is (s8.pc + 1) (.pop .r9)
      rw [hpc8_eq]; exact hpop2_body_at
    have hstack9 : s9.stack = retaddr :: (stk ++ k) := rfl
    have hstep_pop2 : Step is s9 s10 :=
      Step.pop (s := s9) (hd := retaddr) (tl := stk ++ k) hpop2' hstack9

    -- ! 15) jmpabs .r9 at s10 → s11: pc := retaddr.toNat = s1.pc + 6.
    let s11 : State :=
      { pc := (s1.pc + 1) + 5
        regs := s10.regs
        stack := stk ++ k
        zf := s10.zf
        heap := s10.heap }
    have hjmpabs_ret' : instr_at is s10.pc (.jmpabs .r9) := by
      show instr_at is (s9.pc + 1) (.jmpabs .r9)
      show instr_at is (s8.pc + 1 + 1) (.jmpabs .r9)
      rw [hpc8_eq]; exact hjmpabs_body_at
    have hstep_jmpabs_ret : Step is s10 s11 := by
      have hraw := Step.jmpabs (s := s10) (src := .r9) hjmpabs_ret'
      have hr9_s10 : Reg.read .r9 s10.regs = retaddr := by
        show (Reg.write .r9 retaddr s9.regs).r9 = _
        simp [Reg.write]
      have hpc_eq : (Reg.read .r9 s10.regs).toNat = (s1.pc + 1) + 5 := by
        rw [hr9_s10]
        show ((Int.ofNat (s1.pc + 1) + 5 : Int)).toNat = (s1.pc + 1) + 5
        rfl
      simpa [s11, hpc_eq] using hraw

    -- ! 16) Package the result.
    refine ⟨s11, ?_, ?_, ?_⟩
    · -- ! Chain all steps.
      have h_s1_to_s2 : Steps is s1 s2 := Steps.trans Steps.refl hstep_movpc
      have h_s1_to_s3 : Steps is s1 s3 := Steps.trans h_s1_to_s2 hstep_addi
      have h_s1_to_s4 : Steps is s1 s4 := Steps.trans h_s1_to_s3 hstep_push_r9
      have h_s1_to_s5 : Steps is s1 s5 := Steps.trans h_s1_to_s4 hstep_push_rax
      have h_s1_to_s6 : Steps is s1 s6 := Steps.trans h_s1_to_s5 hstep_movi
      have h_s1_to_s7 : Steps is s1 s7 := Steps.trans h_s1_to_s6 hstep_jmpabs
      have h_s1_to_s8 : Steps is s1 s8 := Steps.append h_s1_to_s7 hs7_to_s8
      have h_s1_to_s9 : Steps is s1 s9 := Steps.trans h_s1_to_s8 hstep_pop1
      have h_s1_to_s10 : Steps is s1 s10 := Steps.trans h_s1_to_s9 hstep_pop2
      have h_s1_to_s11 : Steps is s1 s11 := Steps.trans h_s1_to_s10 hstep_jmpabs_ret
      exact Steps.append hs1 h_s1_to_s11
    · refine ⟨?_, ?_, ?_, ?_⟩
      · -- ! Final pc = pc + compile_len (.call f' e_arg) = pc + L + 6.
        show s11.pc = pc + compile_len (.call f' e_arg)
        show (s1.pc + 1) + 5 = pc + compile_len (.call f' e_arg)
        rw [hpc1]
        simp [compile_len]; omega
      · -- ! Stack restored.
        show s11.stack = stk ++ k
        rfl
      · -- ! rax holds the function result, representing v_val.
        show Represents v_val s11.regs.rax s11.heap
        have hrax_s11 : s11.regs.rax = s8.regs.rax := by
          show s10.regs.rax = s8.regs.rax
          show (Reg.write .r9 retaddr s9.regs).rax = s8.regs.rax
          show s9.regs.rax = s8.regs.rax
          show (Reg.write .r9 s1.regs.rax s8.regs).rax = s8.regs.rax
          simp [Reg.write]
        have hheap_s11 : s11.heap = s8.heap := rfl
        rw [hrax_s11, hheap_s11]
        exact hrepr8
      · -- ! Heap extension chain: hext1 (from IH1) ∘ hext8 (from IH2 with shifted base).
        show HeapExtends h s11.heap
        have hheap_s11_s8 : s11.heap = s8.heap := rfl
        rw [hheap_s11_s8]
        -- hext8 : HeapExtends s7.heap s8.heap. s7.heap = s1.heap.
        have hext_s1_s8 : HeapExtends s1.heap s8.heap := by
          have : HeapExtends s7.heap s8.heap := hext8
          rw [hheap_s7] at this; exact this
        exact HeapExtends.trans hext1 hext_s1_s8
    · -- ! FreshFrom carries from IH2 (rbx and heap untouched by the return trio).
      have hrbx_s11 : s11.regs.rbx = s8.regs.rbx := by
        show s10.regs.rbx = s8.regs.rbx
        show (Reg.write .r9 retaddr s9.regs).rbx = s8.regs.rbx
        show s9.regs.rbx = s8.regs.rbx
        show (Reg.write .r9 s1.regs.rax s8.regs).rbx = s8.regs.rbx
        simp [Reg.write]
      have hheap_s11_s8 : s11.heap = s8.heap := rfl
      rw [hheap_s11_s8, hrbx_s11]
      exact hfresh8

  | pairr _ _ ih1 ih2 =>
    -- ! `pair e1 e2` compiles to:
    -- !   compile e1 ; push rax ; compile e2 ;
    -- !   store rbx rax 1 ; pop rax ; store rbx rax 0 ; movr rax rbx ; addi rbx 2
    -- ! After IH1 we have v1 in rax; push it. After IH2 we have v2 in rax;
    -- ! store v2 at heap[rbx+1]. Pop v1 back, store v1 at heap[rbx+0],
    -- ! set rax = rbx (the pair address), bump rbx by 2.
    -- ! `Represents.pair` is then built from the two heap lookups. The two
    -- ! cells are fresh thanks to `hfresh3`; `FreshFrom.step` carries the
    -- ! freshness invariant past the allocation.
    rename_i r' e1_sub v1_val e2_sub v2_val _hev1 _hev2
    -- ! 1) Locate sub-pieces inside `is`.
    have hcode_e1 : code_at is pc (compile ds c e1_sub) :=
      code_at_compile_left
        (tail := [.push .rax] ++ compile ds (none :: c) e2_sub ++
                 [.store .rbx .rax 1, .pop .rax, .store .rbx .rax 0,
                  .movr .rax .rbx, .addi .rbx 2])
        (by simpa [compile, List.append_assoc] using hcode)
    have hpush_at_abs : instr_at is (pc + compile_len e1_sub) (.push .rax) := by
      have hmid : code_at is (pc + compile_len e1_sub) [.push .rax] := by
        simpa using
          (code_at_after_compile_prefix
            (pfx := []) (mid := [.push .rax])
            (sfx := compile ds (none :: c) e2_sub ++
                    [.store .rbx .rax 1, .pop .rax, .store .rbx .rax 0,
                     .movr .rax .rbx, .addi .rbx 2])
            (by simpa [compile, List.append_assoc] using hcode))
      exact code_at_head hmid
    have hcode_e2_abs :
        code_at is (pc + compile_len e1_sub + 1) (compile ds (none :: c) e2_sub) := by
      simpa using
        (code_at_after_compile_prefix
          (pfx := [.push .rax]) (mid := compile ds (none :: c) e2_sub)
          (sfx := [.store .rbx .rax 1, .pop .rax, .store .rbx .rax 0,
                   .movr .rax .rbx, .addi .rbx 2])
          (by simpa [compile, List.append_assoc] using hcode))
    have htail_at :
        code_at is (pc + compile_len e1_sub + 1 + compile_len e2_sub)
          [.store .rbx .rax 1, .pop .rax, .store .rbx .rax 0,
           .movr .rax .rbx, .addi .rbx 2] := by
      have h : code_at is (pc + compile_len e1_sub + 1)
          (compile ds (none :: c) e2_sub ++
           [.store .rbx .rax 1, .pop .rax, .store .rbx .rax 0,
            .movr .rax .rbx, .addi .rbx 2]) := by
        simpa [List.append_assoc] using
          (code_at_after_compile_prefix
            (pfx := [.push .rax])
            (mid := compile ds (none :: c) e2_sub ++
                    [.store .rbx .rax 1, .pop .rax, .store .rbx .rax 0,
                     .movr .rax .rbx, .addi .rbx 2])
            (sfx := [])
            (by simpa [compile, List.append_assoc] using hcode))
      have h2 : code_at is
          ((pc + compile_len e1_sub + 1) + (compile ds (none :: c) e2_sub).length)
          [.store .rbx .rax 1, .pop .rax, .store .rbx .rax 0,
           .movr .rax .rbx, .addi .rbx 2] :=
        code_at_app_right
          (c1 := compile ds (none :: c) e2_sub)
          (c2 := [.store .rbx .rax 1, .pop .rax, .store .rbx .rax 0,
                  .movr .rax .rbx, .addi .rbx 2]) h
      have hlen : (compile ds (none :: c) e2_sub).length = compile_len e2_sub :=
        compile_length _ _ _
      rw [hlen] at h2
      exact h2
    have hstore1_at_abs :
        instr_at is (pc + compile_len e1_sub + 1 + compile_len e2_sub)
          (.store .rbx .rax 1) :=
      code_at_head htail_at
    have hpop_at_abs :
        instr_at is (pc + compile_len e1_sub + 1 + compile_len e2_sub + 1)
          (.pop .rax) :=
      code_at_head (code_at_tail htail_at)
    have hstore2_at_abs :
        instr_at is (pc + compile_len e1_sub + 1 + compile_len e2_sub + 2)
          (.store .rbx .rax 0) :=
      code_at_head (code_at_tail (code_at_tail htail_at))
    have hmovr_at_abs :
        instr_at is (pc + compile_len e1_sub + 1 + compile_len e2_sub + 3)
          (.movr .rax .rbx) :=
      code_at_head (code_at_tail (code_at_tail (code_at_tail htail_at)))
    have haddi_at_abs :
        instr_at is (pc + compile_len e1_sub + 1 + compile_len e2_sub + 4)
          (.addi .rbx 2) :=
      code_at_head (code_at_tail (code_at_tail (code_at_tail (code_at_tail htail_at))))
    -- ! 2) IH1 → s1
    rcases ih1 hcode_e1 hrel hfresh with
      ⟨s1, hs1, ⟨hpc1, hstack1, hrepr1, hext1⟩, hfresh1⟩
    -- ! 3) push rax at s1 → s2
    let s2 : State :=
      { pc := s1.pc + 1, regs := s1.regs,
        stack := s1.regs.rax :: (stk ++ k),
        zf := s1.zf, heap := s1.heap }
    have hpush' : instr_at is s1.pc (.push .rax) := by
      simpa [hpc1] using hpush_at_abs
    have hstep_push : Step is s1 s2 := by
      have hraw := Step.push (s := s1) hpush'
      have hstack_eq : s1.regs.rax :: s1.stack = s1.regs.rax :: (stk ++ k) := by
        rw [hstack1]
      simpa [s2, Reg.read, hstack_eq] using hraw
    -- ! 4) Set up IH2 inputs.
    have hrel2 : Related (s1.regs.rax :: stk) (none :: c) r' s2.heap := by
      have hheap : s2.heap = s1.heap := by rfl
      rw [hheap]
      exact Related.push (Related.mono hrel hext1)
    have hfresh2 : FreshFrom s2.heap s2.regs.rbx := by
      have hheap : s2.heap = s1.heap := by rfl
      have hrbx : s2.regs.rbx = s1.regs.rbx := by rfl
      rw [hheap, hrbx]
      exact hfresh1
    have hcode_e2 : code_at is s2.pc (compile ds (none :: c) e2_sub) := by
      have hpc2eq : s2.pc = pc + compile_len e1_sub + 1 := by
        show s1.pc + 1 = pc + compile_len e1_sub + 1
        rw [hpc1]
      rw [hpc2eq]
      exact hcode_e2_abs
    rcases ih2 (pc := s2.pc) (stk := s1.regs.rax :: stk) (k := k)
               (rs := s2.regs) (zf := s2.zf) (h := s2.heap) (c := none :: c)
               hcode_e2 hrel2 hfresh2 with
      ⟨s3, hs3_raw, ⟨hpc3, hstack3, hrepr3, hext3⟩, hfresh3⟩
    -- ! IH2's start state is exactly s2.
    have hstart_eq :
        ({ pc := s2.pc, regs := s2.regs, stack := (s1.regs.rax :: stk) ++ k,
           zf := s2.zf, heap := s2.heap } : State) = s2 := by
      show ({ pc := s2.pc, regs := s2.regs, stack := s1.regs.rax :: (stk ++ k),
              zf := s2.zf, heap := s2.heap } : State) = s2
      rfl
    have hs2_to_s3 : Steps is s2 s3 := hstart_eq ▸ hs3_raw
    -- ! Precompute pc for s3.
    have hpc3eq : s3.pc = pc + compile_len e1_sub + 1 + compile_len e2_sub := by
      have h : s3.pc = s2.pc + compile_len e2_sub := hpc3
      rw [h]; show s1.pc + 1 + compile_len e2_sub = _; rw [hpc1]
    -- ! 5) store .rbx .rax 1 at s3 → s4
    let s4 : State :=
      { s3 with
        pc := s3.pc + 1
        heap := Heap.ext s3.heap (s3.regs.rbx + 1) s3.regs.rax }
    have hstore1' : instr_at is s3.pc (.store .rbx .rax 1) := by
      rw [hpc3eq]; exact hstore1_at_abs
    have hstep_store1 : Step is s3 s4 :=
      Step.store (s := s3) (addr := .rbx) (src := .rax) (offset := 1)
        (a := s3.regs.rbx) (v := s3.regs.rax) hstore1' rfl rfl
    -- ! 6) pop .rax at s4 → s5
    have hstack4 : s4.stack = s1.regs.rax :: (stk ++ k) := by
      show s3.stack = s1.regs.rax :: (stk ++ k)
      rw [hstack3]; rfl
    let s5 : State :=
      { s4 with
        pc := s4.pc + 1
        regs := Reg.write .rax s1.regs.rax s4.regs
        stack := stk ++ k }
    have hpop' : instr_at is s4.pc (.pop .rax) := by
      show instr_at is (s3.pc + 1) (.pop .rax)
      rw [hpc3eq]; exact hpop_at_abs
    have hstep_pop : Step is s4 s5 :=
      Step.pop (s := s4) (hd := s1.regs.rax) (tl := stk ++ k) hpop' hstack4
    -- ! 7) store .rbx .rax 0 at s5 → s6
    let s6 : State :=
      { s5 with
        pc := s5.pc + 1
        heap := Heap.ext s5.heap (s5.regs.rbx + 0) s5.regs.rax }
    have hstore2' : instr_at is s5.pc (.store .rbx .rax 0) := by
      show instr_at is (s4.pc + 1) (.store .rbx .rax 0)
      show instr_at is (s3.pc + 1 + 1) (.store .rbx .rax 0)
      rw [hpc3eq]; exact hstore2_at_abs
    have hstep_store2 : Step is s5 s6 :=
      Step.store (s := s5) (addr := .rbx) (src := .rax) (offset := 0)
        (a := s5.regs.rbx) (v := s5.regs.rax) hstore2' rfl rfl
    -- ! 8) movr .rax .rbx at s6 → s7
    let s7 : State :=
      { s6 with
        pc := s6.pc + 1
        regs := Reg.write .rax (Reg.read .rbx s6.regs) s6.regs }
    have hmovr' : instr_at is s6.pc (.movr .rax .rbx) := by
      show instr_at is (s5.pc + 1) (.movr .rax .rbx)
      show instr_at is (s4.pc + 1 + 1) (.movr .rax .rbx)
      show instr_at is (s3.pc + 1 + 1 + 1) (.movr .rax .rbx)
      rw [hpc3eq]; exact hmovr_at_abs
    have hstep_movr : Step is s6 s7 := Step.movr (s := s6) hmovr'
    -- ! 9) addi .rbx 2 at s7 → s8
    let s8 : State :=
      { s7 with
        pc := s7.pc + 1
        regs := Reg.write .rbx (Reg.read .rbx s7.regs + 2) s7.regs }
    have haddi' : instr_at is s7.pc (.addi .rbx 2) := by
      show instr_at is (s6.pc + 1) (.addi .rbx 2)
      show instr_at is (s5.pc + 1 + 1) (.addi .rbx 2)
      show instr_at is (s4.pc + 1 + 1 + 1) (.addi .rbx 2)
      show instr_at is (s3.pc + 1 + 1 + 1 + 1) (.addi .rbx 2)
      rw [hpc3eq]; exact haddi_at_abs
    have hstep_addi : Step is s7 s8 := Step.addi (s := s7) haddi'
    -- ! Key auxiliary facts about register/heap shapes.
    -- ! rbx stays at s3.regs.rbx through s4, s5, s6 (store/pop/store don't touch rbx).
    have hrbx_s5 : s5.regs.rbx = s3.regs.rbx := by
      show (Reg.write .rax s1.regs.rax s4.regs).rbx = s3.regs.rbx
      simp [Reg.write, s4]
    have hrbx_s6 : s6.regs.rbx = s3.regs.rbx := by
      show s5.regs.rbx = s3.regs.rbx
      exact hrbx_s5
    have hrax_s5 : s5.regs.rax = s1.regs.rax := by
      show (Reg.write .rax s1.regs.rax s4.regs).rax = s1.regs.rax
      simp [Reg.write]
    -- ! Heap progression.
    have hheap_s4 : s4.heap = Heap.ext s3.heap (s3.regs.rbx + 1) s3.regs.rax := by rfl
    have hheap_s5 : s5.heap = s4.heap := by rfl
    have hheap_s6 :
        s6.heap = Heap.ext s4.heap (s3.regs.rbx + 0) s1.regs.rax := by
      show Heap.ext s5.heap (s5.regs.rbx + 0) s5.regs.rax =
           Heap.ext s4.heap (s3.regs.rbx + 0) s1.regs.rax
      rw [hheap_s5, hrbx_s5, hrax_s5]
    have hheap_s8 : s8.heap = s6.heap := by rfl
    -- ! HeapExtends chain s3 → s4 → s6.
    -- yunze: FreshFrom is now a structure; use `.lookup` to apply.
    have hfresh3_at_1 : Heap.lookup s3.heap (s3.regs.rbx + 1) = none := by
      have h := hfresh3.lookup 1
      simpa using h
    have hfresh3_at_0 : Heap.lookup s3.heap (s3.regs.rbx + 0) = none := by
      have h := hfresh3.lookup 0
      simpa using h
    have hext_s3_s4 : HeapExtends s3.heap s4.heap := by
      rw [hheap_s4]
      exact HeapExtends.write hfresh3_at_1
    have hfresh_s4_at_0 : Heap.lookup s4.heap (s3.regs.rbx + 0) = none := by
      rw [hheap_s4]
      have hne : (s3.regs.rbx + 0 : Int) ≠ s3.regs.rbx + 1 := by omega
      rw [ext_lookup_of_ne hne]
      exact hfresh3_at_0
    have hext_s4_s6 : HeapExtends s4.heap s6.heap := by
      rw [hheap_s6]
      exact HeapExtends.write hfresh_s4_at_0
    have hext_s3_s8 : HeapExtends s3.heap s8.heap := by
      rw [hheap_s8]
      exact HeapExtends.trans hext_s3_s4 hext_s4_s6
    -- ! `i1 := s1.regs.rax` represents v1 in s8.heap, via mono through s3 then s8.
    have hrepr1_s8 : Represents v1_val s1.regs.rax s8.heap :=
      Represents.mono (Represents.mono hrepr1 hext3) hext_s3_s8
    -- ! `i2 := s3.regs.rax` represents v2 in s8.heap.
    have hrepr2_s8 : Represents v2_val s3.regs.rax s8.heap :=
      Represents.mono hrepr3 hext_s3_s8
    -- ! Look up the two cells in s8.heap.
    have hlook0 : Heap.lookup s8.heap (s3.regs.rbx + 0) = some s1.regs.rax := by
      rw [hheap_s8, hheap_s6]
      show Heap.lookup (Heap.ext _ (s3.regs.rbx + 0) s1.regs.rax) (s3.regs.rbx + 0)
           = some s1.regs.rax
      simp [Heap.lookup, Heap.ext]
    have hlook1 : Heap.lookup s8.heap (s3.regs.rbx + 1) = some s3.regs.rax := by
      rw [hheap_s8, hheap_s6, hheap_s4]
      have hne10 : (s3.regs.rbx + 1 : Int) ≠ s3.regs.rbx + 0 := by omega
      rw [ext_lookup_of_ne hne10]
      simp [Heap.lookup, Heap.ext]
    -- ! Build Represents.pair at the pair address `s3.regs.rbx`.
    -- yunze: supply the new `s3.regs.rbx ≥ 1` premise from `hfresh3.pos`.
    have hpair_at_addr : Represents (.pair v1_val v2_val) s3.regs.rbx s8.heap :=
      Represents.pair (i1 := s1.regs.rax) (i2 := s3.regs.rax)
        hrepr1_s8 hrepr2_s8 hlook0 hlook1 hfresh3.pos
    -- ! s8.regs.rax = s3.regs.rbx (movr rax rbx, addi rbx unchanged for rax).
    have hrax_s8 : s8.regs.rax = s3.regs.rbx := by
      show (Reg.write .rbx (Reg.read .rbx s7.regs + 2) s7.regs).rax = s3.regs.rbx
      show s7.regs.rax = s3.regs.rbx
      show (Reg.write .rax (Reg.read .rbx s6.regs) s6.regs).rax = s3.regs.rbx
      show Reg.read .rbx s6.regs = s3.regs.rbx
      show s6.regs.rbx = s3.regs.rbx
      exact hrbx_s6
    -- ! s8.regs.rbx = s3.regs.rbx + 2 (the post-allocation bump).
    have hrbx_s8 : s8.regs.rbx = s3.regs.rbx + 2 := by
      show (Reg.write .rbx (Reg.read .rbx s7.regs + 2) s7.regs).rbx = s3.regs.rbx + 2
      show Reg.read .rbx s7.regs + 2 = s3.regs.rbx + 2
      show s7.regs.rbx + 2 = s3.regs.rbx + 2
      show (Reg.write .rax (Reg.read .rbx s6.regs) s6.regs).rbx + 2 = s3.regs.rbx + 2
      show s6.regs.rbx + 2 = s3.regs.rbx + 2
      rw [hrbx_s6]
    refine ⟨s8, ?_, ?_, ?_⟩
    · -- ! Chain: initial →* s1 (IH1), s1 → s2 (push), s2 →* s3 (IH2),
      -- ! then s3 → s4 → s5 → s6 → s7 → s8 (the five-instruction tail).
      have h_s1_to_s2 : Steps is s1 s2 := Steps.trans Steps.refl hstep_push
      have h_s1_to_s3 : Steps is s1 s3 := Steps.append h_s1_to_s2 hs2_to_s3
      have h_s1_to_s4 : Steps is s1 s4 := Steps.trans h_s1_to_s3 hstep_store1
      have h_s1_to_s5 : Steps is s1 s5 := Steps.trans h_s1_to_s4 hstep_pop
      have h_s1_to_s6 : Steps is s1 s6 := Steps.trans h_s1_to_s5 hstep_store2
      have h_s1_to_s7 : Steps is s1 s7 := Steps.trans h_s1_to_s6 hstep_movr
      have h_s1_to_s8 : Steps is s1 s8 := Steps.trans h_s1_to_s7 hstep_addi
      exact Steps.append hs1 h_s1_to_s8
    · refine ⟨?_, ?_, ?_, ?_⟩
      · -- ! pc bookkeeping: 6 instrs past pc + L(e1) + L(e2).
        show s8.pc = pc + compile_len (.pair e1_sub e2_sub)
        show s7.pc + 1 = _
        show s6.pc + 1 + 1 = _
        show s5.pc + 1 + 1 + 1 = _
        show s4.pc + 1 + 1 + 1 + 1 = _
        show s3.pc + 1 + 1 + 1 + 1 + 1 = _
        rw [hpc3eq]
        simp [compile_len]; omega
      · -- ! stack restored.
        show s8.stack = stk ++ k
        rfl
      · -- ! rax represents (.pair v1 v2): rewrite rax to the pair address.
        show Represents (.pair v1_val v2_val) s8.regs.rax s8.heap
        rw [hrax_s8]
        exact hpair_at_addr
      · -- ! heap chain through IH1, IH2, and the two stores.
        show HeapExtends h s8.heap
        exact HeapExtends.trans hext1 (HeapExtends.trans hext3 hext_s3_s8)
    · -- ! FreshFrom: new rbx is `s3.regs.rbx + 2`; heap has two cells past it.
      show FreshFrom s8.heap s8.regs.rbx
      rw [hheap_s8, hheap_s6, hheap_s4, hrbx_s8]
      -- ! Normalize `s3.regs.rbx + 0` to `s3.regs.rbx` so the term matches
      -- ! `FreshFrom.step`'s output literal form.
      have heq : (s3.regs.rbx + 0 : Int) = s3.regs.rbx := Int.add_zero _
      rw [heq]
      exact FreshFrom.step hfresh3

  | fstr _ ih =>
    -- ! `fst e` compiles to `compile e ++ [load rax rax 0]`.
    -- ! IH gives us a heap address in rax representing `(v1, v2)`; the `load`
    -- ! reads heap[addr + 0] = i1, and `Represents.pair` tells us i1 represents v1.
    rename_i r' e_sub v1_val v2_val _hev
    have hcode_e : code_at is pc (compile ds c e_sub) :=
      code_at_compile_left
        (tail := [.load .rax .rax 0])
        (by simpa [compile] using hcode)
    have hload_at_abs :
        instr_at is (pc + compile_len e_sub) (.load .rax .rax 0) := by
      have hmid : code_at is (pc + compile_len e_sub) [.load .rax .rax 0] := by
        simpa using
          (code_at_after_compile_prefix
            (pfx := []) (mid := [.load .rax .rax 0]) (sfx := [])
            (by simpa [compile] using hcode))
      exact code_at_head hmid
    rcases ih hcode_e hrel hfresh with
      ⟨s1, hs1, ⟨hpc1, hstack1, hrepr1, hext1⟩, hfresh1⟩
    -- ? Crack open the `Represents (.pair v1 v2)` to get the heap layout.
    rcases Represents.pair_inv hrepr1 with ⟨i1, i2, hrep1, _hrep2, hlook1, _hlook2, _hpos⟩
    let s2 : State :=
      { s1 with
        pc := s1.pc + 1
        regs := Reg.write .rax i1 s1.regs }
    have hload' : instr_at is s1.pc (.load .rax .rax 0) := by
      simpa [hpc1] using hload_at_abs
    have hstep_load : Step is s1 s2 :=
      Step.load (s := s1) (dst := .rax) (addr := .rax) (offset := 0)
        (a := s1.regs.rax) (v := i1) hload' rfl hlook1
    refine ⟨s2, ?_, ?_, ?_⟩
    · exact Steps.trans hs1 hstep_load
    · refine ⟨?_, ?_, ?_, ?_⟩
      · -- ? pc bookkeeping: +1 after compile_len e.
        show s2.pc = pc + compile_len (.fst e_sub)
        simp [s2, hpc1, compile_len, Nat.add_assoc]
      · -- ? stack unchanged.
        show s2.stack = stk ++ k
        simp [s2, hstack1]
      · -- ? rax now holds i1, which represents v1.
        show Represents v1_val s2.regs.rax s2.heap
        have hrax : (Reg.write .rax i1 s1.regs).rax = i1 := by simp [Reg.write]
        have hheap : s2.heap = s1.heap := by rfl
        show Represents v1_val (Reg.write .rax i1 s1.regs).rax s1.heap
        rw [hrax]; exact hrep1
      · -- ? heap unchanged.
        show HeapExtends h s2.heap
        have : s2.heap = s1.heap := by rfl
        rw [this]
        exact hext1
    · -- ? rbx unchanged.
      have hheap : s2.heap = s1.heap := by rfl
      have hrbx : s2.regs.rbx = s1.regs.rbx := by simp [s2, Reg.write]
      rw [hheap, hrbx]
      exact hfresh1

  | sndr _ ih =>
    -- ! Same as `fstr` but offset 1 — we want the second component instead.
    rename_i r' e_sub v1_val v2_val _hev
    have hcode_e : code_at is pc (compile ds c e_sub) :=
      code_at_compile_left
        (tail := [.load .rax .rax 1])
        (by simpa [compile] using hcode)
    have hload_at_abs :
        instr_at is (pc + compile_len e_sub) (.load .rax .rax 1) := by
      have hmid : code_at is (pc + compile_len e_sub) [.load .rax .rax 1] := by
        simpa using
          (code_at_after_compile_prefix
            (pfx := []) (mid := [.load .rax .rax 1]) (sfx := [])
            (by simpa [compile] using hcode))
      exact code_at_head hmid
    rcases ih hcode_e hrel hfresh with
      ⟨s1, hs1, ⟨hpc1, hstack1, hrepr1, hext1⟩, hfresh1⟩
    rcases Represents.pair_inv hrepr1 with ⟨i1, i2, _hrep1, hrep2, _hlook1, hlook2, _hpos⟩
    let s2 : State :=
      { s1 with
        pc := s1.pc + 1
        regs := Reg.write .rax i2 s1.regs }
    have hload' : instr_at is s1.pc (.load .rax .rax 1) := by
      simpa [hpc1] using hload_at_abs
    have hstep_load : Step is s1 s2 :=
      Step.load (s := s1) (dst := .rax) (addr := .rax) (offset := 1)
        (a := s1.regs.rax) (v := i2) hload' rfl hlook2
    refine ⟨s2, ?_, ?_, ?_⟩
    · exact Steps.trans hs1 hstep_load
    · refine ⟨?_, ?_, ?_, ?_⟩
      · show s2.pc = pc + compile_len (.snd e_sub)
        simp [s2, hpc1, compile_len, Nat.add_assoc]
      · show s2.stack = stk ++ k
        simp [s2, hstack1]
      · show Represents v2_val s2.regs.rax s2.heap
        have hrax : (Reg.write .rax i2 s1.regs).rax = i2 := by simp [Reg.write]
        show Represents v2_val (Reg.write .rax i2 s1.regs).rax s1.heap
        rw [hrax]; exact hrep2
      · have : s2.heap = s1.heap := by rfl
        rw [this]
        exact hext1
    · have hheap : s2.heap = s1.heap := by rfl
      have hrbx : s2.regs.rbx = s1.regs.rbx := by simp [s2, Reg.write]
      rw [hheap, hrbx]
      exact hfresh1

  | consr _ _ ih1 ih2 =>
    -- ! `cons e1 e2` compiles to the exact same instruction sequence as
    -- ! `pair e1 e2`, and `Eval.consr` produces `.pair v1 v2`. So this proof
    -- ! is identical to the `pairr` case modulo `compile_len (.cons ...)`.
    rename_i r' e1_sub v1_val e2_sub v2_val _hev1 _hev2
    -- ! 1) Locate sub-pieces inside `is`.
    have hcode_e1 : code_at is pc (compile ds c e1_sub) :=
      code_at_compile_left
        (tail := [.push .rax] ++ compile ds (none :: c) e2_sub ++
                 [.store .rbx .rax 1, .pop .rax, .store .rbx .rax 0,
                  .movr .rax .rbx, .addi .rbx 2])
        (by simpa [compile, List.append_assoc] using hcode)
    have hpush_at_abs : instr_at is (pc + compile_len e1_sub) (.push .rax) := by
      have hmid : code_at is (pc + compile_len e1_sub) [.push .rax] := by
        simpa using
          (code_at_after_compile_prefix
            (pfx := []) (mid := [.push .rax])
            (sfx := compile ds (none :: c) e2_sub ++
                    [.store .rbx .rax 1, .pop .rax, .store .rbx .rax 0,
                     .movr .rax .rbx, .addi .rbx 2])
            (by simpa [compile, List.append_assoc] using hcode))
      exact code_at_head hmid
    have hcode_e2_abs :
        code_at is (pc + compile_len e1_sub + 1) (compile ds (none :: c) e2_sub) := by
      simpa using
        (code_at_after_compile_prefix
          (pfx := [.push .rax]) (mid := compile ds (none :: c) e2_sub)
          (sfx := [.store .rbx .rax 1, .pop .rax, .store .rbx .rax 0,
                   .movr .rax .rbx, .addi .rbx 2])
          (by simpa [compile, List.append_assoc] using hcode))
    have htail_at :
        code_at is (pc + compile_len e1_sub + 1 + compile_len e2_sub)
          [.store .rbx .rax 1, .pop .rax, .store .rbx .rax 0,
           .movr .rax .rbx, .addi .rbx 2] := by
      have h : code_at is (pc + compile_len e1_sub + 1)
          (compile ds (none :: c) e2_sub ++
           [.store .rbx .rax 1, .pop .rax, .store .rbx .rax 0,
            .movr .rax .rbx, .addi .rbx 2]) := by
        simpa [List.append_assoc] using
          (code_at_after_compile_prefix
            (pfx := [.push .rax])
            (mid := compile ds (none :: c) e2_sub ++
                    [.store .rbx .rax 1, .pop .rax, .store .rbx .rax 0,
                     .movr .rax .rbx, .addi .rbx 2])
            (sfx := [])
            (by simpa [compile, List.append_assoc] using hcode))
      have h2 : code_at is
          ((pc + compile_len e1_sub + 1) + (compile ds (none :: c) e2_sub).length)
          [.store .rbx .rax 1, .pop .rax, .store .rbx .rax 0,
           .movr .rax .rbx, .addi .rbx 2] :=
        code_at_app_right
          (c1 := compile ds (none :: c) e2_sub)
          (c2 := [.store .rbx .rax 1, .pop .rax, .store .rbx .rax 0,
                  .movr .rax .rbx, .addi .rbx 2]) h
      have hlen : (compile ds (none :: c) e2_sub).length = compile_len e2_sub :=
        compile_length _ _ _
      rw [hlen] at h2
      exact h2
    have hstore1_at_abs :
        instr_at is (pc + compile_len e1_sub + 1 + compile_len e2_sub)
          (.store .rbx .rax 1) :=
      code_at_head htail_at
    have hpop_at_abs :
        instr_at is (pc + compile_len e1_sub + 1 + compile_len e2_sub + 1)
          (.pop .rax) :=
      code_at_head (code_at_tail htail_at)
    have hstore2_at_abs :
        instr_at is (pc + compile_len e1_sub + 1 + compile_len e2_sub + 2)
          (.store .rbx .rax 0) :=
      code_at_head (code_at_tail (code_at_tail htail_at))
    have hmovr_at_abs :
        instr_at is (pc + compile_len e1_sub + 1 + compile_len e2_sub + 3)
          (.movr .rax .rbx) :=
      code_at_head (code_at_tail (code_at_tail (code_at_tail htail_at)))
    have haddi_at_abs :
        instr_at is (pc + compile_len e1_sub + 1 + compile_len e2_sub + 4)
          (.addi .rbx 2) :=
      code_at_head (code_at_tail (code_at_tail (code_at_tail (code_at_tail htail_at))))
    -- ! 2) IH1 → s1
    rcases ih1 hcode_e1 hrel hfresh with
      ⟨s1, hs1, ⟨hpc1, hstack1, hrepr1, hext1⟩, hfresh1⟩
    -- ! 3) push rax at s1 → s2
    let s2 : State :=
      { pc := s1.pc + 1, regs := s1.regs,
        stack := s1.regs.rax :: (stk ++ k),
        zf := s1.zf, heap := s1.heap }
    have hpush' : instr_at is s1.pc (.push .rax) := by
      simpa [hpc1] using hpush_at_abs
    have hstep_push : Step is s1 s2 := by
      have hraw := Step.push (s := s1) hpush'
      have hstack_eq : s1.regs.rax :: s1.stack = s1.regs.rax :: (stk ++ k) := by
        rw [hstack1]
      simpa [s2, Reg.read, hstack_eq] using hraw
    -- ! 4) Set up IH2 inputs.
    have hrel2 : Related (s1.regs.rax :: stk) (none :: c) r' s2.heap := by
      have hheap : s2.heap = s1.heap := by rfl
      rw [hheap]
      exact Related.push (Related.mono hrel hext1)
    have hfresh2 : FreshFrom s2.heap s2.regs.rbx := by
      have hheap : s2.heap = s1.heap := by rfl
      have hrbx : s2.regs.rbx = s1.regs.rbx := by rfl
      rw [hheap, hrbx]
      exact hfresh1
    have hcode_e2 : code_at is s2.pc (compile ds (none :: c) e2_sub) := by
      have hpc2eq : s2.pc = pc + compile_len e1_sub + 1 := by
        show s1.pc + 1 = pc + compile_len e1_sub + 1
        rw [hpc1]
      rw [hpc2eq]
      exact hcode_e2_abs
    rcases ih2 (pc := s2.pc) (stk := s1.regs.rax :: stk) (k := k)
               (rs := s2.regs) (zf := s2.zf) (h := s2.heap) (c := none :: c)
               hcode_e2 hrel2 hfresh2 with
      ⟨s3, hs3_raw, ⟨hpc3, hstack3, hrepr3, hext3⟩, hfresh3⟩
    -- ! IH2's start state is exactly s2.
    have hstart_eq :
        ({ pc := s2.pc, regs := s2.regs, stack := (s1.regs.rax :: stk) ++ k,
           zf := s2.zf, heap := s2.heap } : State) = s2 := by
      show ({ pc := s2.pc, regs := s2.regs, stack := s1.regs.rax :: (stk ++ k),
              zf := s2.zf, heap := s2.heap } : State) = s2
      rfl
    have hs2_to_s3 : Steps is s2 s3 := hstart_eq ▸ hs3_raw
    -- ! Precompute pc for s3.
    have hpc3eq : s3.pc = pc + compile_len e1_sub + 1 + compile_len e2_sub := by
      have h : s3.pc = s2.pc + compile_len e2_sub := hpc3
      rw [h]; show s1.pc + 1 + compile_len e2_sub = _; rw [hpc1]
    -- ! 5) store .rbx .rax 1 at s3 → s4
    let s4 : State :=
      { s3 with
        pc := s3.pc + 1
        heap := Heap.ext s3.heap (s3.regs.rbx + 1) s3.regs.rax }
    have hstore1' : instr_at is s3.pc (.store .rbx .rax 1) := by
      rw [hpc3eq]; exact hstore1_at_abs
    have hstep_store1 : Step is s3 s4 :=
      Step.store (s := s3) (addr := .rbx) (src := .rax) (offset := 1)
        (a := s3.regs.rbx) (v := s3.regs.rax) hstore1' rfl rfl
    -- ! 6) pop .rax at s4 → s5
    have hstack4 : s4.stack = s1.regs.rax :: (stk ++ k) := by
      show s3.stack = s1.regs.rax :: (stk ++ k)
      rw [hstack3]; rfl
    let s5 : State :=
      { s4 with
        pc := s4.pc + 1
        regs := Reg.write .rax s1.regs.rax s4.regs
        stack := stk ++ k }
    have hpop' : instr_at is s4.pc (.pop .rax) := by
      show instr_at is (s3.pc + 1) (.pop .rax)
      rw [hpc3eq]; exact hpop_at_abs
    have hstep_pop : Step is s4 s5 :=
      Step.pop (s := s4) (hd := s1.regs.rax) (tl := stk ++ k) hpop' hstack4
    -- ! 7) store .rbx .rax 0 at s5 → s6
    let s6 : State :=
      { s5 with
        pc := s5.pc + 1
        heap := Heap.ext s5.heap (s5.regs.rbx + 0) s5.regs.rax }
    have hstore2' : instr_at is s5.pc (.store .rbx .rax 0) := by
      show instr_at is (s4.pc + 1) (.store .rbx .rax 0)
      show instr_at is (s3.pc + 1 + 1) (.store .rbx .rax 0)
      rw [hpc3eq]; exact hstore2_at_abs
    have hstep_store2 : Step is s5 s6 :=
      Step.store (s := s5) (addr := .rbx) (src := .rax) (offset := 0)
        (a := s5.regs.rbx) (v := s5.regs.rax) hstore2' rfl rfl
    -- ! 8) movr .rax .rbx at s6 → s7
    let s7 : State :=
      { s6 with
        pc := s6.pc + 1
        regs := Reg.write .rax (Reg.read .rbx s6.regs) s6.regs }
    have hmovr' : instr_at is s6.pc (.movr .rax .rbx) := by
      show instr_at is (s5.pc + 1) (.movr .rax .rbx)
      show instr_at is (s4.pc + 1 + 1) (.movr .rax .rbx)
      show instr_at is (s3.pc + 1 + 1 + 1) (.movr .rax .rbx)
      rw [hpc3eq]; exact hmovr_at_abs
    have hstep_movr : Step is s6 s7 := Step.movr (s := s6) hmovr'
    -- ! 9) addi .rbx 2 at s7 → s8
    let s8 : State :=
      { s7 with
        pc := s7.pc + 1
        regs := Reg.write .rbx (Reg.read .rbx s7.regs + 2) s7.regs }
    have haddi' : instr_at is s7.pc (.addi .rbx 2) := by
      show instr_at is (s6.pc + 1) (.addi .rbx 2)
      show instr_at is (s5.pc + 1 + 1) (.addi .rbx 2)
      show instr_at is (s4.pc + 1 + 1 + 1) (.addi .rbx 2)
      show instr_at is (s3.pc + 1 + 1 + 1 + 1) (.addi .rbx 2)
      rw [hpc3eq]; exact haddi_at_abs
    have hstep_addi : Step is s7 s8 := Step.addi (s := s7) haddi'
    have hrbx_s5 : s5.regs.rbx = s3.regs.rbx := by
      show (Reg.write .rax s1.regs.rax s4.regs).rbx = s3.regs.rbx
      simp [Reg.write, s4]
    have hrbx_s6 : s6.regs.rbx = s3.regs.rbx := by
      show s5.regs.rbx = s3.regs.rbx
      exact hrbx_s5
    have hrax_s5 : s5.regs.rax = s1.regs.rax := by
      show (Reg.write .rax s1.regs.rax s4.regs).rax = s1.regs.rax
      simp [Reg.write]
    have hheap_s4 : s4.heap = Heap.ext s3.heap (s3.regs.rbx + 1) s3.regs.rax := by rfl
    have hheap_s5 : s5.heap = s4.heap := by rfl
    have hheap_s6 :
        s6.heap = Heap.ext s4.heap (s3.regs.rbx + 0) s1.regs.rax := by
      show Heap.ext s5.heap (s5.regs.rbx + 0) s5.regs.rax =
           Heap.ext s4.heap (s3.regs.rbx + 0) s1.regs.rax
      rw [hheap_s5, hrbx_s5, hrax_s5]
    have hheap_s8 : s8.heap = s6.heap := by rfl
    -- yunze: FreshFrom is now a structure; use `.lookup` to apply.
    have hfresh3_at_1 : Heap.lookup s3.heap (s3.regs.rbx + 1) = none := by
      have h := hfresh3.lookup 1
      simpa using h
    have hfresh3_at_0 : Heap.lookup s3.heap (s3.regs.rbx + 0) = none := by
      have h := hfresh3.lookup 0
      simpa using h
    have hext_s3_s4 : HeapExtends s3.heap s4.heap := by
      rw [hheap_s4]
      exact HeapExtends.write hfresh3_at_1
    have hfresh_s4_at_0 : Heap.lookup s4.heap (s3.regs.rbx + 0) = none := by
      rw [hheap_s4]
      have hne : (s3.regs.rbx + 0 : Int) ≠ s3.regs.rbx + 1 := by omega
      rw [ext_lookup_of_ne hne]
      exact hfresh3_at_0
    have hext_s4_s6 : HeapExtends s4.heap s6.heap := by
      rw [hheap_s6]
      exact HeapExtends.write hfresh_s4_at_0
    have hext_s3_s8 : HeapExtends s3.heap s8.heap := by
      rw [hheap_s8]
      exact HeapExtends.trans hext_s3_s4 hext_s4_s6
    have hrepr1_s8 : Represents v1_val s1.regs.rax s8.heap :=
      Represents.mono (Represents.mono hrepr1 hext3) hext_s3_s8
    have hrepr2_s8 : Represents v2_val s3.regs.rax s8.heap :=
      Represents.mono hrepr3 hext_s3_s8
    have hlook0 : Heap.lookup s8.heap (s3.regs.rbx + 0) = some s1.regs.rax := by
      rw [hheap_s8, hheap_s6]
      show Heap.lookup (Heap.ext _ (s3.regs.rbx + 0) s1.regs.rax) (s3.regs.rbx + 0)
           = some s1.regs.rax
      simp [Heap.lookup, Heap.ext]
    have hlook1 : Heap.lookup s8.heap (s3.regs.rbx + 1) = some s3.regs.rax := by
      rw [hheap_s8, hheap_s6, hheap_s4]
      have hne10 : (s3.regs.rbx + 1 : Int) ≠ s3.regs.rbx + 0 := by omega
      rw [ext_lookup_of_ne hne10]
      simp [Heap.lookup, Heap.ext]
    -- yunze: supply the new `s3.regs.rbx ≥ 1` premise from `hfresh3.pos`.
    have hpair_at_addr : Represents (.pair v1_val v2_val) s3.regs.rbx s8.heap :=
      Represents.pair (i1 := s1.regs.rax) (i2 := s3.regs.rax)
        hrepr1_s8 hrepr2_s8 hlook0 hlook1 hfresh3.pos
    have hrax_s8 : s8.regs.rax = s3.regs.rbx := by
      show (Reg.write .rbx (Reg.read .rbx s7.regs + 2) s7.regs).rax = s3.regs.rbx
      show s7.regs.rax = s3.regs.rbx
      show (Reg.write .rax (Reg.read .rbx s6.regs) s6.regs).rax = s3.regs.rbx
      show Reg.read .rbx s6.regs = s3.regs.rbx
      show s6.regs.rbx = s3.regs.rbx
      exact hrbx_s6
    have hrbx_s8 : s8.regs.rbx = s3.regs.rbx + 2 := by
      show (Reg.write .rbx (Reg.read .rbx s7.regs + 2) s7.regs).rbx = s3.regs.rbx + 2
      show Reg.read .rbx s7.regs + 2 = s3.regs.rbx + 2
      show s7.regs.rbx + 2 = s3.regs.rbx + 2
      show (Reg.write .rax (Reg.read .rbx s6.regs) s6.regs).rbx + 2 = s3.regs.rbx + 2
      show s6.regs.rbx + 2 = s3.regs.rbx + 2
      rw [hrbx_s6]
    refine ⟨s8, ?_, ?_, ?_⟩
    · have h_s1_to_s2 : Steps is s1 s2 := Steps.trans Steps.refl hstep_push
      have h_s1_to_s3 : Steps is s1 s3 := Steps.append h_s1_to_s2 hs2_to_s3
      have h_s1_to_s4 : Steps is s1 s4 := Steps.trans h_s1_to_s3 hstep_store1
      have h_s1_to_s5 : Steps is s1 s5 := Steps.trans h_s1_to_s4 hstep_pop
      have h_s1_to_s6 : Steps is s1 s6 := Steps.trans h_s1_to_s5 hstep_store2
      have h_s1_to_s7 : Steps is s1 s7 := Steps.trans h_s1_to_s6 hstep_movr
      have h_s1_to_s8 : Steps is s1 s8 := Steps.trans h_s1_to_s7 hstep_addi
      exact Steps.append hs1 h_s1_to_s8
    · refine ⟨?_, ?_, ?_, ?_⟩
      · show s8.pc = pc + compile_len (.cons e1_sub e2_sub)
        show s7.pc + 1 = _
        show s6.pc + 1 + 1 = _
        show s5.pc + 1 + 1 + 1 = _
        show s4.pc + 1 + 1 + 1 + 1 = _
        show s3.pc + 1 + 1 + 1 + 1 + 1 = _
        rw [hpc3eq]
        simp [compile_len]; omega
      · show s8.stack = stk ++ k
        rfl
      · show Represents (.pair v1_val v2_val) s8.regs.rax s8.heap
        rw [hrax_s8]
        exact hpair_at_addr
      · show HeapExtends h s8.heap
        exact HeapExtends.trans hext1 (HeapExtends.trans hext3 hext_s3_s8)
    · show FreshFrom s8.heap s8.regs.rbx
      rw [hheap_s8, hheap_s6, hheap_s4, hrbx_s8]
      have heq : (s3.regs.rbx + 0 : Int) = s3.regs.rbx := Int.add_zero _
      rw [heq]
      exact FreshFrom.step hfresh3

  | isnilt _ ih =>
    -- ! yunze: with the corrected codegen
    -- !     [movi r9 0, cmp rax r9, movi rax 0, bnz 2, movi rax 1]
    -- ! the `isnilt` case (input is `.nil`, output is `.bool true`) goes:
    -- !   IH gives rax = 0 (Represents.nil_inv).
    -- !   movi r9 0 → r9 = 0.
    -- !   cmp        → zf = (0 == 0) = true.
    -- !   movi rax 0 → rax = 0.
    -- !   bnz 2 with zf = true → bnzf falls through (pc + 1).
    -- !   movi rax 1 → rax = 1 = encoding of `.bool true`. ✓
    rename_i r' e_sub _hev
    -- ! 1) Locate the 5 trailing instructions inside `is`.
    have hcode_e_sub : code_at is pc (compile ds c e_sub) :=
      code_at_compile_left
        (tail := [.movi .r9 0, .cmp .rax .r9, .movi .rax 0, .bnz 2, .movi .rax 1])
        (by simpa [compile, List.append_assoc] using hcode)
    have htail_at :
        code_at is (pc + compile_len e_sub)
          [.movi .r9 0, .cmp .rax .r9, .movi .rax 0, .bnz 2, .movi .rax 1] := by
      simpa using
        (code_at_after_compile_prefix
          (pfx := [])
          (mid := [.movi .r9 0, .cmp .rax .r9, .movi .rax 0, .bnz 2, .movi .rax 1])
          (sfx := [])
          (by simpa [compile, List.append_assoc] using hcode))
    have hmovi_r9_at_abs : instr_at is (pc + compile_len e_sub) (.movi .r9 0) :=
      code_at_head htail_at
    have hcmp_at_abs : instr_at is (pc + compile_len e_sub + 1) (.cmp .rax .r9) :=
      code_at_head (code_at_tail htail_at)
    have hmovi_0_at_abs : instr_at is (pc + compile_len e_sub + 2) (.movi .rax 0) :=
      code_at_head (code_at_tail (code_at_tail htail_at))
    have hbnz_at_abs : instr_at is (pc + compile_len e_sub + 3) (.bnz 2) :=
      code_at_head (code_at_tail (code_at_tail (code_at_tail htail_at)))
    have hmovi_1_at_abs : instr_at is (pc + compile_len e_sub + 4) (.movi .rax 1) :=
      code_at_head (code_at_tail (code_at_tail (code_at_tail (code_at_tail htail_at))))
    -- ! 2) IH on e_sub → s1, rax represents .nil so rax = 0.
    rcases ih hcode_e_sub hrel hfresh with
      ⟨s1, hs1, ⟨hpc1, hstack1, hrepr1, hext1⟩, hfresh1⟩
    have hrax1 : s1.regs.rax = 0 := Represents.nil_inv hrepr1
    -- ! 3) movi r9 0 at s1 → s2
    let s2 : State :=
      { s1 with
        pc := s1.pc + 1
        regs := Reg.write .r9 0 s1.regs }
    have hmovi_r9' : instr_at is s1.pc (.movi .r9 0) := by
      simpa [hpc1] using hmovi_r9_at_abs
    have hstep_movi_r9 : Step is s1 s2 := Step.movi (s := s1) hmovi_r9'
    -- ! 4) cmp rax r9 at s2 → s3. zf = (0 == 0) = true.
    let s3 : State :=
      { s2 with
        pc := s2.pc + 1
        zf := (Reg.read .rax s2.regs == Reg.read .r9 s2.regs) }
    have hcmp' : instr_at is s2.pc (.cmp .rax .r9) := by
      show instr_at is (s1.pc + 1) (.cmp .rax .r9)
      have hh : (s1.pc + 1 : Nat) = pc + compile_len e_sub + 1 := by rw [hpc1]
      rw [hh]; exact hcmp_at_abs
    have hstep_cmp : Step is s2 s3 := Step.cmp (s := s2) hcmp'
    have hzf3 : s3.zf = true := by
      show (Reg.read .rax s2.regs == Reg.read .r9 s2.regs) = true
      have hr9 : Reg.read .r9 s2.regs = 0 := by
        show (Reg.write .r9 0 s1.regs).r9 = 0
        simp [Reg.write]
      have hax : Reg.read .rax s2.regs = 0 := by
        show (Reg.write .r9 0 s1.regs).rax = 0
        show s1.regs.rax = 0
        exact hrax1
      rw [hax, hr9]; decide
    -- ! 5) movi rax 0 at s3 → s4. rax = 0.
    let s4 : State :=
      { s3 with
        pc := s3.pc + 1
        regs := Reg.write .rax 0 s3.regs }
    have hmovi_0' : instr_at is s3.pc (.movi .rax 0) := by
      show instr_at is (s2.pc + 1) (.movi .rax 0)
      show instr_at is (s1.pc + 1 + 1) (.movi .rax 0)
      have hh : (s1.pc + 1 + 1 : Nat) = pc + compile_len e_sub + 2 := by rw [hpc1]
      rw [hh]; exact hmovi_0_at_abs
    have hstep_movi_0 : Step is s3 s4 := Step.movi (s := s3) hmovi_0'
    -- ! 6) bnz 2 at s4: zf = true, so bnzf falls through (pc + 1).
    let s5 : State :=
      { s4 with pc := s4.pc + 1 }
    have hbnz' : instr_at is s4.pc (.bnz 2) := by
      show instr_at is (s3.pc + 1) (.bnz 2)
      show instr_at is (s2.pc + 1 + 1) (.bnz 2)
      show instr_at is (s1.pc + 1 + 1 + 1) (.bnz 2)
      have hh : (s1.pc + 1 + 1 + 1 : Nat) = pc + compile_len e_sub + 3 := by rw [hpc1]
      rw [hh]; exact hbnz_at_abs
    have hzf4 : s4.zf = true := by
      show s3.zf = true
      exact hzf3
    have hstep_bnz : Step is s4 s5 := Step.bnzf (s := s4) hbnz' hzf4
    -- ! 7) movi rax 1 at s5 → s6. rax = 1.
    let s6 : State :=
      { s5 with
        pc := s5.pc + 1
        regs := Reg.write .rax 1 s5.regs }
    have hmovi_1' : instr_at is s5.pc (.movi .rax 1) := by
      show instr_at is (s4.pc + 1) (.movi .rax 1)
      show instr_at is (s3.pc + 1 + 1) (.movi .rax 1)
      show instr_at is (s2.pc + 1 + 1 + 1) (.movi .rax 1)
      show instr_at is (s1.pc + 1 + 1 + 1 + 1) (.movi .rax 1)
      have hh : (s1.pc + 1 + 1 + 1 + 1 : Nat) = pc + compile_len e_sub + 4 := by rw [hpc1]
      rw [hh]; exact hmovi_1_at_abs
    have hstep_movi_1 : Step is s5 s6 := Step.movi (s := s5) hmovi_1'
    -- ! 8) Package: chain s1 → s2 → s3 → s4 → s5 → s6.
    refine ⟨s6, ?_, ?_, ?_⟩
    · have h_s1_to_s2 : Steps is s1 s2 := Steps.trans Steps.refl hstep_movi_r9
      have h_s1_to_s3 : Steps is s1 s3 := Steps.trans h_s1_to_s2 hstep_cmp
      have h_s1_to_s4 : Steps is s1 s4 := Steps.trans h_s1_to_s3 hstep_movi_0
      have h_s1_to_s5 : Steps is s1 s5 := Steps.trans h_s1_to_s4 hstep_bnz
      have h_s1_to_s6 : Steps is s1 s6 := Steps.trans h_s1_to_s5 hstep_movi_1
      exact Steps.append hs1 h_s1_to_s6
    · refine ⟨?_, ?_, ?_, ?_⟩
      · -- ! pc bookkeeping: 5 instrs past pc + compile_len e_sub.
        show s6.pc = pc + compile_len (.is_nil e_sub)
        show s5.pc + 1 = _
        show s4.pc + 1 + 1 = _
        show s3.pc + 1 + 1 + 1 = _
        show s2.pc + 1 + 1 + 1 + 1 = _
        show s1.pc + 1 + 1 + 1 + 1 + 1 = _
        rw [hpc1]; simp [compile_len]; omega
      · -- ! Stack untouched by movi/cmp/bnz/movi.
        show s6.stack = stk ++ k
        show s5.stack = stk ++ k
        show s4.stack = stk ++ k
        show s3.stack = stk ++ k
        show s2.stack = stk ++ k
        show s1.stack = stk ++ k
        exact hstack1
      · -- ! rax = 1 represents .bool true.
        show Represents (.bool true) s6.regs.rax s6.heap
        have hrax6 : s6.regs.rax = 1 := by
          show (Reg.write .rax 1 s5.regs).rax = 1
          simp [Reg.write]
        rw [hrax6]
        -- ! Represents.bool gives `Represents (.bool b) (if b then 1 else 0) h`.
        exact Represents.bool (b := true)
      · -- ! Heap unchanged across all 5 trailing instructions.
        show HeapExtends h s6.heap
        have hheap6 : s6.heap = s1.heap := by
          show s5.heap = s1.heap
          show s4.heap = s1.heap
          show s3.heap = s1.heap
          show s2.heap = s1.heap
          rfl
        rw [hheap6]
        exact hext1
    · -- ! FreshFrom: heap unchanged, rbx unchanged.
      have hheap6 : s6.heap = s1.heap := by
        show s5.heap = s1.heap
        show s4.heap = s1.heap
        show s3.heap = s1.heap
        show s2.heap = s1.heap
        rfl
      have hrbx6 : s6.regs.rbx = s1.regs.rbx := by
        show (Reg.write .rax 1 s5.regs).rbx = s1.regs.rbx
        show s5.regs.rbx = s1.regs.rbx
        show s4.regs.rbx = s1.regs.rbx
        show (Reg.write .rax 0 s3.regs).rbx = s1.regs.rbx
        show s3.regs.rbx = s1.regs.rbx
        show s2.regs.rbx = s1.regs.rbx
        show (Reg.write .r9 0 s1.regs).rbx = s1.regs.rbx
        simp [Reg.write]
      rw [hheap6, hrbx6]
      exact hfresh1

  | isnilf _ ih =>
    -- ! yunze: now unblocked by Option A (strengthened FreshFrom + `i ≥ 1` on
    -- ! Represents.pair). Trace with the corrected codegen
    -- !     [movi r9 0, cmp rax r9, movi rax 0, bnz 2, movi rax 1]:
    -- !   IH gives Represents (.pair v1 v2) rax heap. By `pair_inv` we extract
    -- !   `rax ≥ 1`, so rax ≠ 0.
    -- !   movi r9 0 → r9 = 0.
    -- !   cmp        → zf = (rax == 0) = false (since rax ≥ 1).
    -- !   movi rax 0 → rax = 0.
    -- !   bnz 2 with zf = false → bnzt jumps pc + 2 (skips movi rax 1).
    -- !   Final: rax = 0 = encoding of `.bool false`. ✓
    rename_i r' e_sub v1_val v2_val _hev
    -- ! 1) Locate the 5 trailing instructions inside `is`.
    have hcode_e_sub : code_at is pc (compile ds c e_sub) :=
      code_at_compile_left
        (tail := [.movi .r9 0, .cmp .rax .r9, .movi .rax 0, .bnz 2, .movi .rax 1])
        (by simpa [compile, List.append_assoc] using hcode)
    have htail_at :
        code_at is (pc + compile_len e_sub)
          [.movi .r9 0, .cmp .rax .r9, .movi .rax 0, .bnz 2, .movi .rax 1] := by
      simpa using
        (code_at_after_compile_prefix
          (pfx := [])
          (mid := [.movi .r9 0, .cmp .rax .r9, .movi .rax 0, .bnz 2, .movi .rax 1])
          (sfx := [])
          (by simpa [compile, List.append_assoc] using hcode))
    have hmovi_r9_at_abs : instr_at is (pc + compile_len e_sub) (.movi .r9 0) :=
      code_at_head htail_at
    have hcmp_at_abs : instr_at is (pc + compile_len e_sub + 1) (.cmp .rax .r9) :=
      code_at_head (code_at_tail htail_at)
    have hmovi_0_at_abs : instr_at is (pc + compile_len e_sub + 2) (.movi .rax 0) :=
      code_at_head (code_at_tail (code_at_tail htail_at))
    have hbnz_at_abs : instr_at is (pc + compile_len e_sub + 3) (.bnz 2) :=
      code_at_head (code_at_tail (code_at_tail (code_at_tail htail_at)))
    -- ! 2) IH on e_sub. `pair_inv` exposes `rax ≥ 1`.
    rcases ih hcode_e_sub hrel hfresh with
      ⟨s1, hs1, ⟨hpc1, hstack1, hrepr1, hext1⟩, hfresh1⟩
    rcases Represents.pair_inv hrepr1 with ⟨_, _, _, _, _, _, hpos1⟩
    -- ! 3) movi r9 0 at s1 → s2.
    let s2 : State :=
      { s1 with
        pc := s1.pc + 1
        regs := Reg.write .r9 0 s1.regs }
    have hmovi_r9' : instr_at is s1.pc (.movi .r9 0) := by
      simpa [hpc1] using hmovi_r9_at_abs
    have hstep_movi_r9 : Step is s1 s2 := Step.movi (s := s1) hmovi_r9'
    -- ! 4) cmp rax r9 at s2 → s3. rax = s1.regs.rax ≥ 1, r9 = 0, so zf = false.
    let s3 : State :=
      { s2 with
        pc := s2.pc + 1
        zf := (Reg.read .rax s2.regs == Reg.read .r9 s2.regs) }
    have hcmp' : instr_at is s2.pc (.cmp .rax .r9) := by
      show instr_at is (s1.pc + 1) (.cmp .rax .r9)
      have hh : (s1.pc + 1 : Nat) = pc + compile_len e_sub + 1 := by rw [hpc1]
      rw [hh]; exact hcmp_at_abs
    have hstep_cmp : Step is s2 s3 := Step.cmp (s := s2) hcmp'
    have hzf3 : s3.zf = false := by
      show (Reg.read .rax s2.regs == Reg.read .r9 s2.regs) = false
      have hr9 : Reg.read .r9 s2.regs = 0 := by
        show (Reg.write .r9 0 s1.regs).r9 = 0
        simp [Reg.write]
      have hax : Reg.read .rax s2.regs = s1.regs.rax := by
        show (Reg.write .r9 0 s1.regs).rax = s1.regs.rax
        simp [Reg.write]
      rw [hax, hr9]
      -- ! rax ≥ 1, so rax ≠ 0, hence (rax == 0) = false.
      have hne : s1.regs.rax ≠ 0 := by
        intro h; rw [h] at hpos1; exact absurd hpos1 (by decide)
      rw [Bool.eq_false_iff]
      intro hbeq
      exact hne (by simpa using hbeq)
    -- ! 5) movi rax 0 at s3 → s4. rax becomes 0.
    let s4 : State :=
      { s3 with
        pc := s3.pc + 1
        regs := Reg.write .rax 0 s3.regs }
    have hmovi_0' : instr_at is s3.pc (.movi .rax 0) := by
      show instr_at is (s2.pc + 1) (.movi .rax 0)
      show instr_at is (s1.pc + 1 + 1) (.movi .rax 0)
      have hh : (s1.pc + 1 + 1 : Nat) = pc + compile_len e_sub + 2 := by rw [hpc1]
      rw [hh]; exact hmovi_0_at_abs
    have hstep_movi_0 : Step is s3 s4 := Step.movi (s := s3) hmovi_0'
    -- ! 6) bnz 2 at s4: zf = false → bnzt → pc += 2 (skips movi rax 1).
    let s5 : State :=
      { s4 with pc := (Int.ofNat s4.pc + 2).toNat }
    have hbnz' : instr_at is s4.pc (.bnz 2) := by
      show instr_at is (s3.pc + 1) (.bnz 2)
      show instr_at is (s2.pc + 1 + 1) (.bnz 2)
      show instr_at is (s1.pc + 1 + 1 + 1) (.bnz 2)
      have hh : (s1.pc + 1 + 1 + 1 : Nat) = pc + compile_len e_sub + 3 := by rw [hpc1]
      rw [hh]; exact hbnz_at_abs
    have hzf4 : s4.zf = false := by
      show s3.zf = false
      exact hzf3
    have hstep_bnz : Step is s4 s5 := Step.bnzt (s := s4) hbnz' hzf4
    -- ! 7) Package: chain s1 → s2 → s3 → s4 → s5.
    refine ⟨s5, ?_, ?_, ?_⟩
    · have h_s1_to_s2 : Steps is s1 s2 := Steps.trans Steps.refl hstep_movi_r9
      have h_s1_to_s3 : Steps is s1 s3 := Steps.trans h_s1_to_s2 hstep_cmp
      have h_s1_to_s4 : Steps is s1 s4 := Steps.trans h_s1_to_s3 hstep_movi_0
      have h_s1_to_s5 : Steps is s1 s5 := Steps.trans h_s1_to_s4 hstep_bnz
      exact Steps.append hs1 h_s1_to_s5
    · refine ⟨?_, ?_, ?_, ?_⟩
      · -- ! pc bookkeeping: s5.pc = s4.pc + 2 = pc + compile_len e_sub + 5.
        -- ! (s4 is reached after 3 instructions past s1: movi/cmp/movi.)
        show s5.pc = pc + compile_len (.is_nil e_sub)
        show (Int.ofNat s4.pc + 2).toNat = pc + compile_len (.is_nil e_sub)
        have hs4pc : s4.pc = pc + compile_len e_sub + 3 := by
          show s3.pc + 1 = _
          show s2.pc + 1 + 1 = _
          show s1.pc + 1 + 1 + 1 = _
          rw [hpc1]
        rw [hs4pc]
        -- ! (Int.ofNat (pc + L + 3) + (2 : Int)).toNat reduces by defeq to
        -- ! `pc + compile_len e_sub + 3 + 2`.
        show pc + compile_len e_sub + 3 + 2 = pc + compile_len (.is_nil e_sub)
        simp [compile_len]; omega
      · -- ! Stack untouched by movi/cmp/movi/bnz.
        show s5.stack = stk ++ k
        show s4.stack = stk ++ k
        show s3.stack = stk ++ k
        show s2.stack = stk ++ k
        show s1.stack = stk ++ k
        exact hstack1
      · -- ! rax = 0 represents .bool false.
        show Represents (.bool false) s5.regs.rax s5.heap
        have hrax5 : s5.regs.rax = 0 := by
          show s4.regs.rax = 0
          show (Reg.write .rax 0 s3.regs).rax = 0
          simp [Reg.write]
        rw [hrax5]
        -- ! `Represents.bool` gives `Represents (.bool b) (if b then 1 else 0) h`.
        have h := Represents.bool (b := false) (h := s5.heap)
        simpa using h
      · -- ! Heap unchanged across all 4 trailing instructions.
        show HeapExtends h s5.heap
        have hheap5 : s5.heap = s1.heap := by
          show s4.heap = s1.heap
          show s3.heap = s1.heap
          show s2.heap = s1.heap
          rfl
        rw [hheap5]
        exact hext1
    · -- ! FreshFrom: heap unchanged, rbx unchanged.
      have hheap5 : s5.heap = s1.heap := by
        show s4.heap = s1.heap
        show s3.heap = s1.heap
        show s2.heap = s1.heap
        rfl
      have hrbx5 : s5.regs.rbx = s1.regs.rbx := by
        show s4.regs.rbx = s1.regs.rbx
        show (Reg.write .rax 0 s3.regs).rbx = s1.regs.rbx
        show s3.regs.rbx = s1.regs.rbx
        show s2.regs.rbx = s1.regs.rbx
        show (Reg.write .r9 0 s1.regs).rbx = s1.regs.rbx
        simp [Reg.write]
      rw [hheap5, hrbx5]
      exact hfresh1



-- ═══════════════════════════════════════════════════════════════════════════
-- SECTION 9 — Whole-program correctness
-- ═══════════════════════════════════════════════════════════════════════════
-- `FinalState` packages up what it means for the whole compiled program to
-- have finished cleanly: the pc points at `halt`, the stack is empty, and
-- `rax` represents the source result `v`. `compile_prog_correct` is the
-- top-level theorem, a corollary of `compiler_correct_general`.

def FinalState (ds : Defns) (e : Expr) (v : Val) (s : State) : Prop :=
  s.pc = compile_defns_len ds + 1 + compile_len e ∧
  instr_at (compile_prog ds e) s.pc .halt ∧
  s.stack = [] ∧
  Represents v s.regs.rax s.heap

-- yunze: initial rbx changed from 0 to 1. The new FreshFrom invariant
-- requires `rbx ≥ 1` at all times, and we establish it at the program
-- entry. This is a visible change to the theorem's public statement.
theorem compile_prog_correct {ds e v}
    (heval : Eval ds [] e v) :
    ∃ s',
      Steps (compile_prog ds e)
        { pc := 0, regs := Reg.write .rbx 1 regs0, stack := [], zf := false, heap := [] } s' ∧
      FinalState ds e v s' := by
  -- ! The compiled whole program is laid out as:
  -- !   [ .jmp (compile_defns_len ds + 1) ]   -- pc 0, the leading jump
  -- !   ++ compile_defns ds                   -- the function-definition block
  -- !   ++ compile ds [] e                    -- the main expression
  -- !   ++ [ .halt ]                          -- final stop
  -- !
  -- ! Plan:
  -- !   (1) Take the leading `jmp`, which moves us from pc = 0 to the start
  -- !       of the main expression code.
  -- !   (2) At that point, the heap and stack are still empty, `Related` is
  -- !       trivially `Related.mt`, and any rbx is fresh from the empty heap.
  -- !   (3) Feed everything to `compiler_correct_general`. It steps the rest
  -- !       of the program and lands us at pc = expr-start + compile_len e —
  -- !       i.e. exactly on the trailing `.halt`.
  -- !   (4) Repackage the resulting state as a `FinalState`.

  -- (1) The leading jump.
  have hjmp : instr_at (compile_prog ds e) 0
      (.jmp ((compile_defns_len ds : Int) + 1)) := by
    -- compile_prog starts with this exact jump as its first instruction.
    simp [compile_prog, instr_at]
    exact get.hd

  let s0 : State :=
    { pc := 0
      regs := Reg.write .rbx 1 regs0
      stack := []
      zf := false
      heap := [] }
  let s1 : State :=
    { s0 with pc := compile_defns_len ds + 1 }
  have hstep_jmp : Steps (compile_prog ds e) s0 s1 := by
    -- `Step.jmp` lands at `(Int.ofNat 0 + (n + 1)).toNat = n + 1`.
    refine Steps.trans Steps.refl ?_
    simpa [s0, s1] using (Step.jmp (s := s0) hjmp)

  -- (2) Build the inputs needed by `compiler_correct_general`.
  have hdefs : defns_in_place (compile_prog ds e) ds :=
    compile_prog_defns_in_place
  have hcode_e : code_at (compile_prog ds e) s1.pc (compile ds [] e) := by
    show code_at (compile_prog ds e) (compile_defns_len ds + 1) (compile ds [] e)
    exact compile_prog_expr_code_at
  have hrel : Related ([] : Stack) ([] : CEnv) ([] : Env) s1.heap :=
    Related.mt
  have hfresh : FreshFrom s1.heap s1.regs.rbx := by
    -- yunze: now need to provide both fields. `pos`: rbx was initialized to 1
    -- and never written before s1. `lookup`: heap is still []; `Heap.lookup []`
    -- is `none` for every address.
    refine ⟨?_, ?_⟩
    · -- pos: s1.regs.rbx = (Reg.write .rbx 1 regs0).rbx = 1 ≥ 1
      show s1.regs.rbx ≥ 1
      show (Reg.write .rbx 1 regs0).rbx ≥ 1
      simp [Reg.write]
    · intro k
      rfl

  -- (3) Run the simulation. We have to pin down every implicit input
  --     (especially `zf`) so that the resulting `Steps` starts at *exactly*
  --     `s1` and can be chained onto `hstep_jmp`.
  rcases compiler_correct_general
      (pc := s1.pc) (stk := ([] : Stack)) (k := ([] : Stack))
      (rs := s1.regs) (zf := false) (h := s1.heap)
      hdefs hcode_e hrel heval hfresh
    with ⟨s', hsteps, hpost, _⟩
  rcases hpost with ⟨hpc', hstack', hrep', _⟩

  -- Normalize the start state of `hsteps` from
  --   { pc := s1.pc, regs := s1.regs, stack := [] ++ [], zf := false, heap := s1.heap }
  -- to literally `s1`, so we can stitch it onto the jump.
  have hsteps_from_s1 : Steps (compile_prog ds e) s1 s' := by
    simpa [s1, s0] using hsteps

  -- (4) Stitch the jump and the simulation together (note: `Steps.append`,
  --     not `Steps.trans` — the latter only chains a single `Step` on the
  --     right). Then discharge the four `FinalState` clauses.
  refine ⟨s', Steps.append hstep_jmp hsteps_from_s1, ?_, ?_, ?_, ?_⟩
  · -- pc-clause: `s'.pc = s1.pc + compile_len e = compile_defns_len ds + 1 + compile_len e`.
    simpa [s1] using hpc'
  · -- halt-clause: the `.halt` we appended lives at exactly that pc.
    -- We construct it via `code_at`-then-`instr_at`.
    have hhalt_code : code_at (compile_prog ds e)
        (compile_defns_len ds + 1 + compile_len e) [.halt] := by
      -- compile_prog = [.jmp ..] ++ compile_defns ds ++ compile ds [] e ++ [.halt]
      refine ⟨[.jmp ((compile_defns_len ds : Int) + 1)] ++ compile_defns ds
                ++ compile ds [] e, [], ?_, ?_⟩
      · simp [compile_prog, List.append_assoc]
      · simp [compile_defns_length, compile_length]
        omega
    have : s'.pc = compile_defns_len ds + 1 + compile_len e := by
      simpa [s1] using hpc'
    rw [this]
    exact code_at_head hhalt_code
  · -- stack-clause: the IH gave `s'.stack = stk ++ k = [] ++ [] = []`.
    simpa using hstack'
  · -- represents-clause: directly from the IH.
    exact hrep'

-- ═══════════════════════════════════════════════════════════════════════════
-- SECTION 10 — Collaboration template (planning notes)
-- ═══════════════════════════════════════════════════════════════════════════
-- Not part of the formal development; just a roadmap for teammates listing
-- the remaining proof obligations and design questions.

-- TODO: I added something here so we can follow this plan largely
-- =========================================================
-- Collaboration Template
-- =========================================================

-- ! Part 1: Finish the current correctness story.
-- ! Goal:
-- ! prove the remaining top-level theorems for the compiler we already have.
--
-- Suggested tasks:
-- - finish `compiler_correct_general`
-- - finish `compile_prog_correct`
-- - add any helper lemmas needed for call / pair / fst / snd cases

-- ! Part 2: Decide how lists should look in the source language.
-- ! Goal:
-- ! choose the list features we want in the final project.
--
-- Possible design questions:
-- - do we want a dedicated list value in `Val`?
-- - do we want to encode lists using `pair` + `bool` + heap cells?
-- - what list expressions do we want?
--   examples: `nil`, `cons`, `head`, `tail`, `isNil`

-- ! Part 3: Extend the syntax and semantics.
-- ! Goal:
-- ! add list syntax and big-step evaluation rules.
--
-- Possible checklist:
-- - add new `Expr` constructors
-- - add new `Val` constructor(s) if needed
-- - add `Eval` rules for every new expression form
-- - write a few `#eval` / example terms if helpful

-- ! Part 4: Extend the compiler.
-- ! Goal:
-- ! compile the new list expressions to machine code.
--
-- Possible checklist:
-- - update `compile_len`
-- - update `compile`
-- - update `compile_defn_len` only if needed
-- - add any new helper machine-code patterns

-- ! Part 5: Extend the representation relation.
-- ! Goal:
-- ! explain how source-level list values live in the heap.
--
-- Possible checklist:
-- - extend `Represents`
-- - add heap lemmas for the chosen list layout
-- - extend `Related` lemmas if necessary
-- - update freshness lemmas if list allocation needs them

-- ! Part 6: Prove correctness for the new list features.
-- ! Goal:
-- ! extend the compiler proof to cover the new syntax.
--
-- Possible checklist:
-- - add new helper lemmas for each list constructor / operation
-- - extend `compiler_correct_general`
-- - derive final corollaries for whole programs

-- ! Part 7: Write the short report.
-- ! Goal:
-- ! explain the design choices and proof strategy in plain language.
--
-- Good report topics:
-- - how values are represented in registers / heap
-- - how lists are represented
-- - what invariant `Related` is capturing
-- - how the proof is organized
-- - what is complete and what remains future work

-- ! Suggested collaborator split.
-- ! Person A:
-- ! focus on the remaining current correctness proofs.
-- ! Person B:
-- ! design and implement the list extension.
-- ! Then both:
-- ! connect the new list cases back into the main proof.

-- ! Handy local TODO format for this file:
-- TODO: short task name
-- TODO: owner?
-- TODO: blocking lemmas?
-- TODO: done?
