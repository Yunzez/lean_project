
-- A little register + stack + heap machine semantics

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


-- syntax and semantics

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

inductive Defn where
  | defn (f x : Var) (e : Expr)

inductive Val where
  | int (i : Int) : Val
  | bool (b : Bool) : Val
  | pair (v1 v2 : Val) : Val

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


-- compiler

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

-- proof

inductive Represents : Val -> Int -> Heap -> Prop where
  | int {i h} : Represents (.int i) i h
  | bool {b h} : Represents (.bool b) (if b then 1 else 0) h
  | pair {v1 i1 h v2 i2 i} :
    Represents v1 i1 h ->
    Represents v2 i2 h ->
    Heap.lookup h (i+0) = i1 ->
    Heap.lookup h (i+1) = i2 ->
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

def FreshFrom (h : Heap) (a : Int) : Prop :=
  ∀ k : Nat, Heap.lookup h (a + k) = none

theorem exists_freshFrom (h : Heap) :
  ∃ a : Int, FreshFrom h a := by
  let M : Nat := maxAbsIntList (dom h)
  refine ⟨Int.ofNat (M + 1), ?_⟩
  intro k
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
  | pair h1 h2 hlook1 hlook2 ih1 ih2 =>
    exact .pair (ih1 hext) (ih2 hext) (hext _ _ hlook1) (hext _ _ hlook2)

theorem Represents.bool_inv {b i h} :
  Represents (.bool b) i h ->
  i = if b then 1 else 0 := by
  intro hrep
  cases hrep with
  | bool =>
      rfl

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

theorem ext_lookup_of_ne {h : Heap} {a b i : Int} (hba : b ≠ a) :
  Heap.lookup (Heap.ext h a i) b = Heap.lookup h b := by
  simp [Heap.lookup, Heap.ext, hba]

-- ! If `a` was fresh before, then after writing at `a` and `a+1`,
-- ! everything from `a+2` onward is still fresh.
theorem FreshFrom.step {h : Heap} {a i1 i2 : Int} :
  FreshFrom h a ->
  FreshFrom ((h.ext (a + 1) i2).ext a i1) (a + 2) := by
  intro hfresh
  intro k
  -- ? Expand the two heap writes and check the queried address is not `a`.
  have hne1 : a + 2 + k ≠ a := by
    omega
  -- ? Check it is also not `a + 1`.
  have hne2 : a + 2 + k ≠ a + 1 := by
    omega
  rw [ext_lookup_of_ne hne1, ext_lookup_of_ne hne2]
  -- ? Now we can use the original freshness from `a`.
  have := hfresh (k + 2)
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
  sorry







def FinalState (ds : Defns) (e : Expr) (v : Val) (s : State) : Prop :=
  s.pc = compile_defns_len ds + 1 + compile_len e ∧
  instr_at (compile_prog ds e) s.pc .halt ∧
  s.stack = [] ∧
  Represents v s.regs.rax s.heap

theorem compile_prog_correct {ds e v}
    (heval : Eval ds [] e v) :
    ∃ s',
      Steps (compile_prog ds e)
        { pc := 0, regs := Reg.write .rbx 0 regs0, stack := [], zf := false, heap := [] } s' ∧
      FinalState ds e v s' := by
  -- ! This final theorem follows from the general compiler correctness theorem above.
  -- ! It connects the compiled whole program to the expected halted final state.
  -- you don't need to prove this, but it is provable from the general theorem above
  sorry

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
