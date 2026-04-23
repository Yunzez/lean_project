

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
  stack : List Int
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

mutual
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
    | none => []
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
    match Defns.entry ds f with
    | none => []
    | some i =>
      compile ds c e ++
      [.movpc .r9,
      .addi .r9 5,
      .push .r9,
      .push .rax,
      .movi .r9 i,
      .jmpabs .r9]

def compile_defns (ds : Defns) (ds' : Defns): List Instr :=
  match ds' with
  | [] => []
  | (d :: ds') =>  compile_defn ds d ++ compile_defns ds ds'

def compile_defn (ds : Defns) (d : Defn) : List Instr :=
  match d with
  | .defn _ x e =>
    compile ds [some x] e ++
    [.pop .r9, -- discard argument
     .pop .r9, -- pop return pointer
     .jmpabs .r9]

def go (ds : Defns) (f : Var) (ds' : Defns) (pc : Nat) :=
  match ds' with
  | [] => none
  | (.defn g x e) :: ds'' =>
    if f = g then
      some pc
    else
      go ds f ds'' (pc + (compile_defn ds (.defn g x e)).length)

def Defns.entry (ds : Defns) (f : Var) : Option Nat :=
  go ds f ds 1
end

def compile_prog (ds : Defns) (e : Expr) : List Instr :=
  let ids := compile_defns ds ds
  [.jmp (ids.length + 1)] ++ ids ++ compile ds [] e ++ [.halt]
