import «Leroy».Sequences
import «Leroy».Imp
import Init.Data.List.Basic

set_option grind.warning false

@[grind] inductive instr : Type where
  | Iconst (n: Int)
  | Ivar (x: ident)
  | Isetvar (x: ident)
  | Iadd
  | Iopp
  | Ibranch (d: Int)
  | Ibeq (d1: Int) (d0: Int)
  | Ible (d1: Int) (d0: Int)
  | Ihalt
    deriving Repr

@[grind] def codelen (c: List instr) : Int := c.length

def stack : Type := List Int

def config : Type := Int × stack × store

@[grind] def instr_at (C : List instr) (pc : Int) : Option instr :=
  match C with
  | [] => .none
  | i :: C' => if pc = 0 then .some i else instr_at C' (pc - 1)

@[grind] inductive transition (C: List instr): config → config → Prop where
  | trans_const : ∀ pc stk s n,
      instr_at C pc = .some (.Iconst n) →
      transition C (pc    , stk     , s)
                   (pc + 1, n :: stk, s)
  | trans_var : forall pc stk s x,
      instr_at C pc = .some (.Ivar x) ->
      transition C (pc    , stk       , s)
                   (pc + 1, s x :: stk, s)
  | trans_setvar: forall pc stk s x n,
      instr_at C pc = .some (.Isetvar x) ->
      transition C (pc    , n :: stk, s)
                   (pc + 1, stk     , update x n s)
  | trans_add: forall pc stk s n1 n2,
      instr_at C pc = .some (.Iadd) ->
      transition C (pc    , n2 :: n1 :: stk , s)
                   (pc + 1, (n1 + n2) :: stk, s)
  | trans_opp: forall pc stk s n,
      instr_at C pc = .some (.Iopp) ->
      transition C (pc    , n :: stk    , s)
                   (pc + 1, (- n) :: stk, s)
  | trans_branch: forall pc stk s d pc',
      instr_at C pc = .some (.Ibranch d) ->
      pc' = pc + 1 + d ->
      transition C (pc , stk, s)
                   (pc', stk, s)
  | trans_beq: forall pc stk s d1 d0 n1 n2 pc',
      instr_at C pc = .some (.Ibeq d1 d0) ->
      pc' = pc + 1 + (if n1 = n2 then d1 else d0) ->
      transition C (pc , n2 :: n1 :: stk, s)
                   (pc', stk            , s)
  | trans_ble: forall pc stk s d1 d0 n1 n2 pc',
      instr_at C pc = .some (.Ible d1 d0) ->
      pc' = pc + 1 + (if n1 ≤ n2 then d1 else d0) ->
      transition C (pc , n2 :: n1 :: stk, s)
                   (pc', stk            , s)

def transitions (C: List instr) : config -> config -> Prop :=
  star (transition C)

def machine_terminates (C: List instr) (s_init: store) (s_final: store) : Prop :=
  exists pc, transitions C (0, [], s_init) (pc, [], s_final)
          ∧ instr_at C pc = .some .Ihalt

def machine_goes_wrong (C: List instr) (s_init: store) : Prop :=
  exists pc stk s,
      transitions C (0, [], s_init) (pc, stk, s)
   ∧ irred (transition C) (pc, stk, s)
   ∧ (instr_at C pc ≠ .some .Ihalt ∨ stk ≠ [])

def compile_aexp (a: aexp) : List instr :=
  match a with
  | .CONST n => .Iconst n :: []
  | .VAR x => .Ivar x :: []
  | .PLUS a1 a2  => (compile_aexp a1) ++ (compile_aexp a2) ++ (.Iadd :: [])
  | .MINUS a1 a2 => compile_aexp a1 ++ compile_aexp a2 ++ (.Iopp :: .Iadd :: [])

def compile_bexp (b: bexp) (d1: Int) (d0: Int) : List instr :=
  match b with
  | .TRUE => if d1 = 0 then [] else .Ibranch d1 :: []
  | .FALSE => if d0 = 0 then [] else .Ibranch d0 :: []
  | .EQUAL a1 a2 => compile_aexp a1 ++ compile_aexp a2 ++ .Ibeq d1 d0 :: []
  | .LESSEQUAL a1 a2 => compile_aexp a1 ++ compile_aexp a2 ++ .Ible d1 d0 :: []
  | .NOT b1 => compile_bexp b1 d0 d1
  | .AND b1 b2 =>
      let code2 := compile_bexp b2 d1 d0
      let code1 := compile_bexp b1 0 (codelen code2 + d0)
      code1 ++ code2

def compile_com (c: com) : List instr:=
  match c with
  | .SKIP =>
      []
  | .ASSIGN x a =>
      compile_aexp a ++ .Isetvar x :: []
  | .SEQ c1 c2 =>
      compile_com c1 ++ compile_com c2
  | .IFTHENELSE b ifso ifnot =>
      let code_ifso := compile_com ifso
      let code_ifnot := compile_com ifnot
      compile_bexp b 0 (codelen code_ifso + 1)
      ++ code_ifso
      ++ .Ibranch (codelen code_ifnot)
      :: code_ifnot
  | .WHILE b body =>
      let code_body := compile_com body
      let code_test := compile_bexp b 0 (codelen code_body + 1)
      code_test
      ++ code_body
      ++ .Ibranch (- (codelen code_test + codelen code_body + 1)) :: []

def compile_program (p: com) : List instr:=
  compile_com p ++ .Ihalt :: []

#eval (compile_program (.ASSIGN "x" (.PLUS (.VAR "x") (.CONST 1))))

def smart_Ibranch (d: Int) : List instr:=
  if d = 0 then [] else .Ibranch d :: []

@[grind] inductive code_at: List instr-> Int -> List instr-> Prop where
  | code_at_intro: forall C1 C2 C3 pc,
      pc = codelen C1 ->
      code_at (C1 ++ C2 ++ C3) pc C2

theorem codelen_cons:
  forall i c, codelen (i :: c) = codelen c + 1 := by grind

theorem codelen_app:
  forall c1 c2, codelen (c1 ++ c2) = codelen c1 + codelen c2 := by
    intro c1 c2
    induction c1
    all_goals grind

theorem instr_a : forall i c2 c1 pc,
  pc = codelen c1 ->
  instr_at (c1.append (i :: c2) ) pc = .some i := by
    intro i c2 c1 pc
    induction c1 generalizing pc
    case nil =>
      dsimp [instr_at, codelen]
      grind
    case cons h t ih =>
      dsimp [codelen, instr_at]
      intro h1
      split
      all_goals grind [List.append_eq]

@[grind] theorem instr_at_app:
  ∀ i c2 c1 pc,
  pc = codelen c1 ->
  instr_at (c1.append (i :: c2)) pc = .some i := by
    intro i c2 c1 pc pc_eq
    induction c1 generalizing pc
    case nil =>
      dsimp [instr_at]
      dsimp [codelen] at pc_eq
      grind
    case cons h t t_ih =>
      grind [instr_at, codelen, List.append_eq]

theorem code_at_head :
  forall C pc i C',
  code_at C pc (i :: C') ->
  instr_at C pc = .some i := by
    intro C pc i C'  H
    generalize heq1 : (i :: C') = x
    rw [heq1] at H
    induction H
    case code_at_intro c1 c2 c3 oc a =>
      unfold instr_at
      rw [←heq1]
      induction c1 generalizing oc
      case nil =>
        grind
      case cons h t t_ih =>
        have _ : oc ≠ 0 := by grind
        have _ : t ++ i :: (C' ++ c3) ≠ [] := by grind
        dsimp
        grind

theorem code_at_tail :
   forall C pc i C',
  code_at C pc (i :: C') →
  code_at C (pc + 1) C' := by
    intro C pc i C' h
    cases h
    case code_at_intro c1 c3 a =>
      have s : c1 ++ i :: C' ++ c3 = c1 ++ [i] ++ C' ++ c3 := by grind [List.append_cons]
      rw [s]
      apply code_at.code_at_intro
      grind

theorem code_at_app_left:
  forall C pc C1 C2,
  code_at C pc (C1 ++ C2) ->
  code_at C pc C1 := by
    intro c pc m1 m2 h
    cases h
    case code_at_intro c1 c3 a =>
      have := code_at.code_at_intro c1 m1 (m2 ++ c3) pc a
      grind [List.append_assoc]

theorem code_at_app_right:
  forall C pc C1 C2,
  code_at C pc (C1 ++ C2) ->
  code_at C (pc + codelen C1) C2 := by
    intro C pc c1 c2 h
    cases h
    case code_at_intro b e a =>
      have := code_at.code_at_intro (b ++ c1) c2 e (pc + codelen c1) (by grind)
      grind [List.append_assoc]

theorem code_at_app_right2 : forall C pc C1 C2 C3,
  code_at C pc (C1 ++ C2 ++ C3) →
  code_at C (pc + codelen C1) C2 := by
    intro C pc c1 c2 c3 h
    cases h
    case code_at_intro b e a =>
      have := code_at.code_at_intro (b ++ c1) c2 (c3 ++ e) (pc + codelen c1) (by grind)
      grind [List.append_assoc]

theorem code_at_nil : forall C pc C1,
  code_at C pc C1 -> code_at C pc [] := by
    intro C pc c1 h
    cases h
    case code_at_intro b e a =>
      have := code_at.code_at_intro b [] (c1 ++ e) pc a
      grind [List.append_nil, List.append_assoc]

theorem instr_at_code_at_nil :
  forall C pc i, instr_at C pc = .some i -> code_at C pc [] := by
    intro C pc i h
    induction C generalizing pc i
    case nil => grind
    case cons f t t_ih =>
      unfold instr_at at h
      by_cases pc = 0
      rotate_left
      next nz =>
        simp [nz] at h
        specialize t_ih (pc - 1) i h
        cases t_ih
        next c1 c3 a =>
          simp
          have := code_at.code_at_intro (f :: c1) [] c3 pc
          grind
      next z =>
        have := code_at.code_at_intro [] [] (f :: t) pc
        grind [List.nil_append]
