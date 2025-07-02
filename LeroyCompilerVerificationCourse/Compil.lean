/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under LGPL 2.1 license as described in the file LICENSE.md.
Authors: Wojciech Różowski
-/

import LeroyCompilerVerificationCourse.Imp

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
  | trans_var : ∀ pc stk s x,
      instr_at C pc = .some (.Ivar x) ->
      transition C (pc    , stk       , s)
                   (pc + 1, s x :: stk, s)
  | trans_setvar: ∀ pc stk s x n,
      instr_at C pc = .some (.Isetvar x) ->
      transition C (pc    , n :: stk, s)
                   (pc + 1, stk     , update x n s)
  | trans_add: ∀ pc stk s n1 n2,
      instr_at C pc = .some (.Iadd) ->
      transition C (pc    , n2 :: n1 :: stk , s)
                   (pc + 1, (n1 + n2) :: stk, s)
  | trans_opp: ∀ pc stk s n,
      instr_at C pc = .some (.Iopp) ->
      transition C (pc    , n :: stk    , s)
                   (pc + 1, (- n) :: stk, s)
  | trans_branch: ∀ pc stk s d pc',
      instr_at C pc = .some (.Ibranch d) ->
      pc' = pc + 1 + d ->
      transition C (pc , stk, s)
                   (pc', stk, s)
  | trans_beq: ∀ pc stk s d1 d0 n1 n2 pc',
      instr_at C pc = .some (.Ibeq d1 d0) ->
      pc' = pc + 1 + (if n1 = n2 then d1 else d0) ->
      transition C (pc , n2 :: n1 :: stk, s)
                   (pc', stk            , s)
  | trans_ble: ∀ pc stk s d1 d0 n1 n2 pc',
      instr_at C pc = .some (.Ible d1 d0) ->
      pc' = pc + 1 + (if n1 ≤ n2 then d1 else d0) ->
      transition C (pc , n2 :: n1 :: stk, s)
                   (pc', stk            , s)

@[grind] def transitions (C: List instr) : config → config → Prop :=
  star (transition C)

def machine_terminates (C: List instr) (s_init: store) (s_final: store) : Prop :=
  ∃ pc, transitions C (0, [], s_init) (pc, [], s_final)
          ∧ instr_at C pc = .some .Ihalt

def machine_diverges (C: List instr) (s_init: store) : Prop :=
  infseq (transition C) (0, [], s_init)

def machine_goes_wrong (C: List instr) (s_init: store) : Prop :=
  ∃ pc stk s,
      transitions C (0, [], s_init) (pc, stk, s)
   ∧ irred (transition C) (pc, stk, s)
   ∧ (instr_at C pc ≠ .some .Ihalt ∨ stk ≠ [])

@[grind] def compile_aexp (a: aexp) : List instr :=
  match a with
  | .CONST n => .Iconst n :: []
  | .VAR x => .Ivar x :: []
  | .PLUS a1 a2  => (compile_aexp a1) ++ (compile_aexp a2) ++ (.Iadd :: [])
  | .MINUS a1 a2 => compile_aexp a1 ++ compile_aexp a2 ++ (.Iopp :: .Iadd :: [])

@[grind] def compile_bexp (b: bexp) (d1: Int) (d0: Int) : List instr :=
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

@[grind] def compile_com (c: com) : List instr:=
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

/-- info: [instr.Ivar "x", instr.Iconst 1, instr.Iadd, instr.Isetvar "x", instr.Ihalt] -/
#guard_msgs in
#eval (compile_program (.ASSIGN "x" (.PLUS (.VAR "x") (.CONST 1))))

def smart_Ibranch (d: Int) : List instr:=
  if d = 0 then [] else .Ibranch d :: []

@[grind] inductive code_at: List instr -> Int -> List instr-> Prop where
  | code_at_intro: ∀ C1 C2 C3 pc,
      pc = codelen C1 ->
      code_at (C1 ++ C2 ++ C3) pc C2

@[grind] theorem codelen_cons:
  ∀ i c, codelen (i :: c) = codelen c + 1 := by grind

@[grind] theorem codelen_singleton : codelen [i] = 1 := by
  dsimp [codelen]

@[grind] theorem codelen_app:
  ∀ c1 c2, codelen (c1 ++ c2) = codelen c1 + codelen c2 := by
    intro c1 _
    induction c1 with grind

@[grind =>] theorem instr_a : ∀ i c2 c1 pc,
  pc = codelen c1 ->
  instr_at (c1 ++ (i :: c2) ) pc = .some i := by
    intro i c2 c1 pc
    induction c1 generalizing pc with grind

@[grind] theorem instr_at_app:
  ∀ i c2 c1 pc,
  pc = codelen c1 ->
  instr_at (c1 ++ (i :: c2)) pc = .some i := by
    intro i c2 c1 pc pc_eq
    induction c1 generalizing pc with grind

theorem code_at_head :
  ∀ C pc i C',
  code_at C pc (i :: C') ->
  instr_at C pc = .some i := by
    intro C pc i C'  H
    generalize heq1 : (i :: C') = x
    rw [heq1] at H
    induction H
    case code_at_intro c1 c2 c3 oc a =>
      unfold instr_at
      induction c1 generalizing oc with grind

@[grind] theorem code_at_tail :
   ∀ C pc i C',
  code_at C pc (i :: C') →
  code_at C (pc + 1) C' := by
    intro C pc i C' h
    cases h
    case code_at_intro c1 c3 a =>
      have s : c1 ++ i :: C' ++ c3 = c1 ++ [i] ++ C' ++ c3 := by grind
      grind

@[grind] theorem code_at_app_left:
  ∀ C pc C1 C2,
  code_at C pc (C1 ++ C2) ->
  code_at C pc C1 := by
    intro c pc m1 m2 h
    cases h
    case code_at_intro c1 c3 a =>
      have := code_at.code_at_intro c1 m1 (m2 ++ c3) pc a
      grind [List.append_assoc]

@[grind] theorem code_at_app_right:
  ∀ C pc C1 C2,
  code_at C pc (C1 ++ C2) ->
  code_at C (pc + codelen C1) C2 := by
    intro C pc c1 c2 h
    cases h
    case code_at_intro b e a =>
      have := code_at.code_at_intro (b ++ c1) c2 e (pc + codelen c1) (by grind)
      grind [List.append_assoc]

@[grind] theorem code_at_app_right2 : ∀ C pc C1 C2 C3,
  code_at C pc (C1 ++ C2 ++ C3) →
  code_at C (pc + codelen C1) C2 := by
    intro C pc c1 c2 c3 h
    cases h
    case code_at_intro b e a =>
      have := code_at.code_at_intro (b ++ c1) c2 (c3 ++ e) (pc + codelen c1) (by grind)
      grind

@[grind] theorem code_at_nil : ∀ C pc C1,
  code_at C pc C1 -> code_at C pc [] := by
    intro C pc c1 h
    cases h
    case code_at_intro b e a =>
      have := code_at.code_at_intro b [] (c1 ++ e) pc a
      grind [List.append_nil, List.append_assoc]

@[grind] theorem instr_at_code_at_nil :
  ∀ C pc i, instr_at C pc = .some i -> code_at C pc [] := by
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
          grind [← code_at.code_at_intro]
      next z =>
        have := code_at.code_at_intro [] [] (f :: t) pc
        grind [List.nil_append]

@[grind] theorem code_at_to_instr_at : code_at C pc (c1 ++ i :: c2) → instr_at C (pc + codelen c1) = .some i := by
    intro h
    cases h
    next b e a =>
      have := instr_at_app i (c2 ++ e) (b ++ c1) (pc + codelen c1) (by simp [codelen]; grind)
      grind [List.append_assoc, List.append_eq]

theorem compile_aexp_correct (C : List instr) (s : store) (a : aexp) (pc : Int) (stk : stack) :
  code_at C pc (compile_aexp a) →
  transitions C (pc, stk, s) (pc + codelen (compile_aexp a), aeval s a :: stk, s) := by
    induction a generalizing C pc stk
    next =>
      simp [aeval, compile_aexp]
      intro a
      unfold transitions
      apply star_one
      apply transition.trans_const
      cases a
      next => grind
    next =>
      simp [aeval, compile_aexp]
      intro a
      apply star_one
      apply transition.trans_var
      cases a
      next => grind
    next a1 a2 a1_ih a2_ih =>
      simp [aeval, compile_aexp]
      intro a
      apply star_trans
      · apply a1_ih
        grind
      · apply star_trans
        · specialize a2_ih C (pc + codelen (compile_aexp a1)) (aeval s a1 :: stk)
          apply a2_ih
          grind
        · apply star_one
          cases a
          next c1 c3 a =>
            have h1 := instr_a instr.Iadd c3 (c1 ++ compile_aexp a1 ++ compile_aexp a2) (pc + codelen (compile_aexp a1) + codelen (compile_aexp a2)) (by grind)
            have h2 := @transition.trans_add ((c1 ++ compile_aexp a1 ++ compile_aexp a2) ++ (instr.Iadd :: c3)) (pc + codelen (compile_aexp a1) + codelen (compile_aexp a2)) stk s (aeval s a1) (aeval s a2) (by grind)
            grind
    next a1 a2 a1_ih a2_ih =>
      simp [aeval, compile_aexp]
      intro a
      apply star_trans
      · apply a1_ih
        grind
      · apply star_trans
        · specialize a2_ih C (pc + codelen (compile_aexp a1)) (aeval s a1 :: stk)
          apply a2_ih
          grind
        · apply star_trans
          · apply star_one
            · have := @transition.trans_opp C (pc + codelen (compile_aexp a1) + codelen (compile_aexp a2)) ((aeval s a1) :: stk) s (aeval s a2)
              apply this
              grind
          · apply star_one
            · have := @code_at_to_instr_at C pc (compile_aexp a1 ++ compile_aexp a2 ++ [instr.Iopp])  instr.Iadd [] (by grind [List.append_assoc, List.cons_append, List.nil_append])
              have := @transition.trans_add C (pc + codelen (compile_aexp a1) + codelen (compile_aexp a2) + 1) stk s (aeval s a1) (-aeval s a2) (by simp [codelen] at *; grind)
              grind
-- Miss 5
theorem compile_bexp_correct (C : List instr) (s : store) (b : bexp) (d1 d0 : Int) (pc : Int) (stk : stack) (h : code_at C pc (compile_bexp b d1 d0))  :
   transitions C
       (pc, stk, s)
       (pc + codelen (compile_bexp b d1 d0) + (if beval s b then d1 else d0), stk, s) := by
    induction b generalizing d1 d0 pc
    next =>
      simp [compile_bexp, beval]
      by_cases d1 = 0
      case pos is_zero =>
        simp [is_zero, codelen]
        apply star.star_refl
      case neg is_not_zero =>
        apply star_one
        simp [is_not_zero, codelen]
        apply transition.trans_branch _ _ _ d1
        · simp [compile_bexp, is_not_zero] at h
          have := @code_at_to_instr_at C pc [] (instr.Ibranch d1) [] (by grind [List.append_assoc, List.nil_append])
          grind
        · grind
    next =>
      simp [compile_bexp, beval]
      by_cases d0 = 0
      case pos is_zero =>
        simp [is_zero, codelen]
        apply star.star_refl
      case neg is_not_zero =>
        apply star_one
        simp [is_not_zero, codelen]
        apply transition.trans_branch _ _ _ d0
        · simp [compile_bexp, is_not_zero] at h
          have := @code_at_to_instr_at C pc [] (instr.Ibranch d0) [] (by grind [List.append_assoc, List.nil_append])
          grind
        · grind
    next a1 a2 =>
      simp [compile_bexp, beval]
      apply star_trans
      · apply compile_aexp_correct
        rotate_left
        · exact a1
        · grind
      · apply star_trans
        · apply compile_aexp_correct
          rotate_right
          · exact a2
          · grind
        · apply star_one
          · apply transition.trans_beq
            rotate_left; rotate_left
            · exact d1
            · exact d0
            · simp [compile_bexp] at h
              grind
            · grind
    next a1 a2 =>
      simp [compile_bexp, beval]
      apply star_trans
      · apply compile_aexp_correct
        rotate_left
        · exact a1
        · grind
      · apply star_trans
        · apply compile_aexp_correct
          rotate_right
          · exact a2
          · grind
        · apply star_one
          · apply transition.trans_ble
            rotate_left; rotate_left
            · exact d1
            · exact d0
            · simp [compile_bexp] at h
              grind
            · grind
    next b1 ih =>
      grind
    next b1 b2 b1_ih b2_ih =>
      generalize heq1 : compile_bexp b2 d1 d0 = code2
      generalize heq2 : compile_bexp b1 0 (codelen code2 + d0) = code1
      unfold compile_bexp
      simp [heq1, heq2]
      apply star_trans
      · apply b1_ih
        rotate_left
        · exact 0
        · exact (codelen code2 + d0)
        · grind
      · by_cases beval s b1 = true
        case pos isTrue =>
          simp [isTrue]
          rw [heq2]
          simp [beval, isTrue]
          specialize b2_ih d1 d0 (pc + codelen code1)
          rw [heq1] at b2_ih
          simp [compile_bexp, heq1, heq2] at h
          specialize b2_ih (by grind)
          simp [codelen_app]
          simp [Int.add_assoc] at *
          exact b2_ih
        case neg isFalse =>
          simp [beval, isFalse]
          rw [heq2]
          simp [codelen_app]
          grind

theorem compile_com_correct_terminating (s s' : store) (c : com) (h₁ : cexec s c s') :
 ∀ C pc stk, code_at C pc (compile_com c) →
  transitions C
      (pc, stk, s)
      (pc + codelen (compile_com c), stk, s') := by
  induction h₁
  case cexec_skip =>
    intro C pc stk h
    unfold compile_com
    dsimp [codelen]
    simp only [Int.add_zero]
    apply star.star_refl
  case cexec_assign s' x a =>
    intro C pc stk h
    unfold compile_com
    apply star_trans
    · apply compile_aexp_correct
      rotate_left
      · exact a
      · unfold compile_com at h
        grind
    · apply star_one
      · have := @transition.trans_setvar C (pc + codelen (compile_aexp a)) stk s x (aeval s a)
        rw [codelen_app, codelen_singleton]
        suffices transition C (pc + codelen (compile_aexp a), aeval s a :: stk, s) (pc + codelen (compile_aexp a) + 1, stk, update x (aeval s a) s) from by grind
        apply this
        grind
  case cexec_seq s'2 c1 s1 c2 s2 cexec1 cexec2 c1_ih c2_ih =>
    intro C pc stk h
    apply star_trans
    · apply c1_ih
      unfold compile_com at h
      apply code_at_app_left
      exact h
    · specialize c2_ih C (pc + codelen (compile_com c1)) stk
      simp [compile_com, codelen_app]
      simp [Int.add_assoc] at c2_ih
      apply c2_ih
      grind
  case cexec_ifthenelse s b c1 c2 s' cexec_h ih =>
    intro C pc stk
    generalize heq1 : compile_com c1 = code1
    generalize heq2 : compile_com c2 = code2
    generalize heq3 : compile_bexp b 0 (codelen code1 + 1) = code3
    simp [compile_com]
    rw [heq1, heq2, heq3]
    intro h
    apply star_trans
    · have := compile_bexp_correct C s b 0 (codelen code1 + 1) pc stk (by grind)
      apply this
    · by_cases beval s b = true
      case pos isTrue =>
        simp [isTrue]
        apply star_trans
        · apply ih
          grind
        · apply star_one
          · apply transition.trans_branch
            rotate_right
            · exact codelen code2
            · grind
            · grind
      case neg isFalse =>
        simp [isFalse]
        rw [heq3]
        specialize ih C (pc + codelen code3 + (codelen code1 + 1)) stk
        simp [isFalse] at ih
        suffices h2 : code_at C (pc + codelen code3 + (codelen code1 + 1)) (compile_com c2) from by
          specialize ih h2
          simp [codelen_app, codelen_cons]
          have : (pc + codelen code3 + (codelen code1 + 1) + codelen (compile_com c2)) = (pc + (codelen code3 + (codelen code1 + (codelen code2 + 1)))) := by grind
          rw [this] at ih
          apply ih
        have := @code_at_app_right C pc (code3 ++ code1 ++ [instr.Ibranch (codelen code2)]) code2 (by simp[h])
        grind
  case cexec_while_done s b c1 isFalse =>
    intro C pc stk h
    generalize heq1 : compile_com c1 = code_body
    generalize heq2 : compile_bexp b 0 (codelen code_body + 1) = code_branch
    generalize heq3 : - (codelen code_branch + codelen code_body + 1) = d
    simp [compile_com]
    rw [heq1, heq2, heq3]
    simp [codelen_app, codelen_singleton]
    apply star_trans
    · apply compile_bexp_correct C s b 0 (codelen code_body + 1) pc stk (by grind)
    · grind
  case cexec_while_loop s b c1 s_intermediate s' isTrue cexec1 cexec2 ih1 ih2 =>
    intro C pc stk
    generalize heq1 : compile_com c1 = code_body
    generalize heq2 : compile_bexp b 0 (codelen code_body + 1) = code_branch
    generalize heq3 : - (codelen code_branch + codelen code_body + 1) = d
    simp [compile_com]
    rw [heq1, heq2, heq3]
    intro h
    apply star_trans
    · apply compile_bexp_correct C s b 0 (codelen code_body + 1) pc stk (by grind)
    · apply star_trans
      · simp [isTrue]
        rw [heq2]
        specialize ih1 C (pc + codelen code_branch) stk
        apply ih1
        grind
      · apply star_trans
        · apply star_one
          apply transition.trans_branch
          rotate_left
          rotate_left
          · exact d
          · exact (pc + codelen code_branch + codelen code_body + 1 + d)
          · grind
          · grind
        · specialize ih2 C (pc + codelen code_branch + codelen code_body + 1 + d) stk
          suffices h2 : code_at C (pc + codelen code_branch + codelen code_body + 1 + d) (compile_com (com.WHILE b c1)) from by
            specialize ih2 h2
            simp [compile_com] at ih2
            rw [heq1, heq2, heq3] at ih2
            simp [codelen_app]
            simp [codelen_app] at ih2

            have : (pc + codelen code_branch + codelen code_body + 1 + d +
      (codelen code_branch + (codelen code_body + codelen [instr.Ibranch d])) ) = (pc + (codelen code_branch + (codelen code_body + codelen [instr.Ibranch d]))) := by grind
            rw [←this]
            apply ih2
          grind

inductive compile_cont (C: List instr) : cont -> Int -> Prop where
  | ccont_stop: ∀ pc,
      instr_at C pc = .some .Ihalt ->
      compile_cont C .Kstop pc
  | ccont_seq: ∀ c k pc pc',
      code_at C pc (compile_com c) ->
      pc' = pc + codelen (compile_com c) ->
      compile_cont C k pc' ->
      compile_cont C (.Kseq c k) pc
  | ccont_while: ∀ b c k pc d pc' pc'',
      instr_at C pc = .some (.Ibranch d) ->
      pc' = pc + 1 + d ->
      code_at C pc' (compile_com (.WHILE b c)) ->
      pc'' = pc' + codelen (compile_com (.WHILE b c)) ->
      compile_cont C k pc'' ->
      compile_cont C (.Kwhile b c k) pc
  | ccont_branch: ∀ d k pc pc',
      instr_at C pc = .some (.Ibranch d) ->
      pc' = pc + 1 + d ->
      compile_cont C k pc' ->
      compile_cont C k pc

inductive match_config (C: List instr): com × cont × store -> config -> Prop where
  | match_config_intro: ∀ c k st pc,
      code_at C pc (compile_com c) ->
      compile_cont C k (pc + codelen (compile_com c)) ->
      match_config C (c, k, st) (pc, [], st)

def com_size (c: com) : Nat :=
  match c with
  | .SKIP => 1
  | .ASSIGN _ _ => 1
  | (c1 ;; c2) => (com_size c1 + com_size c2 + 1)
  | .IFTHENELSE _ c1 c2 => (com_size c1 + com_size c2 + 1)
  | .WHILE _ c1 => (com_size c1 + 1)


theorem com_size_nonzero: ∀ c, (com_size c > 0) := by
  intro c
  fun_induction com_size with grind

def cont_size (k: cont) : Nat :=
  match k with
  | .Kstop => 0
  | .Kseq c k' => (com_size c + cont_size k')
  | .Kwhile _ _ k' => cont_size k'

def measure' (impconf: com × cont × store) : Nat :=
  match impconf with
  | (c, k, _) => (com_size c + cont_size k)

theorem compile_cont_Kstop_inv (C : List instr) (pc : Int) (s : store):
  compile_cont C .Kstop pc →
  ∃ pc',
  star (transition C) (pc, [], s) (pc', [], s)
  ∧ instr_at C pc' = .some .Ihalt := by
    intro H
    generalize h₁ : cont.Kstop = a₁
    generalize h₂ : pc = a₂
    rw [h₁, h₂] at H
    induction H generalizing pc with grind

theorem compile_cont_Kseq_inv (C : List instr) (c : com) (k :cont) (pc : Int) (s : store) (H : compile_cont C (.Kseq c k) pc):
  ∃ pc',
  star (transition C) (pc, [], s) (pc', [], s)
  ∧ code_at C pc' (compile_com c)
  ∧ compile_cont C k (pc' + codelen (compile_com c)) := by
    generalize h₁ : (cont.Kseq c k) = a₁
    generalize h₂ : pc = a₂
    rw [h₁, h₂] at H
    induction H generalizing pc k with grind

theorem compile_cont_Kwhile_inv (C : List instr) (b : bexp) (c : com) (k : cont) (pc : Int) (s : store) (H : compile_cont C (.Kwhile b c k) pc):
  ∃ pc',
  plus (transition C) (pc, [], s) (pc', [], s)
  ∧ code_at C pc' (compile_com (.WHILE b c))
  ∧ compile_cont C k (pc' + codelen (compile_com (.WHILE b c))) := by
    generalize h₁ : (cont.Kwhile b c k) = a₁
    generalize h₂ : pc = a₂
    rw [h₁, h₂] at H
    induction H generalizing pc k
    any_goals grind
    case ccont_branch d k' pc₂ pc₃ h₃ h₄ h₅ ih =>
      specialize ih k pc₃ h₁ rfl
      apply Exists.elim ih
      intro pc₄ ih
      exists pc₄
      apply And.intro
      · rw [h₄] at ih
        rw [←h₂]
        rw [←h₂] at ih
        apply plus.plus_left
        rotate_left
        · apply plus_star
          exact ih.1
        · apply transition.trans_branch
          rotate_left
          · exact rfl
          · grind
      · grind
    case ccont_while b' c' k' pc₂ d pc₃ pc₄ h₃ h₄ h₅ h₆ h₇ ih =>
      exists (pc + 1 + d)
      constructor
      apply plus_one
      apply transition.trans_branch
      rotate_left 2
      · exact d
      any_goals grind

theorem match_config_skip (C : List instr) (k : cont) (s : store) (pc : Int) (H: compile_cont C k pc):
 match_config C (.SKIP, k, s) (pc, [], s) := by
  constructor
  · cases H <;> grind
  · grind

theorem simulation_step:
  ∀ C impconf1 impconf2 machconf1,
  step impconf1 impconf2 ->
  match_config C impconf1 machconf1 ->
  ∃ machconf2,
      (plus (transition C) machconf1 machconf2
       \/ (star (transition C) machconf1 machconf2
           /\ (measure' impconf2 < measure' impconf1)))
   /\ match_config C impconf2 machconf2 := by
    intro C impconf1 impconf2 matchconf1 STEP MATCH
    cases MATCH
    case match_config_intro c k st pc h₁ h₂ =>
      rcases impconf2 with ⟨c' , k', s'⟩
      cases STEP
      next x a =>
        constructor
        constructor
        case h.left =>
          apply Or.intro_left
          apply plus_right
          apply compile_aexp_correct
          rotate_left
          exact a
          rotate_left
          · grind
          · apply transition.trans_setvar
            rotate_left
            exact x
            grind
        apply match_config_skip
        grind
      next c2 =>
        constructor
        constructor
        apply Or.intro_right
        constructor
        apply star.star_refl
        simp [measure', com_size, cont_size]
        grind
        constructor
        simp [compile_com] at h₁
        grind
        apply compile_cont.ccont_seq
        · grind
        rotate_right
        · exact pc + codelen (compile_com c') + codelen (compile_com c2)
        · rfl
        · grind
      next b c1 c2 =>
        generalize h₃ : compile_com c1 = code1
        generalize h₄ : compile_bexp b 0 (codelen code1 + 1) = codeb
        generalize h₅ : compile_com c2 = code2
        simp [compile_com, h₃, h₄, h₅] at h₁ h₂
        constructor
        constructor
        apply Or.intro_right
        constructor
        · apply compile_bexp_correct
          rotate_left
          · exact b
          · exact 0
          · exact (codelen code1 + 1)
          · grind
        · simp [measure', com_size]
          grind
        · rw [h₄]
          constructor
          · by_cases beval st b = true
            case pos isTrue =>
              simp [isTrue] at *
              grind
            case neg isFalse =>
              simp [isFalse] at *
              rw [h₅]
              have := @code_at_app_right C pc (codeb ++ code1 ++ [instr.Ibranch (codelen code2)]) code2 (by grind [List.append_assoc, List.cons_append, List.nil_append])
              simp [codelen_cons, codelen_app] at this
              simp [codelen] at *
              grind
          · by_cases beval st b = true
            case pos isTrue =>
              simp [isTrue] at *
              apply compile_cont.ccont_branch
              rotate_right
              · exact (pc + codelen (codeb ++ (code1 ++ instr.Ibranch (codelen code2) :: code2)))
              rotate_right
              · exact codelen code2
              any_goals grind
            case neg isFalse =>
              simp [isFalse] at *
              grind
      next b c isFalse =>
        generalize h₃ : compile_com c = codec
        generalize h₄ : (compile_bexp b 0 (codelen codec + 1)) = codeb
        constructor
        constructor
        apply Or.intro_right
        constructor
        · apply compile_bexp_correct
          rotate_left
          · exact b
          · exact 0
          · exact (codelen codec + 1)
          · grind
        · simp [measure', com_size]
          fun_induction com_size with grind
        · simp [isFalse]
          rw [h₄]
          simp [compile_com] at h₂ h₁
          rw [h₃, h₄] at h₂ h₁
          constructor
          · grind
          · grind
      next b isTrue =>
        generalize h₃ : compile_com c' = codec
        generalize h₄ : compile_bexp b 0 (codelen codec + 1) = codeb
        constructor
        constructor
        · apply Or.intro_right
          constructor
          · apply compile_bexp_correct
            rotate_left
            · exact b
            · exact 0
            · exact (codelen codec + 1)
            · grind
          · simp [measure', cont_size, com_size]
        · simp [isTrue]
          rw [h₄]
          constructor
          · simp [compile_com] at h₁
            rw [h₃, h₄] at h₁
            grind
          · simp [compile_com, h₃, h₄] at h₁ h₂
            apply compile_cont.ccont_while
            rotate_left 4
            · exact h₂
            · exact (-(codelen codeb + codelen codec + 1))
            rotate_left 3
            · simp [compile_com, h₃, h₄]
              exact h₁
            · grind
            · grind
            · grind
      next =>
        have := compile_cont_Kseq_inv C c' k' pc st (by simp [compile_com, codelen] at h₂; grind)
        apply Exists.elim this
        intro pc'
        intro ⟨w₁, w₂⟩
        exists (pc', [], st)
        constructor
        · apply Or.intro_right
          constructor
          · exact w₁
          · simp [measure', cont_size, com_size]
        · constructor
          · exact w₂.1
          · simp [compile_com, codelen] at h₂
            grind
      next b c =>
        have := compile_cont_Kwhile_inv C b c k' pc st (by simp [compile_com, codelen] at h₂; grind)
        apply Exists.elim this
        intro pc'
        intro ⟨ w₁, w₂ ⟩
        exists (pc', [], st)
        constructor
        · apply Or.intro_left
          · exact w₁
        · constructor
          · exact w₂.1
          · exact w₂.2

theorem simulation_steps:
  ∀ C impconf1 impconf2, star step impconf1 impconf2 ->
  ∀ machconf1, match_config C impconf1 machconf1 ->
  ∃ machconf2,
     star (transition C) machconf1 machconf2
  /\ match_config C impconf2 machconf2 := by
      intro C impconf1 impconf2 STAR machconf1 MATCH
      induction STAR generalizing machconf1
      case star_refl x =>
        exists machconf1
        constructor
        · apply star.star_refl
        · exact MATCH
      case star_step x y z STEP STAR ih =>
        have ⟨ machconf2, steps2, match2 ⟩ := simulation_step C x y machconf1 STEP MATCH
        specialize ih machconf2 match2
        rcases ih with ⟨ machconf3, steps3, match3⟩
        exists machconf3
        have w : star (transition C) machconf1 machconf2 := by
          cases steps2
          case inl h =>
            apply plus_star
            exact h
          case inr h =>
            exact h.1
        constructor
        · apply star_trans
          · exact w
          · exact steps3
        · exact match3

theorem instr_at_len : instr_at (C ++ [i]) (codelen C) = .some i := by
  induction C with grind

theorem match_initial_configs:
  ∀ c s,
  match_config (compile_program c) (c, .Kstop, s) (0, [], s) := by
    intro c s
    generalize heq : compile_com c = C
    constructor
    · simp [compile_program]
      have := code_at.code_at_intro [] C [instr.Ihalt] 0 (by simp [codelen])
      grind [List.nil_append]
    · simp [compile_program, heq]
      constructor
      grind

theorem compile_program_correct_terminating_2:
  ∀ c s s',
  star step (c, .Kstop, s) (.SKIP, .Kstop, s') ->
  machine_terminates (compile_program c) s s' := by
    intro c s s' STAR
    generalize heq : compile_program c = C
    have ⟨ ms, A, B ⟩ := simulation_steps C (c, cont.Kstop, s) (com.SKIP, cont.Kstop, s') STAR (0, [], s) (by grind [match_initial_configs])
    cases B
    case match_config_intro pc w1 w2 =>
      have ⟨pc', D, E ⟩ := compile_cont_Kstop_inv C (pc + codelen (compile_com com.SKIP)) s' w2
      exists pc'
      constructor
      · apply star_trans
        · exact A
        · simp [compile_com, codelen] at D
          exact D
      · exact E

theorem simulation_infseq_inv:
  ∀ C n impconf1 machconf1,
  infseq step impconf1 -> match_config C impconf1 machconf1 ->
  (measure' impconf1 < n) ->
  ∃ impconf2 machconf2,
      infseq step impconf2
   /\ plus (transition C) machconf1 machconf2
   /\ match_config C impconf2 machconf2 := by
    intro C n impconf1 h1 h2 h3 h4
    induction n generalizing impconf1 h1
    case zero => contradiction
    case succ n' ih =>
      rw [infseq] at h2
      rcases h2 with ⟨impconf2 , STEP, INFSEQ⟩
      have ⟨ machconf2, h5 , h6 ⟩ := simulation_step C impconf1 impconf2 h1 STEP h3
      cases h5
      next PLUS =>
        exists impconf2
        exists machconf2
      next w =>
        rcases w with ⟨ STAR, MEASURE ⟩
        specialize ih impconf2 machconf2 INFSEQ h6 (by omega)
        rcases ih with ⟨ c1, m1, w⟩
        exists c1
        exists m1
        constructor
        · exact w.1
        · constructor
          · apply star_plus_trans
            · exact STAR
            · exact w.2.1
          · exact w.2.2

theorem compile_program_correct_diverging:
  ∀ c s,
  infseq step (c, .Kstop, s) ->
  machine_diverges (compile_program c) s := by
    intro c s H
    generalize heq : compile_program c = C
    unfold machine_diverges
    apply infseq_coinduction_principle_2 (fun machconf => ∃ impconf, infseq step impconf /\ match_config C impconf machconf)
    rotate_left
    · exists (c, .Kstop, s)
      constructor
      · exact H
      · have := match_initial_configs c s
        grind
    · intro machconf ⟨ impconf , ⟨INFSEQ, MATCH ⟩⟩
      have ⟨impconf2 , machconf2, INFSEQ2 , PLUS , MATCH2⟩  := simulation_infseq_inv C (measure' impconf +1) impconf machconf INFSEQ MATCH (by omega)
      exists machconf2
      constructor
      · exact PLUS
      · exists impconf2
