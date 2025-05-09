import «Leroy».Sequences

set_option grind.debug true

-- Definition ident := string.

def ident := String deriving BEq

@[grind] inductive aexp : Type where
  | CONST (n : Int)
  | VAR (x : ident)
  | PLUS (a1 : aexp) (a2 : aexp)
  | MINUS (a1 : aexp) (s2 : aexp)

def store : Type := ident → Int

@[grind] def aeval (s : store) (a : aexp) : Int :=
  match a with
  | .CONST n => n
  | .VAR x => s x
  | .PLUS a1 a2 => aeval s a1 + aeval s a2
  | .MINUS a1 a2 => aeval s a1 - aeval s a2


#eval aeval (λ _ => 2) (.PLUS (.VAR "x") (.MINUS (.VAR "x") (.CONST 1)))

theorem aeval_xplus1 : ∀ s x, aeval s (.PLUS (.VAR x) (.CONST 1)) > aeval s (.VAR x) := by
  grind

/-- Finally, we can prove "meta-properties" that hold for all expressions.
    For example: the value of an expression depends only on the values of its
    free variables.

    Free variables are defined by this recursive predicate:
--/

@[grind] def free_in_aexp (x : ident) (a : aexp) : Prop :=
  match a with
  | .CONST _ => False
  | .VAR y => y = x
  | .PLUS a1 a2 | .MINUS a1 a2 => free_in_aexp x a1 ∨ free_in_aexp x a2

theorem aeval_free :
  ∀ s1 s2 a,
  (∀ x, free_in_aexp x a → s1 x = s2 x) →
  aeval s1 a = aeval s2 a := by
    intro s1 s2 a h
    fun_induction aeval
    any_goals grind

inductive bexp : Type :=
  | TRUE                              -- always true
  | FALSE                             -- always false
  | EQUAL (a1: aexp) (a2: aexp)       -- whether [a1 = a2]
  | LESSEQUAL (a1: aexp) (a2: aexp)   -- whether [a1 <= a2]
  | NOT (b1: bexp)                    -- Boolean negation
  | AND (b1: bexp) (b2: bexp)       -- Boolean conjunction
/--
Just like arithmetic expressions evaluate to integers,
  Boolean expressions evaluate to Boolean values [true] or [false].
-/

def NOTEQUAL (a1 a2: aexp) : bexp := .NOT (.EQUAL a1 a2)

def GREATEREQUAL (a1 a2: aexp) : bexp := .LESSEQUAL a2 a1

def GREATER (a1 a2: aexp) : bexp := .NOT (.LESSEQUAL a1 a2)

def LESS (a1 a2: aexp) : bexp := GREATER a2 a1

@[grind] def OR (b1 b2: bexp) : bexp := .NOT (.AND (.NOT b1) (.NOT b2))


@[grind] def beval (s: store) (b: bexp) : Bool :=
  match b with
  | .TRUE => true
  | .FALSE => false
  | .EQUAL a1 a2 => aeval s a1 = aeval s a2
  | .LESSEQUAL a1 a2 => aeval s a1 <= aeval s a2
  | .NOT b1 =>  !(beval s b1)
  | .AND b1 b2 => beval s b1 && beval s b2

theorem beval_OR:
  ∀ s b1 b2, beval s (OR b1 b2) = beval s b1 ∨ beval s b2 := by grind

/--
To complete the definition of the IMP language, here is the
  abstract syntax of commands, also known as statements.
-/

inductive com: Type :=
  | SKIP                                     -- do nothing
  | ASSIGN (x : ident) (a: aexp)              -- assignment: [v := a]
  | SEQ (c1: com) (c2: com)                  -- sequence: [c1; c2]
  | IFTHENELSE (b: bexp) (c1: com) (c2: com) -- conditional: [if b then c1 else c2]
  | WHILE (b: bexp) (c1: com)               --loop: [while b do c1 done]

notation:10 l:10 " ;; " r:11 => com.SEQ l r

#check .SKIP ;; .SKIP

def Euclidean_division :=
  .ASSIGN "r" (.VAR "a") ;;
  .ASSIGN "q" (.CONST 0) ;;
  .WHILE (.LESSEQUAL (.VAR "b") (.VAR "r"))
    (.ASSIGN "r" (.MINUS (.VAR "r") (.VAR "b")) ;;
     .ASSIGN "q" (.PLUS (.VAR "q") (.CONST 1)))

@[grind] def update (x: ident) (v: Int) (s: store) : store :=
  fun y => if x == y then v else s y

@[grind] inductive cexec: store → com → store → Prop where
  | cexec_skip:
      cexec s .SKIP s
  | cexec_assign:
      cexec s (.ASSIGN x a) (update x (aeval s a) s)
  | cexec_seq:
      cexec s c1 s' -> cexec s' c2 s'' ->
      cexec s (.SEQ c1 c2) s''
  | cexec_ifthenelse:
      cexec s (if beval s b then c1 else c2) s' ->
      cexec s (.IFTHENELSE b c1 c2) s'
  | cexec_while_done:
      beval s b = false ->
      cexec s (.WHILE b c) s
  | cexec_while_loop:
      beval s b = true -> cexec s c s' -> cexec s' (.WHILE b c) s'' ->
      cexec s (.WHILE b c) s''

theorem cexec_infinite_loop:
  ∀ s, ¬ ∃ s', cexec s (.WHILE .TRUE .SKIP) s' := by
  intro s h
  apply Exists.elim h
  intro s'
  generalize h : (com.WHILE .TRUE .SKIP) = c
  intro h2
  induction h2
  all_goals grind


@[grind] def cexec_bounded (fuel : Nat) (s : store) (c : com) : Option store :=
  match fuel with
  | .zero => .none
  | .succ fuel' =>
    match c with
    | .SKIP => .some s
    | .ASSIGN x a => .some (update x (aeval s a) s)
    | .SEQ c1 c2 =>
      match cexec_bounded fuel' s c1 with
      | .none => .none
      | .some s' => cexec_bounded fuel' s' c2
    | .IFTHENELSE b c1 c2 =>
      if beval s b then cexec_bounded fuel' s c1 else cexec_bounded fuel' s c2
    | .WHILE b c1 =>
      if beval s b then
        match cexec_bounded fuel' s c1 with
        | .none => .none
        | .some s' => cexec_bounded fuel' s' (.WHILE b c1)
      else
        .some s

theorem cexec_bounded_sound : ∀ fuel s c s',
    cexec_bounded fuel s c = .some s'
  → cexec s c s' := by
  intro fuel
  induction fuel
  any_goals grind
  case succ fuel ih =>
    intro s c
    revert s
    induction c
    any_goals grind

theorem cexec_bounded_complete :
  ∀ s c s', cexec s c s' →
  ∃ fuel1, ∀ fuel, (fuel ≥ fuel1) → cexec_bounded fuel s c = .some s' :=
  by
    intro s c
    revert s
    induction c
    case SKIP =>
      intro s s' h
      apply Exists.intro 1
      intro fuel
      induction fuel
      any_goals grind
    case ASSIGN name aex =>
      intro s s'
      intro h
      apply Exists.intro 1
      intro fuel
      induction fuel
      any_goals grind
    case SEQ c1 c2 c1_ih c2_ih =>
      intro s s' h
      cases h
      case cexec_seq s_intermediate cexec1 cexec2 =>
        have c1_ih := c1_ih s s_intermediate cexec1
        have c2_ih := c2_ih s_intermediate s' cexec2
        apply Exists.elim c1_ih
        intro fuel1 c1_ih
        apply Exists.elim c2_ih
        intro fuel2 c2_ih
        apply Exists.intro (fuel1 + fuel2)
        intro bigger_fuel ineq
        induction ineq
        case refl =>
          induction fuel1
          case zero =>
            have _ := c1_ih 0 (by grind)
            grind
          case succ n1 ih1 =>
            induction fuel2
            case zero =>
              have _ := c2_ih 0 (by grind)
              grind
            case succ n2 ih2 => grind
        case step m ineq ih =>
          simp at ineq
          have _ := c1_ih m (by grind)
          have _ := c2_ih m (by grind)
          grind
    case IFTHENELSE b c1 c2 c1_ih c2_ih =>
      intro s s'
      have t : beval s b = true ∨ beval s b = false := by grind
      intro cexec_ite
      cases cexec_ite
      sorry
    case WHILE => sorry

@[grind] inductive red : com ×store → com × store → Prop where
  | red_assign: ∀ x a s,
      red (.ASSIGN x a, s) (.SKIP, update x (aeval s a) s)
  | red_seq_done: ∀ c s,
      red (.SEQ .SKIP c, s) (c, s)
  | red_seq_step: ∀ c1 c s1 c2 s2,
      red (c1, s1) (c2, s2) →
      red (.SEQ c1 c, s1) (.SEQ c2 c, s2)
  | red_ifthenelse: ∀ b c1 c2 s,
      red (.IFTHENELSE b c1 c2, s) ((if beval s b then c1 else c2), s)
  | red_while_done: ∀ b c s,
      beval s b = false →
      red (.WHILE b c, s) (SKIP, s)
  | red_while_loop: ∀ b c s,
      beval s b = true →
      red (.WHILE b c, s) (.SEQ c (.WHILE b c), s)

theorem red_progress:
  ∀ c s, c = .SKIP ∨ ∃ c', ∃ s', red (c, s) (c', s') := by
    intro c
    induction c
    any_goals grind
    case ASSIGN identifier expression =>
      intro s
      apply Or.intro_right
      apply Exists.intro com.SKIP
      apply Exists.intro (update identifier (aeval s expression) s)
      apply red.red_assign
    case SEQ c1 c2 c1_ih c2_ih =>
      intro s
      apply Or.intro_right
      apply Or.elim (c1_ih s)
      case h.left =>
        intro c1_eq
        rw [c1_eq]
        apply Exists.intro c2
        apply Exists.intro s
        apply red.red_seq_done
      case h.right =>
        intro h
        apply Exists.elim h
        intro c1'
        intro h
        apply Exists.elim h
        intro s'
        intro h
        apply Exists.intro (.SEQ c1' c2)
        apply Exists.intro s'
        grind
    case IFTHENELSE b c1 c2 c1_ih c2_ih =>
      intro s
      apply Or.intro_right
      have h : beval s b = true ∨ beval s b = false := by grind
      apply Or.elim h
      case h.left =>
        intro is_true
        apply Or.elim (c1_ih s)
        case left =>
          intro c1_skip
          apply Exists.intro .SKIP
          apply Exists.intro s
          grind
        case right => grind
      case h.right =>
        intro is_false
        apply Or.elim (c2_ih s)
        case left =>
          intro c2_skip
          apply Exists.intro .SKIP
          apply Exists.intro s
          grind
        case right => grind
    case WHILE b c ih =>
      intro s
      have h : beval s b = true ∨ beval s b = false := by grind
      apply Or.intro_right
      apply Or.elim h
      case left =>
        intro is_true
        apply Or.elim (ih s)
        case left =>
          intro is_skip
          apply Exists.intro (.SEQ .SKIP  (.WHILE b c))
          apply Exists.intro s
          grind
        case right => grind
      case right =>
        intro is_false
        apply Exists.intro .SKIP
        apply Exists.intro s
        grind

def goes_wrong (c: com) (s: store) : Prop := ∃ c', ∃ s', star red (c, s) (c', s') ∧ irred red (c', s') ∧ c' ≠ .SKIP

theorem not_goes_wrong : ∀ c s, ¬(goes_wrong c s) := by
  sorry

theorem red_seq_steps (c2 c c' : com) (s s' : store) : star red (c, s) (c', s') → star red ((c;;c2), s) ((c';;c2), s') := by
  intro H
  generalize h₁ : (c,s) = v₁
  generalize h₂ : (c',s') = v₂
  rw [h₁, h₂] at H
  induction H generalizing c s
  case star_refl =>
    have t₁ : c = c' := by grind
    have t₂ : s = s' := by grind
    rw [←t₁, ←t₂]
    apply star.star_refl
  case star_step x y z a₁ a₂ a_ih =>
    apply star.star_step
    rotate_left
    apply a_ih
    rotate_left
    exact h₂
    exact y.1
    exact y.2
    apply red.red_seq_step
    rw [←h₁] at a₁
    apply a₁
    rfl


theorem red_append_cexec:
  ∀ c1 s1 c2 s2, red (c1, s1) (c2, s2) →
  ∀ s', cexec s2 c2 s' →  cexec s1 c1 s' := by
    intro c1 s1 c2 s2
    intro step
    generalize h₁ : (c1, s1) = prem₁
    generalize h₂ : (c2, s2) = prem₂
    rw [h₁, h₂] at step
    induction step
    any_goals grind
    case red_seq_done c2' intermediate =>
      simp at h₁ h₂
      simp [h₁, h₂]
      intro ending
      intro second_transition
      apply cexec.cexec_seq
      apply cexec.cexec_skip
      apply second_transition
    any_goals sorry
