import LeroyCompilerVerificationCourse.Sequences
import LeroyCompilerVerificationCourse.Imp
import Init.Data.List.Basic
import Std.Data.HashMap
import Std.Data.HashMap.Lemmas
open Classical in
instance [BEq α] [BEq β] [Hashable α] : BEq (Std.HashMap α β) where
  beq m n := Id.run do
    if m.size != n.size then return false
    for e in m do
      match n.get? e.1 with
      | none => return false
      | some v => if e.2 != v then return false
    return true

@[grind] def mk_PLUS_CONST (a: aexp) (n: Int) : aexp :=
  if n = 0 then a else
  match a with
  | .CONST m => .CONST (m + n)
  | .PLUS a (.CONST m) => .PLUS a (.CONST (m + n))
  | _ => .PLUS a (.CONST n)

@[grind] def mk_PLUS (a1 a2: aexp) : aexp :=
  match a1, a2 with
  | .CONST m, _ => mk_PLUS_CONST a2 m
  | _, .CONST m => mk_PLUS_CONST a1 m
  | .PLUS a1 (.CONST m1), .PLUS a2 (.CONST m2) => mk_PLUS_CONST (.PLUS a1 a2) (m1 + m2)
  | .PLUS a1 (.CONST m1), _ => mk_PLUS_CONST (.PLUS a1 a2) m1
  | _, .PLUS a2 (.CONST m2) => mk_PLUS_CONST (.PLUS a1 a2) m2
  | _, _ => .PLUS a1 a2

@[grind] def mk_MINUS (a1 a2: aexp) : aexp :=
  match a1, a2 with
  | _, .CONST m => mk_PLUS_CONST a1 (-m)
  | .PLUS a1 (.CONST m1), .PLUS a2 (.CONST m2) => mk_PLUS_CONST (.MINUS a1 a2) (m1 - m2)
  | .PLUS a1 (.CONST m1), _ => mk_PLUS_CONST (.MINUS a1 a2) m1
  | _, .PLUS a2 (.CONST m2) => mk_PLUS_CONST (.MINUS a1 a2) (-m2)
  | _, _ => .MINUS a1 a2

@[grind] def simplif_aexp (a: aexp) : aexp :=
  match a with
  | .CONST n => .CONST n
  | .VAR x => .VAR x
  | .PLUS a1 a2 => mk_PLUS (simplif_aexp a1) (simplif_aexp a2)
  | .MINUS a1 a2 => mk_MINUS (simplif_aexp a1) (simplif_aexp a2)

/-- info: aexp.MINUS (aexp.VAR "x") (aexp.VAR "y") -/
#guard_msgs in
#eval simplif_aexp (.MINUS (.PLUS (.VAR "x") (.CONST 1)) (.PLUS (.VAR "y") (.CONST 1)))

@[grind] theorem mk_PLUS_CONST_sound:
  forall s a n, aeval s (mk_PLUS_CONST a n) = aeval s a + n := by
    intro s a n
    fun_cases mk_PLUS_CONST a n <;> grind

theorem mk_PLUS_sound:
  forall s a1 a2, aeval s (mk_PLUS a1 a2) = aeval s a1 + aeval s a2 := by
    intro s a1 a2
    fun_cases mk_PLUS a1 a2
    <;> (try (simp [aeval]) ; try (simp [mk_PLUS_CONST_sound ]) ; grind)
    next m _ =>
      grind

theorem mk_MINUS_sound:
  forall s a1 a2, aeval s (mk_MINUS a1 a2) = aeval s a1 - aeval s a2 := by
    intro s a1 a2
    fun_cases mk_MINUS a1 a2 <;> (try (simp [aeval]) ; try (simp [mk_PLUS_CONST_sound ]) ; grind)

theorem simplif_aexp_sound : forall s a, aeval s (simplif_aexp a) = aeval s a := by
  intro s a
  induction a
  any_goals grind [mk_PLUS_sound, mk_MINUS_sound]

@[grind] def mk_EQUAL (a1 a2: aexp) : bexp :=
  match a1, a2 with
  | .CONST n1, .CONST n2 => if n1 = n2 then .TRUE else .FALSE
  | .PLUS a1 (.CONST n1), .CONST n2 => .EQUAL a1 (.CONST (n2 - n1))
  | _, _ => .EQUAL a1 a2

@[grind] def mk_LESSEQUAL (a1 a2: aexp) : bexp :=
  match a1, a2 with
  | .CONST n1, .CONST n2 => if n1 <= n2 then .TRUE else .FALSE
  | .PLUS a1 (.CONST n1), .CONST n2 => .LESSEQUAL a1 (.CONST (n2 - n1))
  | _, _ => .LESSEQUAL a1 a2

@[grind] def mk_NOT (b: bexp) : bexp :=
  match b with
  | .TRUE => .FALSE
  | .FALSE => .TRUE
  | .NOT b => b
  | _ => .NOT b

@[grind] def mk_AND (b1 b2: bexp) : bexp :=
  match b1, b2 with
  | .TRUE, _ => b2
  | _, .TRUE => b1
  | .FALSE, _ => .FALSE
  | _, .FALSE => .FALSE
  | _, _ => .AND b1 b2

theorem mk_EQUAL_sound:
  forall s a1 a2, beval s (mk_EQUAL a1 a2) = (aeval s a1 = aeval s a2) := by
    intro s a1 a2
    fun_cases (mk_EQUAL a1 a2) <;> grind

theorem mk_LESSEQUAL_sound:
  forall s a1 a2, beval s (mk_LESSEQUAL a1 a2) = (aeval s a1 <= aeval s a2) := by
    intro s a1 a2
    fun_cases mk_LESSEQUAL a1 a2 <;> grind

theorem mk_NOT_sound :
  forall s b, beval s (mk_NOT b) = ¬ (beval s b) := by
    intros s b
    fun_cases (mk_NOT b) <;> grind

theorem mk_AND_sound:
  forall s b1 b2, beval s (mk_AND b1 b2) = (beval s b1 ∧ beval s b2) := by
    intro s b1 b2
    fun_cases mk_AND b1 b2
    any_goals grind

@[grind] def mk_IFTHENELSE (b: bexp) (c1 c2: com) : com :=
  match b with
  | .TRUE => c1
  | .FALSE => c2
  | _ => .IFTHENELSE b c1 c2

@[grind] def mk_WHILE (b: bexp) (c: com) : com :=
  match b with
  | .FALSE => .SKIP
  | _ => .WHILE b c

theorem cexec_mk_IFTHENELSE: forall s1 b c1 c2 s2,
  cexec s1 (if beval s1 b then c1 else c2) s2 ->
  cexec s1 (mk_IFTHENELSE b c1 c2) s2 := by
    intro s1 b c1 c2 s2
    fun_cases (mk_IFTHENELSE b c1 c2) <;> grind

theorem cexec_mk_WHILE_done: forall s1 b c,
  beval s1 b = false ->
  cexec s1 (mk_WHILE b c) s1 := by
    intro s1 b c H
    fun_cases mk_WHILE b c <;> grind

theorem cexec_mk_WHILE_loop: forall b c s1 s2 s3,
  beval s1 b = true -> cexec s1 c s2 -> cexec s2 (mk_WHILE b c) s3 ->
  cexec s1 (mk_WHILE b c) s3 := by
    intro b c s1 s2 s3 h1 h2 h3
    fun_cases (mk_WHILE b c) <;> grind

def Store := Std.HashMap ident Int
@[grind] def matches' (s: store) (S: Store): Prop :=
  forall x n, S.get? x = .some n -> s x = n

@[grind] def Le (S1 S2: Store) : Prop :=
  forall x n, S2.get? x = .some n -> S1.get? x = .some n

@[grind] def Top : Store := Std.HashMap.emptyWithCapacity

@[grind] def Join (S1 S2: Store) : Store :=
  S1.filter (fun key _ => S2.get? key == S1.get? key)

-- In leroy's course this is decidable
def Equal (S1 S2: Store) := Std.HashMap.Equiv S1 S2

noncomputable instance : Decidable (Equal S' S) :=
  Classical.propDecidable (Equal S' S)

theorem matches_Le: forall s S1 S2, Le S1 S2 -> matches' s S1 -> matches' s S2 := by
  intro s S1 S2 h1 h2
  grind

theorem Le_Top: forall S, Le S Top := by
  unfold Le Top
  intros
  grind [Std.HashMap]

@[grind] theorem Join_characterization:
forall S1 S2 x n,
  (Join S1 S2).get? x = .some n ↔
  S1.get? x = .some n ∧ S2.get? x = .some n := by
  intro S1 S2 x n
  constructor
  case mpr =>
    grind
  case mp =>
    simp [Join]
    grind

theorem Le_Join_l: forall S1 S2, Le S1 (Join S1 S2) := by intros; grind

theorem  Le_Join_r: forall S1 S2, Le S2 (Join S1 S2) := by intros; grind

theorem Equal_Le: forall S1 S2, Equal S1 S2 -> Le S1 S2 := by
  intro S1 S2 eq
  unfold Equal at eq
  unfold Le
  intro x n
  have := @Std.HashMap.Equiv.getElem?_eq _ _ _ _ S1 S2 _ _ x eq
  grind

@[grind] def lift1 {A B: Type} (f: A -> B) (o: Option A) : Option B :=
  match o with
  | .some x => .some (f x)
  | .none => .none

@[grind] def lift2 {A B C: Type} (f: A -> B -> C) (o1: Option A) (o2: Option B) : Option C :=
  match o1, o2 with
  | .some x1, .some x2 => .some (f x1 x2) | _, _ => .none

@[grind] def Aeval (S: Store) (a: aexp) : Option Int :=
  match a with
  | .CONST n => .some n
  | .VAR x => S.get? x
  | .PLUS a1 a2 => lift2 (Int.add) (Aeval S a1) (Aeval S a2)
  | .MINUS a1 a2 => lift2 (Int.sub) (Aeval S a1) (Aeval S a2)

@[grind] def Beval (S: Store) (b: bexp) : Option Bool :=
  match b with
  | .TRUE => .some true
  | .FALSE => .some false
  | .EQUAL a1 a2 => lift2 (fun m n => m == n) (Aeval S a1) (Aeval S a2)
  | .LESSEQUAL a1 a2 => lift2 (fun m n => m <= n) (Aeval S a1) (Aeval S a2)
  | .NOT b1 => lift1 (fun m => !m) (Beval S b1)
  | .AND b1 b2 => lift2 (fun m n => m && n) (Beval S b1) (Beval S b2)

@[grind] theorem Aeval_sound:
  forall s S, matches' s S ->
  forall a n, Aeval S a = .some n -> aeval s a = n := by
    intro s S h1 a n h2
    induction a generalizing n
    any_goals grind
    case PLUS a1 a2 a1_ih a2_ih =>
      simp [Aeval] at h2
      unfold lift2 at h2
      split at h2 <;> grind
    case MINUS a1 s2 a1_ih a2_ih =>
      simp [Aeval] at h2
      unfold lift2 at h2
      split at h2 <;> grind

theorem Beval_sound:
  forall s S, matches' s S ->
  forall b n, Beval S b = .some n -> beval s b = n := by
    intro s S h1 b n h2
    induction b generalizing n
    any_goals grind
    case EQUAL a1 a2 =>
      unfold Beval at h2
      unfold lift2 at h2
      split at h2
      any_goals grind
    case LESSEQUAL a1 a2 =>
      unfold Beval at h2
      unfold lift2 at h2
      split at h2 <;> grind
    case NOT a1 a1_ih =>
      unfold Beval at h2
      unfold lift1 at h2
      split at h2 <;> grind
    case AND a1 a2 =>
      unfold Beval at h2
      unfold lift2 at h2
      split at h2 <;> grind


@[grind] def Update (x: ident) (N: Option Int) (S: Store) : Store :=
  match N with
  | .none => S.erase x
  | .some n => S.insert x n

@[grind] theorem update_characterisation : forall S x N y,
  (Update x N S).get? y = if x == y then N else S.get? y := by
    intro S x N y
    simp
    split
    case isTrue eq =>
      simp at eq
      rw [eq]
      unfold Update
      grind
    case isFalse neq =>
      simp at neq
      unfold Update
      grind

theorem matches_update: forall s S x n N,
  matches' s S ->
  (forall i, N = .some i -> n = i) ->
  matches' (update x n s) (Update x N S) := by
    intro s S x n N m h
    grind

@[grind] noncomputable def fixpoint_rec (F: Store -> Store) (fuel: Nat) (S: Store) : Store :=
  match fuel with
  | 0 => Top
  | fuel + 1 =>
      let S' := F S
      if Equal S' S then S else fixpoint_rec F fuel S'

@[grind] def num_iter : Nat := 20

@[grind] noncomputable def fixpoint (F: Store -> Store) (init_S: Store) : Store :=
  fixpoint_rec F num_iter init_S

theorem fixpoint_sound (F : Store → Store) (init_S : Store) (h : S = fixpoint F init_S) :
  Le (F S) S := by
    have A : forall fuel S,
             fixpoint_rec F fuel S = Top
             \/ Equal (F (fixpoint_rec F fuel S)) (fixpoint_rec F fuel S) := by
      intro fuel
      induction fuel
      case zero => grind
      case succ fuel' ih  =>
        grind
    have E : S = Top \/ Equal (F S) S = true := by grind
    cases E <;> grind [Equal_Le]


@[grind] noncomputable def Cexec (S: Store) (c: com) : Store :=
  match c with
  | .SKIP => S
  | .ASSIGN x a => Update x (Aeval S a) S
  | .SEQ c1 c2 => Cexec (Cexec S c1) c2
  | .IFTHENELSE b c1 c2 =>
      match Beval S b with
      | .some true => Cexec S c1
      | .some false => Cexec S c2
      | .none => Join (Cexec S c1) (Cexec S c2)
  | .WHILE _ c1 =>
      fixpoint (fun x => Join S (Cexec x c1)) S

@[grind] theorem Cexec_sound:
  forall c s1 s2 S1,
  cexec s1 c s2 -> matches' s1 S1 -> matches' s2 (Cexec S1 c) := by
    intro c
    induction c
    next =>
      intro s1 s2 S1 EXEC
      cases EXEC
      grind
    next x a =>
      intro s1 s2 S1 EXEC
      cases EXEC
      grind
    next c1 c2 c1_ih c2_ih =>
      grind
    next b c1 c2 c1_ih c2_ih =>
      intro s1 s2 S1 EXEC
      cases EXEC
      next EXEC =>
        by_cases beval s1 b
        case pos h =>
          unfold Cexec
          intro h2
          have := Beval_sound s1 S1 h2 b
          split <;> grind
        case neg h =>
          simp [h] at EXEC
          intro h2
          unfold Cexec
          have := Beval_sound s1 S1 h2 b
          split <;> grind
    case WHILE b c c1_ih =>
      intro s1 s2 S1 EXEC MATCHES
      generalize eq1 : (fun x => Join S1 (Cexec x c)) = F
      generalize eq2 : fixpoint F S1 = X
      have INNER : forall s1 c1 s2,
                 cexec s1 c1 s2 ->
                 c1 = .WHILE b c ->
                 matches' s1 X ->
                 matches' s2 X := by
                  intro s3 c1 s4 EXEC2 EQ AG
                  induction EXEC2
                  any_goals grind
                  case cexec_while_loop s' b' c' s5 s6 EXEC2 EXEC3 EXEC4 _ a_ih2 =>
                    apply a_ih2
                    . grind
                    . apply matches_Le
                      rotate_right
                      . exact F X
                      . exact @fixpoint_sound X F S1 (by grind)
                      . rw [←eq2, ←eq1]
                        simp
                        apply matches_Le
                        apply Le_Join_r
                        rw [eq1, eq2]
                        apply c1_ih
                        injections EQ
                        rename_i eq1 eq2
                        rw [eq2] at EXEC3
                        exact EXEC3
                        exact AG
      unfold Cexec
      rw [eq1, eq2]
      apply INNER
      . apply EXEC
      . rfl
      . apply matches_Le
        have := @fixpoint_sound X F
        apply this
        rotate_left
        . exact S1
        rotate_left
        . grind
        . rw [←eq1]
          simp
          apply matches_Le
          . apply Le_Join_l
          . exact MATCHES

@[grind] def cp_aexp (S: Store) (a: aexp) : aexp :=
  match a with
  | .CONST n => .CONST n
  | .VAR x => match S.get? x with
    | .some n => .CONST n
    | .none => .VAR x
  | .PLUS a1 a2 => mk_PLUS (cp_aexp S a1) (cp_aexp S a2)
  | .MINUS a1 a2 => mk_MINUS (cp_aexp S a1) (cp_aexp S a2)


@[grind] def cp_bexp (S: Store) (b: bexp) : bexp :=
  match b with
  | .TRUE => .TRUE
  | .FALSE => .FALSE
  | .EQUAL a1 a2 => mk_EQUAL (cp_aexp S a1) (cp_aexp S a2)
  | .LESSEQUAL a1 a2 => mk_LESSEQUAL (cp_aexp S a1) (cp_aexp S a2)
  | .NOT b => mk_NOT (cp_bexp S b)
  | .AND b1 b2 => mk_AND (cp_bexp S b1) (cp_bexp S b2)

@[grind] theorem cp_aexp_sound:
  forall s S, matches' s S ->
  forall a, aeval s (cp_aexp S a) = aeval s a := by
    intro s S AG a
    induction a <;> grind [mk_PLUS_sound, mk_MINUS_sound]

theorem cp_bexp_sound:
  forall s S, matches' s S ->
  forall b, beval s (cp_bexp S b) = beval s b := by
    intro s S AG b
    induction b
    any_goals grind [mk_EQUAL_sound, mk_LESSEQUAL_sound, mk_AND_sound, mk_NOT_sound]

@[grind] noncomputable def cp_com (S: Store) (c: com) : com :=
  match c with
  | .SKIP => .SKIP
  | .ASSIGN x a =>
      .ASSIGN x (cp_aexp S a)
  | .SEQ c1 c2 =>
      .SEQ (cp_com S c1) (cp_com (Cexec S c1) c2)
  | .IFTHENELSE b c1 c2 =>
      mk_IFTHENELSE (cp_bexp S b) (cp_com S c1) (cp_com S c2)
  | .WHILE b c =>
      let sfix := Cexec S (.WHILE b c)
      mk_WHILE (cp_bexp sfix b) (cp_com sfix c)

theorem cp_com_correct_terminating:
  forall c s1 s2 S1,
  cexec s1 c s2 -> matches' s1 S1 -> cexec s1 (cp_com S1 c) s2 := by
    intro c s1 s2 S1 EXEC AG
    induction c generalizing s1 s2 S1
    any_goals grind
    case ASSIGN x a =>
      cases EXEC
      next =>
        simp [cp_com]
        have := @cexec.cexec_assign s1 x (cp_aexp S1 a)
        grind
    case IFTHENELSE b c1 c2 c1_ih c2_ih =>
      cases EXEC
      next =>
        apply cexec_mk_IFTHENELSE
        grind [cp_bexp_sound]
    case WHILE b c c_ih =>
      generalize heq1 : com.WHILE b c = loop
      generalize heq2 : Cexec S1 (.WHILE b c) = X
      have INNER: forall s1 c1 s2,
                 cexec s1 c1 s2 ->
                 c1 = .WHILE b c ->
                 matches' s1 X ->
                 cexec s1 (mk_WHILE (cp_bexp X b) (cp_com X c)) s2 := by
                  intro s1 c1
                  induction c1 generalizing s1 c
                  any_goals grind
                  case WHILE b1 c1 c1_ih  =>
                    intro s2 EXEC EQ AG1
                    injections heq1' heq2'
                    generalize heq : (com.WHILE b1 c1) = loop
                    rw [heq] at EXEC
                    induction EXEC
                    any_goals grind
                    case cexec_while_done isFalse =>
                      apply cexec_mk_WHILE_done
                      . grind [cp_bexp_sound]
                    case cexec_while_loop s3 b' c' s4 s5 isTrue EXEC2 EXEC3 a_ih a_ih2 =>
                      apply cexec_mk_WHILE_loop
                      . grind [cp_bexp_sound]
                      . apply c_ih
                        . injections heq4 heq5
                          rw [heq2'] at heq5
                          rw [←heq5] at EXEC2
                          exact EXEC2
                        . exact AG1
                      . apply a_ih2
                        rotate_left
                        . grind
                        . apply matches_Le
                          rw [←heq2]
                          simp [Cexec]
                          apply fixpoint_sound
                          rotate_left
                          . exact (fun x => Join S1 (Cexec x c))
                          . exact S1
                          rotate_left
                          . grind
                          . apply matches_Le
                            . apply Le_Join_r
                            . apply Cexec_sound
                              . rw [←heq2']
                                injections heq3 heq4
                                rw [heq4]
                                exact EXEC2
                              . grind
      rw [heq1] at EXEC
      induction EXEC
      any_goals grind
      case cexec_while_loop s3 b' c' s4 s5 isTrue EXEC1 EXEC2 ih1 ih2 =>
        injections heq3 heq4
        simp [cp_com]
        specialize INNER s3 (.WHILE b' c') s5
        rw [←heq3, ←heq4, heq2]
        apply INNER
        any_goals grind
        . rw [←heq2]
          simp [Cexec]
          apply matches_Le
          . apply fixpoint_sound
            rotate_left
            . exact (fun x => Join S1 (Cexec x c))
            . exact S1
            . grind
          . grind
