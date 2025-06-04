set_option grind.warning false

universe u

@[grind] class OrderStruct (α : Sort u) where
  eq : α → α → Prop
  le : α → α → Prop
  beq : α → α → Bool
  beq_true : ∀ x y : α, beq x y = true → eq x y
  beq_false : ∀ x y : α, beq x y = false → ¬ eq x y
  bot : α
  bot_smallest : ∀ x, le bot x
  F : α → α
  F_mon: ∀ x y, le x y -> le (F x) (F y)
  le_trans: ∀ x y z, le x y -> le y z -> le x z
open OrderStruct

@[grind] def gt {α : Sort u} [OrderStruct α] (x y : α ) := le y x ∧ ¬eq y x

@[grind] class WellFoundedOrderStruct (α : Sort u) extends OrderStruct α where
  gt_wf : WellFounded (@gt α _)

variable ( α : Sort u ) [inst:  WellFoundedOrderStruct α]
open WellFoundedOrderStruct

instance : WellFoundedRelation α  where
  rel := gt
  wf := gt_wf

theorem fixpoint_exists_1: ∃ x : α, eq x (F x) := by
  have REC : forall x : α, le x (F x) -> exists y : α , eq y (F y) := by
    intro x
    induction x using @WellFounded.induction α gt gt_wf
    case h x ih =>
      intro h
      by_cases (beq x (F x))
      case pos isTrue =>
        exists x
        grind [OrderStruct.beq_true]
      case neg isFalse =>
        specialize ih (F x)
        grind [OrderStruct.beq_false, gt, OrderStruct.F_mon]
  specialize REC bot
  apply REC
  apply bot_smallest

@[grind] def iterate (x : α) (PRE: le x (F x)) (SMALL: forall z, le (F z) z -> le x z) : α :=
  if beq x (F x) then x else iterate (F x) (by apply OrderStruct.F_mon; exact PRE) (by intro z hyp; specialize SMALL z hyp; apply le_trans; apply F_mon; exact SMALL; exact hyp)
termination_by x
decreasing_by
  rename_i h
  unfold gt
  grind [OrderStruct.beq_false]

@[grind] theorem iterate_correct (x : α) (PRE: le x (F x)) (SMALL: forall z, le (F z) z -> le x z) (heq : y = iterate _ x PRE SMALL ) : eq y (F y) ∧ ∀ z, le (F z) z → le y z := by
  fun_induction iterate
  case case1 x' PRE SMALL isTrue  =>
    constructor
    . rw [←heq] at PRE
      grind [OrderStruct.beq_true]
    . intro z hyp
      specialize SMALL z hyp
      grind
  case case2 ih =>
    have := @ih heq
    grind

@[grind] def fixpoint : α := iterate α bot (by apply bot_smallest) (by intro z pre; apply bot_smallest)

theorem fixpoint_correct : inst.eq (@fixpoint α _) (F (@fixpoint _ _)) /\ forall z : α , le (F z) z -> le (@fixpoint _ _) z := by
  unfold fixpoint
  have PRE : inst.le (bot) (F bot) := by apply bot_smallest
  have SMALL : ∀ z, le (F z) z -> inst.le bot z := by
    intro z hyp
    apply le_trans
    rotate_left
    . exact hyp
    . apply bot_smallest
  have := @iterate_correct α inst (iterate α bot PRE SMALL) bot PRE SMALL (rfl)
  grind


-- (** ** 9.2 Application to constant propagation analysis *)

-- (** First, we equip the type of abstract stores with the required equality
--   and ordering predicates.  [le] and [beq] are defined in [Constprop],
--   under the names [le'] and [equal']. *)

-- Definition Eq (S1 S2: Store) : Prop :=
--   IdentMap.Equal S1 S2.

-- Lemma Eq_sym: forall S1 S2, Eq S1 S2 -> Eq S2 S1.
-- Proof.
--   intros. apply IMFact.Equal_sym. auto.
-- Qed.

-- Lemma Equal_Eq: forall S1 S2, Equal S1 S2 = true -> Eq S1 S2.
-- Proof.
--   intros. unfold Eq. apply <- IMFact.Equal_Equivb.
--   apply IdentMap.equal_2. eauto. apply Z.eqb_eq.
-- Qed.

-- Lemma Equal_nEq: forall S1 S2, Equal S1 S2 = false -> ~ Eq S1 S2.
-- Proof.
--   intros. unfold Eq. intros IE.
--   assert (Equal S1 S2 = true).
--   { apply IdentMap.equal_1. apply IMFact.Equal_Equivb. apply Z.eqb_eq. auto. }
--   congruence.
-- Qed.

-- Lemma Eq_Le: forall S1 S2, Eq S1 S2 -> Le S1 S2.
-- Proof.
--   unfold Eq, Le; intros. rewrite H; auto.
-- Qed.

-- Lemma Le_trans: forall S1 S2 S3, Le S1 S2 -> Le S2 S3 -> Le S1 S3.
-- Proof.
--   unfold Le; auto.
-- Qed.

-- Definition Gt (S1 S2: Store) := Le S2 S1 /\ ~ Eq S2 S1.

-- (** We will use monotonically increasing functions a lot. *)

-- Definition Increasing (F: Store -> Store) : Prop :=
--   forall x y, Le x y -> Le (F x) (F y).

-- (** The really hard proof is to show that the strict order [Gt] is
--   well-founded.  For this we reason on the cardinal of the finite maps
--   representing abstract stores, that is, the number of [x = n] facts
--   contained in abstract stores. *)

-- Lemma Le_cardinal:
--   forall S T,
--   Le T S ->
--   IdentMap.cardinal S <= IdentMap.cardinal T
--   /\ (IdentMap.cardinal S = IdentMap.cardinal T -> IdentMap.Equal T S).
-- Proof.
--   induction S using IMProp.map_induction.
--   - intros. rewrite IMProp.cardinal_1 by auto. split.
--     + lia.
--     + intros.
--       assert (IdentMap.Empty T) by (apply IMProp.cardinal_inv_1; auto).
--       apply IMFact.Equal_mapsto_iff. intros.
--       specialize (H k e); specialize (H2 k e). tauto.
--   - intros T2 LE.
--     set (T1 := IdentMap.remove x T2).
--     assert (~ IdentMap.In x T1).
--     { apply IdentMap.remove_1; auto. }
--     assert (IMProp.Add x e T1 T2).
--     { intros y. unfold T1. rewrite IMFact.add_o, IMFact.remove_o.
--       destruct (IMProp.F.eq_dec x y); auto.
--       subst x. apply LE. rewrite H0. apply IMFact.add_eq_o. auto. }
--     assert (Le T1 S1).
--     { red; intros. unfold T1; rewrite IMFact.remove_o.
--       destruct (IMProp.F.eq_dec x x0).
--       subst x0. exfalso; apply H. apply IMFact.in_find_iff. congruence.
--       apply LE. rewrite H0. rewrite IMFact.add_neq_o; auto.
--     }
--     rewrite (@IMProp.cardinal_2 _ S1 S2 x e) by auto.
--     rewrite (@IMProp.cardinal_2 _ T1 T2 x e) by auto.
--     destruct (IHS1 T1) as [A B]; auto.
--     split.
--     + lia.
--     + intros.
--       assert (IdentMap.Equal T1 S1) by (apply B; lia).
--       intros y. rewrite H0, H2. rewrite ! IMFact.add_o.
--       destruct (IMProp.F.eq_dec x y); auto.
-- Qed.

-- Lemma Gt_cardinal:
--   forall S S', Gt S S' -> IdentMap.cardinal S < IdentMap.cardinal S'.
-- Proof.
--   intros S S' [LE NEQ].
--   edestruct Le_cardinal as [A B]. eauto.
--   assert (IdentMap.cardinal S <> IdentMap.cardinal S').
--   { intros EQ; apply NEQ; apply B; auto. }
--   lia.
-- Qed.

-- Lemma Gt_wf: well_founded Gt.
-- Proof.
--   apply wf_incl with (ltof Store (@IdentMap.cardinal Z)).
--   - intros S S' GT. apply Gt_cardinal; auto.
--   - apply well_founded_ltof.
-- Qed.

-- (** Another difficulty is that our type of abstract stores does not have
--   a smallest element [bot].  But for the kind of functions we take fixpoints of,
--   we know a pre-fixpoint we can start iterating with. *)

-- Section FIXPOINT_JOIN.

-- Variable Init: Store.
-- Variable F: Store -> Store.
-- Hypothesis F_incr: Increasing F.

-- Program Definition fixpoint_join : Store :=
--   iterate Store Eq Equal Equal_Eq Equal_nEq Le Le_trans Gt_wf
--           (fun x => Join Init (F x)) _ Init _ _.
-- Next Obligation.
--   unfold Le; intros.
--   apply Join_characterization in H0. destruct H0 as [FIND1 FIND2].
--   apply Join_characterization. split; auto. apply (F_incr _ _ H). auto.
-- Qed.
-- Next Obligation.
--   apply Le_Join_l.
-- Qed.
-- Next Obligation.
--   eapply Le_trans. apply Le_Join_l. eauto.
-- Qed.

-- Lemma fixpoint_join_eq:
--   Eq (Join Init (F fixpoint_join)) fixpoint_join.
-- Proof.
--   apply Eq_sym. unfold fixpoint_join.
--   destruct iterate as (X & EQ & SMALL). auto.
-- Qed.

-- Lemma fixpoint_join_sound:
--   Le Init fixpoint_join /\ Le (F fixpoint_join) fixpoint_join.
-- Proof.
--   assert (LE: Le (Join Init (F fixpoint_join)) fixpoint_join).
--   { apply Eq_Le. apply fixpoint_join_eq. }
--   split.
-- - eapply Le_trans. apply Le_Join_l. eauto.
-- - eapply Le_trans. apply Le_Join_r. eauto.
-- Qed.

-- Lemma fixpoint_join_smallest:
--   forall S, Le (Join Init (F S)) S -> Le fixpoint_join S.
-- Proof.
--   unfold fixpoint_join. destruct iterate as (X & EQ & SMALL).
--   auto.
-- Qed.

-- End FIXPOINT_JOIN.

-- (** Now we can try to use the [fixpoint_join] function above in the [Cexec]
--   static analyzer.  But we are in for a surprise!
-- *)

-- Fail Fixpoint Cexec (S: Store) (c: com) : Store :=
--   match c with
--   | SKIP => S
--   | ASSIGN x a => Update x (Aeval S a) S
--   | SEQ c1 c2 => Cexec (Cexec S c1) c2
--   | IFTHENELSE b c1 c2 =>
--       match Beval S b with
--       | Some true => Cexec S c1
--       | Some false => Cexec S c2
--       | None => Join (Cexec S c1) (Cexec S c2)
--       end
--   | WHILE b c1 =>
--       fixpoint_join S (fun x => Cexec x c1) _
--   end.

-- (** It says:
--   "Cannot infer this placeholder of type [Increasing (fun x : Store => Cexec x c1)]".
--   Of course!  We can only take fixpoints of increasing functions!

--   So, we need to find a way to define the [Cexec] function and SIMULTANEOUSLY
--   show that it is increasing.

--   This can be done, but we'll need a lot of lemmas about increasing
--   functions first.
-- *)

-- Lemma Join_increasing:
--   forall S1 S2 S3 S4,
--   Le S1 S2 -> Le S3 S4 -> Le (Join S1 S3) (Join S2 S4).
-- Proof.
--   unfold Le; intros. rewrite Join_characterization in *. destruct H1; split; auto.
-- Qed.

-- Lemma Aeval_increasing:
--   forall S1 S2, Le S1 S2 ->
--   forall a n, Aeval S2 a = Some n -> Aeval S1 a = Some n.
-- Proof.
--   intros S1 S2 LE; induction a; cbn; intros.
-- - auto.
-- - apply LE; auto.
-- - destruct (Aeval S2 a1), (Aeval S2 a2); cbn in H; inv H.
--   erewrite IHa1, IHa2 by eauto. auto.
-- - destruct (Aeval S2 a1), (Aeval S2 a2); cbn in H; inv H.
--   erewrite IHa1, IHa2 by eauto. auto.
-- Qed.

-- Lemma Beval_increasing:
--   forall S1 S2, Le S1 S2 ->
--   forall b n, Beval S2 b = Some n -> Beval S1 b = Some n.
-- Proof.
--   intros S1 S2 LE; induction b; cbn; intros.
-- - auto.
-- - auto.
-- - destruct (Aeval S2 a1) eqn:A1, (Aeval S2 a2) eqn:A2; cbn in H; inv H.
--   erewrite ! Aeval_increasing by eauto. auto.
-- - destruct (Aeval S2 a1) eqn:A1, (Aeval S2 a2) eqn:A2; cbn in H; inv H.
--   erewrite ! Aeval_increasing by eauto. auto.
-- - destruct (Beval S2 b); cbn in H; inv H.
--   erewrite IHb by eauto. auto.
-- - destruct (Beval S2 b1), (Beval S2 b2); cbn in H; inv H.
--   erewrite IHb1, IHb2 by eauto. auto.
-- Qed.

-- Lemma Update_increasing:
--   forall S1 S2 x a,
--   Le S1 S2 ->
--   Le (Update x (Aeval S1 a) S1) (Update x (Aeval S2 a) S2).
-- Proof.
--   intros; unfold Le; intros.
--   rewrite Update_characterization in *.
--   destruct (string_dec x x0); auto.
--   subst x0. apply Aeval_increasing with S2; auto.
-- Qed.

-- Lemma fixpoint_Join_increasing:
--   forall F (F_incr: Increasing F) S1 S2,
--   Le S1 S2 -> Le (fixpoint_join S1 F F_incr) (fixpoint_join S2 F F_incr).
-- Proof.
--   intros. apply fixpoint_join_smallest.
--   set (fix2 := fixpoint_join S2 F F_incr).
--   assert (Le (Join S2 (F fix2)) fix2) by (apply Eq_Le; apply fixpoint_join_eq).
--   eapply Le_trans; eauto.
--   apply Join_increasing; auto. unfold Le; auto.
-- Qed.

-- (** At long last, we can define [Cexec] while at the same time showing that
--   it is increasing. *)

-- Program Fixpoint Cexec (c: com) : { F: Store -> Store | Increasing F } :=
--   match c with
--   | SKIP => fun S => S
--   | ASSIGN x a => fun S => Update x (Aeval S a) S
--   | SEQ c1 c2 => compose (Cexec c2) (Cexec c1)
--   | IFTHENELSE b c1 c2 =>
--       fun S =>
--       match Beval S b return _ with
--       | Some true => Cexec c1 S
--       | Some false => Cexec c2 S
--       | None => Join (Cexec c1 S) (Cexec c2 S)
--       end
--   | WHILE b c1 =>
--       fun S => fixpoint_join S (fun S => Cexec c1 S) _
--   end.
-- Next Obligation.
--   unfold Increasing. auto.
-- Defined.
-- Next Obligation.
--   intros y z LE. apply Update_increasing; auto.
-- Defined.
-- Next Obligation.
--   intros y z LE. unfold compose. auto.
-- Defined.
-- Next Obligation.
--   intros y z LE. destruct (Beval z b) as [bz|] eqn:BEV.
--   erewrite Beval_increasing by eauto. destruct bz; auto.
--   destruct (Beval y b) as [[]|].
--   apply Le_trans with (x z). auto. apply Le_Join_l.
--   apply Le_trans with (x0 z). auto. apply Le_Join_r.
--   apply Join_increasing; auto.
-- Defined.
-- Next Obligation.
--   intros y z LE. apply fixpoint_Join_increasing. auto.
-- Defined.
