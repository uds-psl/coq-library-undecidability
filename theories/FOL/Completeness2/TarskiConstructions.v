(* * Tarski Semantics *)

(* ** Generalized Theory Extension **)

From Undecidability.FOL Require Import Syntax.Facts Syntax.Asimpl Deduction.FragmentNDFacts Syntax.Theories.
From Undecidability.Synthetic Require Import Definitions DecidabilityFacts EnumerabilityFacts ListEnumerabilityFacts ReducibilityFacts.
From Undecidability Require Import Shared.ListAutomation Shared.Dec.
From Undecidability Require Import Shared.Libs.PSL.Vectors.Vectors Shared.Libs.PSL.Vectors.VectorForall.
Import ListAutomationNotations.

Section GenCons.
  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.

  Context {HdF : eq_dec syms} {HdP : eq_dec preds}.

  Context {ff : falsity_flag}.
  Variable GBot : form.
  Hypothesis GBot_closed : closed GBot.

  Notation "⊥'" := GBot.
  Notation "A ⊢G phi" := (@prv Σ_funcs Σ_preds ff class A phi) (at level 30).
  Notation "T ⊢TG phi" := (@tprv Σ_funcs Σ_preds ff class T phi) (at level 30).

  Definition econsistent T T' := T' ⊢TG ⊥' -> T ⊢TG ⊥'.

  (* **** Union *)

  Section Union.
    Variable f : nat -> theory.
    Hypothesis econsistent_f : forall n, econsistent (f n) (f (S n)).
    Hypothesis f_le : forall m n, m <= n -> f m ⊑ f n.

    Definition union (f : nat -> theory) := fun t => exists n, f n t.

    Lemma union_f phi :
      union f ⊢TG phi -> exists n, f n ⊢TG phi.
    Proof.
      intros (A & HA1 & HA2). enough (exists n, A ⊏ f n) as [n H] by now exists n, A.
      clear HA2; induction A.
      - exists 0; eauto with contains_theory.
      - destruct IHA as [n Hn]; destruct (HA1 a) as [m Hm]; eauto with contains_theory.
        exists (max n m); intros ? []; subst.
        + eapply f_le; [apply PeanoNat.Nat.le_max_r | eauto with contains_theory]. 
        + eapply f_le; [apply PeanoNat.Nat.le_max_l | eauto with contains_theory].
    Qed.

    Lemma union_sub n :
      f n ⊑ union f.
    Proof.
      intros ? ?; exists n; eauto with contains_theory.
    Qed.

    Lemma union_econsistent :
      econsistent (f 0) (union f).
    Proof.
      intros [n H] % union_f. induction n; unfold econsistent in *; eauto.
    Qed.

    Lemma union_closed :
      (forall n, closed_T (f n)) -> closed_T (union f).
    Proof.
      intros f_closed phi [m H]. now eapply f_closed with (n := m) (phi := phi).
    Qed.
  End Union.

  (* **** Explosion *)

  Section Explosion.
    Variable T : theory.
    Hypothesis Hclosed : closed_T T.

    Variable e : nat -> form.
    Hypothesis He : forall phi, exists n, e n = phi.

    Definition exp_axiom phi := ⊥' → close All phi.

    Lemma exp_axiom_closed phi : closed (exp_axiom phi).
    Proof.
      unfold closed, exp_axiom. econstructor. 1:easy.
      apply close_closed.
    Qed.

    Lemma exp_axiom_lift phi A :
      exp_axiom phi el A -> exp_axiom phi el (map (subst_form ↑) A).
    Proof.
      intros H. apply in_map_iff. exists (exp_axiom phi). split. 2: assumption.
      unshelve erewrite <- subst_id. 1: intros x; exact ($x). eapply bounded_subst.
      1: apply exp_axiom_closed. lia. now cbv.
    Qed.

    Fixpoint exp n :=
      match n with
      | 0 => T
      | S n => exp n ⋄ exp_axiom (e n)
      end.
    Definition Exp := union exp.

    Lemma Exp_sub :
      T ⊑ Exp.
    Proof.
      apply union_sub with (n := 0) (f := exp).
    Qed.

    Lemma Exp_econsistent :
      econsistent T Exp.
    Proof.
      apply union_econsistent.
      - cbn. intros n (B & HB & Hprv) % prv_T_impl. use_theory B.
        eapply IE. 1: eapply Pc. apply Hprv.
      - induction 1; intros ?; firstorder.
    Qed.

    Lemma Exp_closed :
      closed_T Exp.
    Proof.
      apply union_closed. induction n; intuition.
      cbn. apply closed_T_extend. 1:easy. apply exp_axiom_closed.
    Qed.

    Definition exploding T := forall phi, (⊥' → close All phi) ∈ T.

    Lemma Exp_exploding :
      exploding Exp.
    Proof.
      intros phi. destruct (He phi) as [n Hn]. exists (S n). right; now subst.
    Qed.

    Lemma exploding_inherit T1 T2 :
      exploding T1 -> T1 ⊑ T2 -> exploding T2.
    Proof.
      firstorder.
    Qed.

  End Explosion. 

  (* **** Proving with explosion axioms *)

  Notation "¬' phi" := (phi → GBot) (at level 20).
  Notation "∃' phi" := (¬' ∀ ¬' phi) (at level 56, right associativity).

  Lemma GExp A phi :
    (exp_axiom phi) el A -> A ⊢G ⊥' -> A ⊢G phi.
  Proof.
    intros Hel Hbot. apply close_extract. exact (IE (Ctx Hel) Hbot).
  Qed.

  Lemma GDN A phi :
    (exp_axiom phi) el A -> A ⊢G ¬' (¬' phi) -> A ⊢G phi.
  Proof.
    intros Hx H.
    eapply IE.
    2: eapply (Pc A phi GBot).
    eapply II.
    eapply IE. 1: eapply Ctx; now left.
    eapply II. apply GExp. 1: now do 2 right.
    eapply IE. 2: eapply Ctx; now left.
    eapply Weak. 1: apply H.
    intros a Ha; now do 2 right.
  Qed.

  Lemma GExE A phi psi :
    exp_axiom psi el A -> A ⊢G (∃' phi) -> (phi :: map (subst_form ↑) A) ⊢G psi[↑] -> A ⊢G psi.
  Proof.
    intros Hx Hex Hinst.
    apply GDN; [easy | apply II].
    eapply IE. 1: eapply Weak; [eapply Hex |eauto].
    eapply AllI. eapply II.
    cbn. rewrite (@subst_closed _ _ _ _ ⊥'). 2: easy.
    eapply IE. 1: apply Ctx; right; now left.
    eapply Weak. 1: apply Hinst.
    intros a [->|H2]; eauto.
  Qed.

  Lemma GExI A t phi :
    A ⊢G phi [t..] -> A ⊢G ∃' phi.
  Proof.
    intros Hc. apply II.
    erewrite <- (@subst_closed _ _ _ _ ⊥' (t..)). 2:easy.
    eapply IE. 2: eapply Weak. 2: apply Hc. 2: intros a Ha; eauto.
    change ((phi[t..] → ⊥'[t..])) with ((phi → ⊥')[t..]).
    eapply AllE. apply Ctx. left.
    now rewrite subst_closed.
  Qed.

  Lemma GXM A phi psi :
    exp_axiom psi el A -> (phi :: A) ⊢G psi -> (¬' phi :: A) ⊢G psi -> A ⊢G psi.
  Proof.
    intros Hx Ht Hf. apply GDN; try easy.
    apply II. eapply IE with (¬' phi); [apply II|].
    - eapply IE. 1: apply Ctx; right; now left. eapply Weak. 1: apply Hf. intros a [->|Ha]; eauto.
    - eapply II. eapply IE. 1: apply Ctx; right; now left. eapply Weak. 1: apply Ht. intros a [->|Ha]; eauto.
  Qed.

  Definition DPexp1 phi := exp_axiom (∃' (phi → (∀ phi)[↑])).
  Definition DPexp2 phi := exp_axiom (phi [($O) .: (S >> (S >> var))]).
  Definition DPexp3 phi := exp_axiom phi.

  Lemma GDP A phi :
    DPexp1 phi el A -> DPexp2 phi el A -> DPexp3 phi el A -> A ⊢G ∃' (phi → (∀ phi)[↑]).
  Proof.
    intros ? H1 H2. do 2 apply exp_axiom_lift in H1. do 1 apply exp_axiom_lift in H2.
    apply (@GXM _ (∃' (¬' phi))); [intuition| |].
    - eapply GExE; [intuition|apply Ctx;now left|]; cbn.
      erewrite !(subst_closed _ GBot_closed).
      apply (@GExI _ ($0)). cbn. apply II. apply AllI. asimpl. apply GExp.
      eapply incl_map. 2: exact H1. intros a Ha; eauto. cbn.
      asimpl. rewrite (subst_closed _ GBot_closed).
      eapply IE; apply Ctx. 2: now left. 1: right; now left.
    - apply (@GExI _ ($0)). cbn. apply II. apply AllI. cbn.
      asimpl. rewrite ! (subst_closed _ GBot_closed).
      eapply GDN. 1: now do 2 right.
      eapply II.
      eapply IE. 1: apply Ctx; right; right; now left.
      apply (@GExI _ ($0)). cbn. rewrite ! (subst_closed _ GBot_closed).
      asimpl. apply Ctx. now left.
  Qed.

  (* **** Henkin *)

  Section Henkin.
    Variable T : theory.
    Hypothesis Hclosed : closed_T T.
    Hypothesis Hexp : exploding T.

    Variable e : nat -> form.
    Hypothesis He : forall phi, exists n, e n = phi.
    Hypothesis Hbounded : forall n, bounded n (e n).

    Definition henkin_axiom phi := (phi → ((∀ phi)[↑])). 

    Lemma henkin_axiom_bounded n phi :
      bounded n (∀ phi) -> bounded (S n) (¬' (henkin_axiom phi)).
    Proof.
      intros H%bounded_S_quant.
      unfold henkin_axiom. constructor. 2: eapply bounded_up; [apply GBot_closed|lia].
      econstructor. 2: cbn; econstructor. 1:easy.
      eapply subst_bounded_max. 2: apply H.
      intros i Hi. unfold up, funcomp, scons. cbn.
      destruct i; econstructor; lia.
    Qed.

    Fixpoint henkin n :=
      match n with
      | O => T
      | S n => henkin n ⋄ subst_form (($ n)..) (henkin_axiom (e n))
      end.

    Lemma henkin_bounded n :
      forall phi, phi ∈ (henkin n) -> bounded n phi.
    Proof.
      induction n as [|n IH]; cbn.
      - intros. now apply Hclosed.
      - intros phi [H1|H1]. 1: eapply bounded_up; intuition.
        subst. econstructor.
        + eapply subst_bounded_max. 2: apply Hbounded.
          intros i Hi. destruct i; econstructor; lia.
        + econstructor. rewrite subst_comp. eapply subst_bounded_max. 2:apply Hbounded.
          intros i Hi. destruct i; econstructor; lia.
    Qed.

    Lemma henkin_le m n :
      m <= n -> henkin m ⊑ henkin n.
    Proof.
      induction 1; firstorder.
    Qed.

    Definition Henkin := union henkin.

    Lemma Henkin_consistent :
      econsistent T Henkin.
    Proof.
      refine (union_econsistent _ henkin_le). intros n.
      cbn; intros (A & HA1 & HA2) % prv_T_impl.
      rewrite <- (@subst_id _ _ _ _ ⊥' var) in HA2.
      rewrite (@bounded_subst _ _ _ _ _ _ _ ($n..) GBot_closed) in HA2.
      apply <- (@nameless_equiv_all' _ _ ff class A (¬' (henkin_axiom (e n))) n) in HA2. 5:easy. 4:lia.
      - use_theory (exp_axiom GBot :: DPexp1 (e n) :: DPexp2 (e n) :: DPexp3 (e n) :: A).
        { intros ? [<- | [<- | [ <- | [<- |]]]]. 5: intuition.
          all: apply henkin_le with (m := 0); [lia | apply Hexp]. }
        eapply IE.
        2: apply (@GDP (exp_axiom GBot :: DPexp1 (e n) :: DPexp2 (e n) :: DPexp3 (e n) :: A) (e n)); eauto.
        apply II.
        eapply GExE. 1: eauto. 1: apply Ctx; eauto.
        cbn.
        rewrite ! (subst_closed _ GBot_closed).
        rewrite ! (subst_closed _ (close_closed _ _)).
        eapply IE. 2: eapply Weak; [apply HA2|]. 2: intros a Ha; now do 6 right.
        apply II. eapply IE. 1: apply Ctx; now left. apply Ctx. right. now left.
      - apply henkin_axiom_bounded. constructor. eapply bounded_up; [apply Hbounded | lia].
      - intros ? H' % HA1. eapply henkin_bounded. apply H'.
    Qed.

    Definition is_Henkin T := forall T' phi, T ⊑ T' -> (forall t, T' ⊢TG phi[t..]) -> T' ⊢TG ∀ phi.

    Lemma Henkin_is_Henkin :
      is_Henkin Henkin.
    Proof.
      intros T' phi HT' Hall. destruct (He phi) as [n Hn]. destruct (Hall ($n)) as (A & HA1 & HA2).
      use_theory (subst_form (($n)..) (henkin_axiom phi) :: A).
      - intros ? [<- |]; [| intuition]; subst. apply HT'. exists (S n). now right.
      - eapply IE; [|eapply Weak; [apply HA2|intros a Ha; eauto]]; apply II.
        cbn. asimpl.
        eapply IE. 1: apply Ctx; eauto. apply Ctx; eauto.
    Qed.

    Lemma is_Henkin_inherit T1 T2 :
      is_Henkin T1 -> T1 ⊑ T2 -> is_Henkin T2.
    Proof.
      intros H1 H2 TT phi HTT. apply H1. intros psi Hpsi. apply HTT. apply H2. easy.
    Qed.

    Lemma Henkin_T :
      T ⊑ Henkin.
    Proof.
      apply union_sub with (f := henkin) (n := 0).
    Qed.
  End Henkin.

  (* **** Omega *)

  Section Omega.
    Variable e : nat -> form.
    Hypothesis He : forall phi, exists n, e n = phi.

    Variable T : theory.
    Hypothesis Hexp : exploding T.
    Hypothesis Hhenkin : is_Henkin T.

    Definition maximal T := forall f, econsistent T (T ⋄ f) -> f ∈ T.

    Definition econsistent_join T phi := fun psi => T psi \/ (econsistent T (T ⋄ phi) /\ psi = phi).
    Infix "∘" := econsistent_join (at level 20).

    Lemma econsistent_join_sub T' phi :
      (T' ∘ phi) ⊑ (T' ⋄ phi).
    Proof.
      intros psi [Htt1|[Htt2 ->]].
      - now left.
      - now right.
    Qed.

    Lemma consistent_join_step T' phi psi :
      T' ∘ psi ⊢TG phi -> T' ⊢TG phi \/ econsistent T' (T' ⋄ psi).
    Proof.
      intros (A & HA1 & HA2).
      enough (A ⊏ T' \/ econsistent T' (T' ⋄ psi)) as [] by ((left; exists A; intuition) + now right).
      clear HA2; induction A.
      - firstorder.
      - destruct (HA1 a), IHA; intuition. all: eauto with contains_theory.
    Qed.

    Fixpoint omega n : theory :=
      match n with
      | 0 => T
      | S n => omega n ∘ e n
      end.

    Lemma omega_le n m :
      n <= m -> omega n ⊑ omega m.
    Proof.
      induction 1; firstorder.
    Qed.

    Definition Omega : theory := union omega.

    Lemma econsistent_Omega :
      econsistent T Omega.
    Proof.
      refine (union_econsistent _ omega_le). intros n H. destruct (consistent_join_step H).
      all: firstorder.
    Qed.

    Lemma econsistency_inheritance T1 T2 T1' T2' :
      econsistent T1 T1' -> T1 ⊑ T2 -> T2' ⊑ T1' -> econsistent T2 T2'.
    Proof.
      intros H1 HT HT' (A & AT2' & Hprv).
      assert (T1' ⊢TG ⊥') as HT1'.
      - use_theory A. 1: intros psi Hin; apply HT', AT2', Hin. easy.
      - destruct (H1 HT1') as (B & BT1' & HBprv).
        use_theory B. intros psi Hin; apply HT, BT1', Hin. easy.
    Qed.

    Lemma econsistency_trans T1 T2 T3 :
      econsistent T1 T2 -> econsistent T2 T3 -> econsistent T1 T3.
    Proof.
      intros H1 H2 H. apply H1. apply H2. easy.
    Qed.

    Lemma maximal_Omega :
      maximal Omega.
    Proof.
      intros phi H. destruct (He phi) as [n Hn].
      apply (union_sub (n := S n)); cbn; rewrite -> Hn. right; split; [| reflexivity].
      eapply econsistency_inheritance.
      + exact (econsistency_trans econsistent_Omega H).
      + apply omega_le with (n := 0). lia.
      + firstorder.
    Qed.

    Lemma econsistent_prv T' T'' phi :
      econsistent T' T'' -> T'' ⊢TG phi -> econsistent T' (T'' ⋄ phi).
    Proof.
      intros HT Hphi Hbot. now apply HT, (prv_T_remove Hphi).
    Qed.

    Lemma maximal_prv T' phi :
      maximal T' -> T' ⊢TG phi -> phi ∈ T'.
    Proof.
      intros Hin Hprv. now apply Hin, econsistent_prv.
    Qed.

    Lemma Omega_prv phi :
      Omega ⊢TG phi -> phi ∈ Omega.
    Proof.
      intros Hprv. now apply (maximal_prv maximal_Omega).
    Qed.

    Lemma Omega_T :
      T ⊑ Omega.
    Proof.
      change T with (omega 0). apply (union_sub (n := 0)).
    Qed.

    Lemma Omega_impl phi psi :
      phi → psi ∈ Omega <-> (phi ∈ Omega -> psi ∈ Omega).
    Proof.
      split.
      - intros Himp Hphi. apply Omega_prv.
        use_theory [phi → psi; phi].
        1: intros a [<-|[<-|[]]]; easy.
        eapply IE. 1: apply Ctx; eauto. apply Ctx; eauto.
      - intros H. apply maximal_Omega. intros (A & HA1 & HA2) % prv_T_impl.
        apply (prv_T_remove (phi := psi)).
        + apply elem_prv, H, Omega_prv.
          use_theory (exp_axiom phi :: exp_axiom psi :: A).
          * intros ? [<- | [ <- | H'']]; [apply Omega_T, Hexp | apply Omega_T, Hexp | now apply HA1].
          * eapply GDN; try eauto. apply II. 
            eapply IE; [|eapply Weak; [apply HA2|intros a Ha; eauto]]; apply II.
            eapply IE; [eapply Ctx; now left|].
            apply II. apply GExp; eauto. eapply IE; [|apply Ctx; now left]. apply Ctx; eauto.
        + use_theory (psi :: A). 1:intros a [->|Hin]; [right|left]; intuition.
          eapply IE; [|eapply Weak; [apply HA2|intros a Ha; eauto]]; apply II.
          eapply IE; [apply Ctx; eauto|]. apply II. apply Ctx; eauto.
    Qed.

    Lemma Omega_all phi :
      ∀ phi ∈ Omega <-> (forall t, phi[t..] ∈ Omega).
    Proof.
      split; intros Hprv.
      - intros t. apply Omega_prv. use_theory [∀ phi]. 1: intros psi [<-|[]]; eauto.
        apply AllE. now apply Ctx.
      - apply Omega_prv, (Hhenkin Omega_T). eauto using elem_prv.
    Qed.
  End Omega.
End GenCons.

(* **** Conclusion *)

Section Composition.
  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.

  Context {HdF : eq_dec syms} {HdP : eq_dec preds}.

  Structure ConstructionInputs : Type :=
    {
      variant : falsity_flag ;

      NBot : form ;
      NBot_closed : closed NBot ;

      In_T : theory ;
      In_T_closed : closed_T In_T ;

      enum : nat -> form ;
      enum_enum : forall phi, exists n, enum n = phi ;
      enum_bounded : forall n, bounded n (enum n)
    }.

  Structure ConstructionOutputs (In : ConstructionInputs) :=
    {
      Out_T : theory ;
      Out_T_econsistent : @econsistent _ _  (variant In) (NBot In) (@In_T In) Out_T ;
      Out_T_sub : @In_T In ⊑ Out_T ;

      Out_T_prv : forall phi, @tprv _ _ (variant In) class Out_T phi -> phi ∈ Out_T ;
      Out_T_all : forall phi, ∀ phi ∈ Out_T <-> (forall t, phi[t..] ∈ Out_T) ;
      Out_T_impl : forall phi psi, phi → psi ∈ Out_T <-> (phi ∈ Out_T -> psi ∈ Out_T)
    }.

  Lemma construct_construction (In : ConstructionInputs) :
    ConstructionOutputs In.
  Proof.
    destruct In as [ff NBot NBot_closed T T_closed e e_enum e_bounded].
    eexists (Omega NBot e (Henkin (Exp NBot T e) e)); cbn.
    + eapply econsistency_trans. { eapply econsistency_trans. eapply Exp_econsistent.
      eapply Henkin_consistent; intuition. 1: eapply Exp_closed; intuition. eapply Exp_exploding. intros n; easy. } eapply econsistent_Omega.
    + transitivity (Henkin (Exp NBot T e) e). 1: transitivity (Exp NBot T e).
      1: apply Exp_sub. 1: apply Henkin_T. apply Omega_T.
    + eapply Omega_prv. easy.
    + eapply Omega_all; try easy. eapply Henkin_is_Henkin. easy.
    + eapply Omega_impl; try easy. eapply exploding_inherit.
      - eapply Exp_exploding. easy.
      - eapply Henkin_T.
  Qed.
End Composition.
