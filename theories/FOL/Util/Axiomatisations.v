From Undecidability.FOL.Util Require Import Syntax Syntax_facts FullDeduction FullDeduction_facts FullTarski.
From Undecidability.Synthetic Require Import DecidabilityFacts EnumerabilityFacts ReducibilityFacts.
From Undecidability.Synthetic Require Import ListEnumerabilityFacts MoreEnumerabilityFacts.
From Undecidability.Shared Require Import Dec.
From Equations Require Import Equations.
Require Import ConstructiveEpsilon.
Require Import List.

Local Set Implicit Arguments.
Local Unset Strict Implicit.



(* Decision problems on axiomatisations *)

Existing Instance falsity_on.

Notation "I ⊨= phi" := (forall rho, sat I rho phi) (at level 20).
Notation "T ⊨T phi" := (forall D (I : interp D), (forall psi, T psi -> I ⊨= psi) -> I ⊨= phi) (at level 55).


Section FixSignature.

  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.

  Implicit Type T : form -> Prop.
  
  Definition tprv_class T phi := T ⊢TC phi.
  Definition tprv_intu T phi := T ⊢TI phi.
  Definition tvalid T phi := T ⊨T phi.



  (* Reductions to axiomatisations *)

  Definition treduction X (f : X -> form) (P : X -> Prop) T :=
    reduction f P (tvalid T) /\ reduction f P (tprv_intu T).

  Notation "P ⪯T T" := (exists f, treduction f P T) (at level 55).



  (* Fact 7 : if a non-trivial problem reduces to T, then T is consistent *)

  Fact reduction_consistency {p : peirce} X (f : X -> form) (P : X -> Prop) T :
    reduction f P (tprv T) -> (exists x, ~ P x) -> ~ T ⊢T ⊥.
  Proof.
    intros Hf [x Hx] [A[H1 H2]]. apply Hx, Hf.
    exists A. split; trivial. now apply Exp.
  Qed.
  
  Section Axiomatisations.

    Context {enum_funcs : enumerable__T Σ_funcs} {eqdec_funcs : eq_dec syms}.
    Context {enum_preds : enumerable__T Σ_preds} {eqdec_preds : eq_dec preds}.



    (* Assuming a discrete and enumerable signature, the type of formulas is discrete and enumerable *)

    Instance EqDec_funcs : EqDec Σ_funcs.
    Proof.
      intros x y. apply eqdec_funcs.
    Qed.

    Instance EqDec_preds : EqDec Σ_preds.
    Proof.
      intros x y. apply eqdec_preds.
    Qed.

    Lemma form_discrete :
      discrete form.
    Proof.
      apply discrete_iff. constructor. apply dec_form; trivial.
      all: intros ? ?; unfold dec; decide equality.
    Qed.

    Lemma form_enumerable :
      enumerable__T form.
    Proof.
      eapply enumT_form; trivial. apply enumT_binop. apply enumT_quantop.
    Qed.



    (* For any axiomatisation, the (classical) deductive consequences are enumerable *)

    Variable T : form -> Prop.
    Hypothesis enum_T : enumerable T.

    Lemma tprv_class_enum :
      enumerable (tprv_class T).
    Proof.
      apply enumerable_enum.
      apply enumerable_enum in enum_T as [L HL].
      apply enum_enumT in enum_funcs as [L1 HL1].
      apply enum_enumT in enum_preds as [L2 HL2].
      exists (@L_tded _ _ L1 HL1 L2 HL2 _ _ class falsity_on (cumul L)).
      now apply enum_tprv.
    Qed.


    
    (* Post's theorem: bi-enumerable logically decidable predicates over discrete domain are decidable *)

    Definition mu (p : nat -> Prop) :
      (forall x, dec (p x)) -> ex p -> sig p.
    Proof.
      apply constructive_indefinite_ground_description_nat_Acc.
    Qed.

    Definition ldecidable {X} (p : X -> Prop) :=
      forall x, p x \/ ~ p x.

    Theorem weakPost X (p : X -> Prop) :
      discrete X -> ldecidable p -> enumerable p -> enumerable (fun x => ~ p x) -> decidable p.
    Proof.
      intros [E] % discrete_iff Hl [f Hf] [g Hg].
      eapply decidable_iff. econstructor. intros x.
      assert (exists n, f n = Some x \/ g n = Some x) by (destruct (Hl x); firstorder).
      destruct (@mu (fun n => f n = Some x \/ g n = Some x)) as [n HN]; trivial.
      - intros n. exact _.
      - decide (f n = Some x); decide (g n = Some x); firstorder.
    Qed.



    (* Fact 9 : consistent complete theories are decidable for closed formulas *)

    Definition stripneg `{falsity_flag} (phi : form) : option form :=
      match phi with 
      | bin Impl phi ⊥ => Some phi
      | _ => None
      end.

    Instance eq_dec_ff :
      eq_dec falsity_flag.
    Proof.
      intros ff ff'. unfold dec. decide equality.
    Qed.

    Lemma stripneg_spec {ff : falsity_flag} {phi psi} :
      stripneg phi = Some psi -> phi = ¬ psi.
    Proof.
      depelim phi; cbn; try destruct b0; try discriminate.
      - inversion H. apply inj_pair2_eq_dec' in H1 as ->; eauto. cbn. discriminate.
      - depelim phi2; cbn; try destruct b0; try discriminate.
        inversion H. apply inj_pair2_eq_dec' in H1 as ->; eauto. congruence.
    Qed.

    Lemma enumerable_equiv X (P Q : X -> Prop) :
      (forall x, P x <-> Q x) -> enumerable P -> enumerable Q.
    Proof.
      intros H [f Hf]. exists f. intros x. rewrite <- H. apply Hf.
    Qed.

    Definition complete :=
      forall phi, bounded 0 phi -> T ⊢TC phi \/ T ⊢TC ¬ phi.
    
    Fact complete_decidable :
      (~ T ⊢TC ⊥) -> complete -> decidable (fun phi => bounded 0 phi /\ T ⊢TC phi).
    Proof.
      intros H1 H2.
      assert (H : forall phi, bounded 0 phi -> ~ T ⊢TC phi <-> T ⊢TC ¬ phi).
      - intros phi HP. split; intros H.
        + destruct (H2 phi) as [H3|H3]; tauto.
        + intros [B[HB1 HB2]]. destruct H as [C[HC1 HC2]].
          apply H1. exists (B ++ C). split.
          * intros psi. rewrite in_app_iff. intuition.
          * eapply IE; eapply Weak; eauto.
      - apply weakPost; try apply form_discrete.
        + intros phi. destruct (bounded_dec phi 0) as [Hb|Hb].
          destruct (H2 phi Hb) as [Hp|Hp % H]. all: tauto.
        + apply enumerable_conj; try apply form_discrete.
          * apply dec_count_enum; try apply form_enumerable.
            apply decidable_iff. constructor. intros phi. apply bounded_dec.
          * apply tprv_class_enum.
        + apply enumerable_equiv with (fun phi => ~ bounded 0 phi \/ T ⊢TC ¬ phi).
          { intros phi. destruct (bounded_dec phi 0); intuition. }
          apply enumerable_disj; try apply dec_count_enum'; try apply form_enumerable.
          { apply decidable_iff. constructor. intros phi. apply bounded_dec. }
          destruct tprv_class_enum as [f Hf].
          exists (fun n => match f n with Some phi => stripneg phi | _ => None end).
          intros phi. rewrite (Hf (¬ phi)). split; intros [n Hn]; exists n; try now rewrite Hn.
          destruct (f n) as [psi|]; try discriminate. now rewrite (stripneg_spec Hn).
    Qed.



    (* Consequence : problems reducing to complete theories are decidable *)

    Fact complete_decidable' X (P : X -> Prop) (f : X -> form) :
      (~ T ⊢TC ⊥) -> complete -> reduction f P (tprv_class T) -> (forall x, bounded 0 (f x)) -> decidable P.
    Proof.
      intros H1 H2 H3 H4. apply complete_decidable in H1; trivial.
      apply decidable_iff in H1 as [H1]. apply decidable_iff. constructor.
      intros x. destruct (H1 (f x)) as [H|H].
      - left. apply H3, H.
      - right. contradict H. split; try now apply H4. apply H3, H.
    Qed.
    
  End Axiomatisations.



  (* Theorem 10 : undecidability transports to extended axiomatisations satisfied by standard models *)
  
  Section Reduction.

    Variable T : form -> Prop.

    Variable X : Type.
    Variable P : X -> Prop.
    Variable f : X -> form.

    Notation "S <<= S'" := (forall phi, S phi -> S' phi) (at level 10).
    
    Variable standard : forall {D : Type}, interp D -> Prop.

    Hypothesis hyp1 : forall x, P x -> T ⊨T (f x).
    Hypothesis hyp2 : forall D (I : interp D) x, standard I -> (forall phi, T phi -> I ⊨= phi) -> I ⊨= f x -> P x.
    Hypothesis hyp3 : forall {p : peirce} x, P x -> T ⊢T (f x).

    Lemma WeakT {p : peirce} (S S' : form -> Prop) phi :
      S ⊢T phi -> S <<= S' -> S' ⊢T phi.
    Proof.
      intros [A[H1 H2]] H. exists A. split; auto.
    Qed.

    Theorem reduction_theorem (S : form -> Prop) :
      T <<= S -> (exists D I, @standard D I /\ forall phi, S phi -> I ⊨= phi) -> P ⪯T S.
    Proof.
      intros HS (D & I & [std MT]). exists f. repeat split; intros H.
      - intros D' I' H'. apply hyp1; auto.
      - apply (hyp2 std); auto.
      - apply WeakT with T; trivial. now apply hyp3.
      - apply (hyp2 std); auto. intros rho. apply (tsoundness H); auto.
    Qed.



    (* Theorem 10 : variant for classical deduction, using LEM *)

    Definition LEM := forall P, P \/ ~ P.
    
    Theorem reduction_theorem_class (S : form -> Prop) :
      LEM -> T <<= S -> (exists D I, @standard D I /\ forall phi, S phi -> I ⊨= phi) -> P ⪯ tprv_class S.
    Proof.
      intros lem HS (D & I & [std MT]). exists f. split; intros H.
      - apply WeakT with T; trivial. now apply hyp3.
      - apply (hyp2 std); auto. intros rho. apply (tsoundness_class lem H); auto.
    Qed.
    
  End Reduction.

End FixSignature.
