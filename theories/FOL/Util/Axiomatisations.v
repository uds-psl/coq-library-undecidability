From Undecidability.FOL.Util Require Import Syntax_facts FullDeduction FullDeduction_facts FullTarski FullTarski_facts.
From Undecidability.Synthetic Require Import Definitions Undecidability.
From Undecidability.Synthetic Require Import DecidabilityFacts EnumerabilityFacts ReducibilityFacts.
From Undecidability.Synthetic Require Import ListEnumerabilityFacts MoreEnumerabilityFacts.
From Undecidability.Shared Require Import Dec.
From Equations Require Import Equations.
Require Import ConstructiveEpsilon.
Require Import List.
Import ListNotations.

Local Set Implicit Arguments.
Local Unset Strict Implicit.



(* Section 3 : Undecidable First-Order Axiomatisations *)

(* Decision problems on axiomatisations *)

Existing Instance falsity_on.

Notation "S <<= S'" := (forall phi, S phi -> S' phi) (at level 10).
Notation "I ⊨= phi" := (forall rho, sat I rho phi) (at level 20).
Notation "I ⊨=T T" := (forall psi, T psi -> I ⊨= psi) (at level 20).
Notation "T ⊨T phi" := (forall D (I : interp D), I ⊨=T T -> I ⊨= phi) (at level 55).

Section FixSignature.

  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.

  Implicit Type T : form -> Prop.
  
  Definition tprv_class T phi := T ⊢TC phi.
  Definition tprv_intu T phi := T ⊢TI phi.
  Definition tvalid T phi := T ⊨T phi.



  (* Definition 5 : reductions to axiomatisations combine Tarski semantics and intuitionistic ND *)

  Definition treduction X (f : X -> form) (P : X -> Prop) T :=
    reduction f P (tvalid T) /\ reduction f P (tprv_intu T).



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



    (* For any (enumerable) axiomatisation, the deductive consequences are enumerable *)

    Variable T : form -> Prop.
    Hypothesis enum_T : enumerable T.

    Lemma tprv_enumerable {p : peirce} :
      enumerable (fun phi => tprv T phi).
    Proof.
      apply enumerable_enum.
      apply enumerable_enum in enum_T as [L HL].
      apply enum_enumT in enum_funcs as [L1 HL1].
      apply enum_enumT in enum_preds as [L2 HL2].
      exists (@L_tded _ _ L1 HL1 L2 HL2 _ _ p falsity_on (cumul L)).
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
          * apply tprv_enumerable.
        + apply enumerable_equiv with (fun phi => ~ bounded 0 phi \/ T ⊢TC ¬ phi).
          { intros phi. destruct (bounded_dec phi 0); intuition. }
          apply enumerable_disj; try apply dec_count_enum'; try apply form_enumerable.
          { apply decidable_iff. constructor. intros phi. apply bounded_dec. }
          destruct (tprv_enumerable (p:=class)) as [f Hf].
          exists (fun n => match f n with Some phi => stripneg phi | _ => None end).
          intros phi. rewrite (Hf (¬ phi)). split; intros [n Hn]; exists n; try now rewrite Hn.
          destruct (f n) as [psi|]; try discriminate. now rewrite (stripneg_spec Hn).
    Qed.



    (* Consequence : problems reducing to complete theories are decidable *)

    Fact complete_reduction X (P : X -> Prop) (f : X -> form) :
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

    Variable standard : forall D, interp D -> Prop.

    Hypothesis hyp1 : forall x, P x -> T ⊨T (f x).
    Hypothesis hyp2 : forall D (I : interp D) x, standard I -> I ⊨=T T -> I ⊨= (f x) -> P x.
    Hypothesis hyp3 : forall {p : peirce} x, P x -> T ⊢T (f x).

    Lemma WeakT {p : peirce} (S S' : form -> Prop) phi :
      S ⊢T phi -> S <<= S' -> S' ⊢T phi.
    Proof.
      intros [A[H1 H2]] H. exists A. split; auto.
    Qed.

    Theorem reduction_theorem (S : form -> Prop) :
      T <<= S -> (exists D (I : interp D), standard I /\ I ⊨=T S) -> treduction f P S.
    Proof.
      intros HS (D & I & [std MT]). repeat split; intros H.
      - intros D' I' H'. apply hyp1; auto.
      - apply (hyp2 std); auto.
      - apply WeakT with T; trivial. now apply hyp3.
      - apply (hyp2 std); auto. intros rho. apply (tsoundness H); auto.
    Qed.



    (* Theorem 10 : variant for classical deduction, using LEM *)

    Definition LEM := forall P, P \/ ~ P.
    
    Theorem reduction_theorem_class (S : form -> Prop) :
      LEM -> T <<= S -> (exists D I, @standard D I /\ I ⊨=T S) -> reduction f P (tprv_class S).
    Proof.
      intros lem HS (D & I & [std MT]). split; intros H.
      - apply WeakT with T; trivial. now apply hyp3.
      - apply (hyp2 std); auto. intros rho. apply (tsoundness_class lem H); auto.
    Qed.
    
  End Reduction.



  (* Fact 11 : *)

  Definition list_theory (A : list form) :=
    fun phi => In phi A.

End FixSignature.



(* Main results *)

(* Theorem 25 : H10 reduces to Q', Q, and PA *)

From Undecidability.FOL Require Import PA Reductions.H10p_to_FA FA_facts.
From Undecidability.H10 Require Import H10p H10p_undec.

Existing Instance PA_funcs_signature.
Existing Instance PA_preds_signature.

(* We first show the three hypotheses regarding Q' *)

Definition Q' := list_theory FAeq.

Lemma PA_undec1 E :
  H10p E -> Q' ⊨T embed E.
Proof.
  intros HE D M HM rho. apply H10p_to_FA_sat; auto.
Qed.

(* A model is standard if it is isomorphic to nat *)

Print standard.

Lemma PA_undec2 D (M : interp D) E :
  standard D M -> M ⊨=T Q' -> M ⊨= embed E -> H10p E.
Proof.
  intros H1 H2 H3. apply standard_embed with (fun n => iO); auto.
Qed.

Lemma PA_undec3 (p : peirce) E :
  H10p E -> Q' ⊢T embed E.
Proof.
  intros H. exists FAeq. split; auto. now apply H10p_to_FA_prv'.
Qed.

(* Then the reductions to Q', Q, and PA all follow by reduction_theorem *)

Notation "P ⪯T T" := (exists f, treduction f P T) (at level 55).

Theorem undec_Q' :
  H10p ⪯T Q'.
Proof.
  exists embed. apply (reduction_theorem PA_undec1 PA_undec2 PA_undec3).
  - auto.
  - exists nat, interp_nat. split; try apply nat_standard.
    eauto using nat_is_FA_model.
Qed.

Theorem undec_Q :
  H10p ⪯T list_theory Qeq.
Proof.
  exists embed. apply (reduction_theorem PA_undec1 PA_undec2 PA_undec3).
  - firstorder.
  - exists nat, interp_nat. split; try apply nat_standard.
    eauto using nat_is_Q_model.
Qed.

Theorem undec_PA :
  H10p ⪯T PAeq.
Proof.
  exists embed. apply (reduction_theorem PA_undec1 PA_undec2 PA_undec3).
  - eauto using PAeq.
  - exists nat, interp_nat. split; try apply nat_standard.
    eauto using nat_is_PAeq_model.
Qed.



(* Theorem 26 : all extensions of Q' satisfied by the standard model are incompletene, using LEM *)

(* We first need to show the PA signature discrete and enumerable *)

Instance eqdec_PA_syms :
  eq_dec syms.
Proof.
  intros x y. unfold dec. decide equality.
Qed.

Instance eqdec_PA_preds :
  eq_dec preds.
Proof.
  intros x y. unfold dec. decide equality.
Qed.

Definition enum_PA_syms :
  enumerable__T syms.
Proof.
  apply enum_enumT. exists (fun _ => [Zero; Succ; Plus; Mult]).
  intros []; exists 0; auto.
Qed.

Definition enum_PA_preds :
  enumerable__T preds.
Proof.
  apply enum_enumT. exists (fun _ => [Eq]).
  intros []; exists 0; auto.
Qed.

(* The claim follows with complete_reduction and reduction_theorem_class *)

Theorem incompleteness_PA (T : form -> Prop) :
  LEM -> list_theory FAeq <<= T -> enumerable T -> complete T -> interp_nat ⊨=T T -> decidable (TM.HaltTM 1).
Proof.
  intros lem HFA HE HC HT. apply H10p_undec.
  apply (@complete_reduction _ _ enum_PA_syms _ enum_PA_preds _ T HE) with embed.
  - intros H. apply (@tsoundness_class _ _ lem _ T ⊥ H nat interp_nat (fun n => 0)). firstorder.
  - apply HC.
  - eapply (reduction_theorem_class PA_undec2 PA_undec3); trivial.
    exists nat, interp_nat. split; auto. apply nat_standard.
  - apply embed_is_closed.
Qed.



(* Theorem 34 : PCP reduces to Z', Z, and ZF, assuming standard models *)

From Undecidability.FOL.Reductions Require Import PCPb_to_ZFeq PCPb_to_ZF PCPb_to_ZFD.
From Undecidability.FOL Require Import Util.Aczel_CE Util.ZF_model ZF.
From Undecidability.PCP Require Import PCP PCP_undec.

(* We first show the three hypotheses regarding Z' *)

Existing Instance ZF_func_sig.
Existing Instance ZF_pred_sig.

Definition Z' := list_theory ZFeq'.

Lemma ZF_undec1 B :
  PCPb B -> Z' ⊨T solvable B.
Proof.
  intros HE D M HM rho. apply (PCP_ZFD (p:=intu)) in HE.
  apply (soundness HE). auto.
Qed.

(* A model is standard if all k ∈ om correspond to some n : nat *)

Print standard.

Lemma ZF_undec2 D (M : interp D) B :
  standard M -> M ⊨=T Z' -> M ⊨= solvable B -> PCPb B.
Proof.
  intros H1 H2 H3. apply PCP_ZFeq with (fun _ => ∅); auto.
Qed.

Lemma ZF_undec3 (p : peirce) B :
  PCPb B -> Z' ⊢T solvable B.
Proof.
  intros H. exists ZFeq'. split; auto. now apply PCP_ZFD.
Qed.

(* Then the reductions so Z', Z, and ZF all follow by reduction_theorem *)

Lemma undec_Z' :
  (exists D I, @standard D I /\ I ⊨=T Z') -> treduction solvable PCPb Z'.
Proof.
  apply (reduction_theorem ZF_undec1 ZF_undec2 ZF_undec3); trivial.
Qed.

Lemma undec_Z :
  (exists D I, @standard D I /\ I ⊨=T Zeq) -> treduction solvable PCPb Zeq.
Proof.
  apply (reduction_theorem ZF_undec1 ZF_undec2 ZF_undec3); trivial.
  eauto using Zeq.
Qed.

Lemma undec_ZF :
  (exists D I, @standard D I /\ I ⊨=T ZFeq) -> treduction solvable PCPb ZFeq.
Proof.
  apply (reduction_theorem ZF_undec1 ZF_undec2 ZF_undec3); trivial.
  eauto using ZFeq.
Qed.



(* Corollary 35 : the standard models required by the previous theorem can be constructed with CE and TED *)

Lemma CE_undec_Z' :
  CE -> treduction solvable PCPb Z'.
Proof.
  intros H. apply undec_Z'.
  destruct (extensionality_model_eq H) as (D & M & H1 & H2 & H3).
  exists D, M. split; trivial. eauto using Zeq.
Qed.

Lemma CE_undec_Z :
  CE -> treduction solvable PCPb Zeq.
Proof.
  intros H. apply undec_Z.
  destruct (extensionality_model_eq H) as (D & M & H1 & H2 & H3).
  exists D, M. split; trivial. auto.
Qed.

Lemma TD_undec_ZF :
  CE -> TD -> treduction solvable PCPb ZFeq.
Proof.
  intros HC HD. apply undec_ZF.
  destruct (normaliser_model_eq HC HD) as (D & M & H1 & H2 & H3).
  exists D, M. split; trivial. auto.
Qed.

(* Refinement : allowing intensional models disposes of CE *)

Lemma refined_undec_Z' :
  treduction solvable PCPb Z'.
Proof.
  apply undec_Z'.
  destruct intensional_model as (D & M & H1 & H2).
  exists D, M. split; trivial. auto.
Qed.



(* Theorem 36 : all extensions of Z' satisfied by a standard model are incompletene, using LEM *)

(* We first need to show the ZF signature discrete and enumerable *)

Instance eqdec_ZF_syms :
  eq_dec syms.
Proof.
  intros x y. unfold dec. decide equality.
Qed.

Instance eqdec_ZF_preds :
  eq_dec preds.
Proof.
  intros x y. unfold dec. decide equality.
Qed.

Definition enum_ZF_syms :
  enumerable__T syms.
Proof.
  apply enum_enumT. exists (fun _ => [eset; pair; power; union; om]).
  intros []; exists 0; auto.
Qed.

Definition enum_ZF_preds :
  enumerable__T preds.
Proof.
  apply enum_enumT. exists (fun _ => [elem; equal]).
  intros []; exists 0; auto.
Qed.

(* The claim follows with complete_reduction and reduction_theorem_class *)

Theorem incompleteness_ZF (T : form -> Prop) :
  LEM -> list_theory ZFeq' <<= T -> enumerable T -> complete T -> (exists D I, @standard D I /\ I ⊨=T T) -> decidable (TM.HaltTM 1).
Proof.
  intros lem HFA HE HC (Ds & Is & HI1 & HI2). apply PCPb_undec.
  apply (@complete_reduction _ _ enum_ZF_syms _ enum_ZF_preds _ T HE) with solvable.
  - intros H. apply (@tsoundness_class _ _ lem _ T ⊥ H Ds Is (fun n => ∅)). firstorder.
  - apply HC.
  - eapply (reduction_theorem_class ZF_undec2 ZF_undec3); trivial. now exists Ds, Is.
  - apply solvabe_bound.
Qed.



(* Theorem 44 : we obtain the same reductions for set theory only formulated with equality and membership *)

From Undecidability.FOL Require Import minZF PCPb_to_minZF minZF_undec.

(* See the file minZF_undec.v for a list of all reductions, we just record the axiom-free version here *)

Definition minZ' := list_theory minZFeq'.

Lemma undec_minZ' :
  PCPb ⪯T minZ'.
Proof.
  exists minsolvable. split.
  - intros B. rewrite (PCPb_entailment_minZFeq' B).
    split; intros H D M; eauto.
  - intros B. rewrite (PCPb_deduction_minZF' B). split; intros H.
    + exists minZFeq'. split; auto.
    + destruct H as [A[H1 H2]]. apply (Weak H2). auto.
Qed.



(* Theorem 45 : FOL with a single binary relation symbol is undecidable *)

From Undecidability.FOL Require Import binZF PCPb_to_binZF binZF_undec binFOL binFOL_undec sig_bin.

Existing Instance sig_empty.
Existing Instance sig_binary.

Lemma undec_valid :
  undecidable (@valid _ _ falsity_on).
Proof.
  apply binFOL_valid_undec.
Qed.

Lemma undec_prv_intu :
  undecidable (@prv _ _ falsity_on FullDeduction.intu nil).
Proof.
  apply binFOL_prv_intu_undec.
Qed.

Lemma undec_prv_class :
  LEM -> undecidable (@prv _ _ falsity_on FullDeduction.class nil).
Proof.
  intros lem. apply (undecidability_from_reducibility PCPb_undec).
  exists (fun B => impl binZF (binsolvable B)). intros phi.
  setoid_rewrite <- impl_prv. rewrite List.app_nil_r. split; intros H.
  - apply (@PCP_ZFD FullDeduction.class), (@rm_const_prv FullDeduction.class nil) in H.
    apply (Weak H). auto. cbn. unfold List.incl. apply List.in_rev.
  - apply PCP_ZFeq'; try apply intensional_model. apply (Weak (B:=binZF)) in H.
    + apply soundness_class in H; trivial.
      intros V M rho HM. apply min_correct; trivial.
      apply H. now apply min_axioms'.
    + unfold List.incl. apply List.in_rev.
Qed.
  



