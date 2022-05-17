(** * Abstract Undecidability and Incompleteness *)

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



(* Post's Theorem *)

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

Lemma enumerable_equiv X (P Q : X -> Prop) :
  (forall x, P x <-> Q x) -> enumerable P -> enumerable Q.
Proof.
  intros H [f Hf]. exists f. intros x. rewrite <- H. apply Hf.
Qed.




Section Abstract.

  (** ** Abstract Incompleteness *)

  Variable sentences : Type.
  Hypothesis sentences_discrete : discrete sentences.

  Variable provable : sentences -> Prop.
  Hypothesis provable_enum : enumerable provable.

  Variable neg : sentences -> sentences.

  Hypothesis neg_dec : forall phi, { psi | phi = neg psi } + (forall psi, phi <> neg psi).
  Hypothesis neg_inj : forall phi psi, neg phi = neg psi -> phi = psi.
  Hypothesis consistency : forall phi, ~ (provable phi /\ provable (neg phi)).

  Lemma refutable_enum :
    enumerable (fun phi => provable (neg phi)).
  Proof.
    destruct provable_enum as [f Hf]. unshelve eexists.
    - intros n. destruct (f n) as [phi|].
      + destruct (neg_dec phi) as [[psi _]|H].
        * exact (Some psi).
        * exact None.
      + exact None.
    - intros phi. cbn. split; intros H.
      + apply Hf in H as [n Hn]. exists n. rewrite Hn. destruct neg_dec as [[psi Hp]|Hp].
        * f_equal. now apply neg_inj.
        * exfalso. now apply (Hp phi).
      + destruct H as [n Hn]. destruct (f n) as [psi|] eqn: Heq; try congruence.
        destruct neg_dec as [[theta Hp]|Hp]; try congruence.
        apply Hf. exists n. congruence.
  Qed.

  Definition completeness :=
    forall phi, provable phi \/ provable (neg phi).

  Lemma completeness_decidable :
    completeness -> decidable provable.
  Proof.
    intros HC. apply weakPost.
    - apply sentences_discrete.
    - intros phi. destruct (HC phi) as [H|H]; try now left.
      right. intros H'. now apply (@consistency phi).
    - apply provable_enum.
    - apply enumerable_equiv with (fun phi => provable (neg phi)).
      + intros phi. split; intros Hp.
        * intros H. now apply (@consistency phi).
        * destruct (HC phi) as [H|H]; tauto.
      + apply refutable_enum.
  Qed.

  (** ** Abstract Undecidability *)

  Variable models : Type.
  Variable sat : models -> sentences -> Prop.

  Definition valid phi :=
    forall M, sat M phi.

  Hypothesis soundness : forall phi, provable phi -> valid phi.

  Variable standard : models -> Prop.
  Hypothesis standard_exists : exists M, standard M.

  Section Reduction.

    Variable X : Type.
    Variable p : X -> Prop.

    Hypothesis F : X -> sentences.
    Hypothesis F_provable : forall x, p x -> provable (F x).
    Hypothesis F_standard : forall M x, standard M -> sat M (F x) -> p x.

    Theorem reduction_provable :
      reduction F p provable.
    Proof.
      intros x. split; try apply F_provable.
      intros H % soundness. destruct standard_exists as [M HM].
      apply (F_standard HM). apply H.
    Qed.

    Theorem reduction_valid :
      reduction F p valid.
    Proof.
      intros x. split; intros H.
      - apply soundness, F_provable, H.
      - destruct standard_exists as [M HM]. apply (F_standard HM), H.
    Qed.

    Theorem incompleteness :
      completeness -> decidable p.
    Proof.
      intros H. eapply dec_red.
      - exists F. apply reduction_provable.
      - now apply completeness_decidable.
    Qed.

  End Reduction.

End Abstract.



(** ** Instantiation to first-order logic *)

From Undecidability.FOL Require Import FullSyntax Incompleteness.Axiomatisations.

Lemma reduction_equiv X Y (P P' : X -> Prop) (Q Q' : Y -> Prop) f :
  (forall x, P x <-> P' x) -> (forall y, Q y <-> Q' y) -> reduction f P Q -> reduction f P' Q'.
Proof.
  firstorder.
Qed.

Section Instantiation.

  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.

  Fact abs_reduction_theorem (T : form -> Prop) X (P : X -> Prop) f (standard : forall D : Type, interp D -> Prop) :
    (forall x : X, P x -> T ⊨T f x) ->
    (forall (D : Type) (I : interp D) rho (x : X), standard D I -> T <<= (sat rho) -> rho ⊨ f x -> P x) ->
    (forall (p : peirce) (x : X), P x -> T ⊢T f x) ->
    forall S : form -> Prop, T <<= S -> (exists D (I : interp D) (d : D), standard D I /\ I ⊨=T S) -> treduction f P S.
  Proof.
    intros H1 H2 H3 S HS HM. split.
    - eapply reduction_equiv. 1: reflexivity.
      2: unshelve eapply (@reduction_valid form (tprv S) {D & {I : interp D & {rho | S <<= (sat rho)}}}).
      3: intros [D[I[rho Hr]]] phi; exact (rho ⊨ phi).
      + unfold Abstract.valid. intros phi. split.
        * intros H D I rho Hp. specialize (H (existT _ D (existT _ I (exist _ rho Hp)))). apply H.
        * intros H [D[I[rho Hr]]]. apply H, Hr.
      + exact intu.
      + intros [D[I[rho Hr]]]. exact (standard D I).
      + intros phi Hp. unfold Abstract.valid. intros [D[I[rho Hr]]]. apply (tsoundness Hp), Hr.
      + destruct HM as [D[I[d H]]]. unshelve eexists.
        * exists D, I, (fun _ => d). intros phi Hp. now apply H.
        * cbn. apply H.
      + intros phi Hp. now eapply WeakT; try apply H3.
      + cbn. intros [D[I[rho Hr]]] x HI. eapply H2; auto.
    - unshelve eapply (@reduction_provable form (tprv S) {D & {I : interp D & {rho | S <<= (sat rho)}}}).
      + intros [D[I[rho Hr]]] phi; exact (rho ⊨ phi).
      + intros [D[I[rho Hr]]]. exact (standard D I).
      + intros phi Hp. unfold Abstract.valid. intros [D[I[rho Hr]]]. apply (tsoundness Hp), Hr.
      + destruct HM as [D[I[d H]]]. unshelve eexists.
        * exists D, I, (fun _ => d). intros phi Hp. now apply H.
        * cbn. apply H.
      + intros phi Hp. now eapply WeakT; try apply H3.
      + cbn. intros [D[I[rho Hr]]] x HI. eapply H2; auto.
  Qed.

  Context {enum_funcs : enumerable__T Σ_funcs} {eqdec_funcs : eq_dec syms}.
  Context {enum_preds : enumerable__T Σ_preds} {eqdec_preds : eq_dec preds}.

  Instance eqdec_on :
    EqDecPoint falsity_flag falsity_on.
  Proof.
    intros ff. decide equality.
  Qed.

  Instance EqDec_syms : EqDec syms.
  Proof.
    intros x y. apply eqdec_funcs.
  Qed.

  Instance EqDec_preds : EqDec preds.
  Proof.
    intros x y. apply eqdec_preds.
  Qed.

  Definition closed phi :=
    (if bounded_dec phi 0 then true else false) = true.

  Lemma closed_mere phi (H H' : closed phi) :
    H = H'.
  Proof.
    apply EqDec.peq_proofs_unicity.
  Qed.

  Lemma bounded_closed phi :
    bounded 0 phi <-> closed phi.
  Proof.
    unfold closed. destruct bounded_dec; intuition congruence.
  Qed.

  Lemma closed_dec phi :
    dec (closed phi).
  Proof.
    eapply dec_transfer; try apply bounded_closed. apply bounded_dec.
  Qed.

  Lemma bot_closed :
    closed ⊥.
  Proof.
    apply bounded_closed. constructor.
  Qed.

  Lemma closed_discrete :
    discrete {phi | closed phi}.
  Proof.
    apply decidable_iff. constructor. intros [[phi H1] [psi H2]].
    destruct dec_form with falsity_on phi psi as [->|H]; eauto.
    1,2: intros x y; unfold dec; decide equality.
    - left. f_equal. apply closed_mere.
    - right. intros [=]. tauto.
  Qed.

  Lemma closed_enum :
    enumerable__T form -> enumerable__T {phi | closed phi}.
  Proof.
    intros [f Hf]. unshelve eexists.
    - intros n. destruct (f n) as [phi|].
      + destruct (closed_dec phi) as [H|_].
        * apply Some. now exists phi.
        * exact None.
      + exact None.
    - intros [phi Hp]. destruct (Hf phi) as [n Hn].
      exists n. cbn. rewrite Hn. destruct closed_dec as [H|H]; try tauto.
      repeat f_equal. apply closed_mere.
  Qed.

  Lemma neg_dec phi :
    { psi | phi = ¬ psi } + (forall psi, phi <> ¬ psi).
  Proof.
    depelim phi.
    - apply EqDec.inj_right_sigma_point in H as ->. right. intros phi. congruence.
    - right. intros phi. congruence.
    - destruct b0. 1,2: right; intros phi; congruence.
      destruct dec_form with falsity_on phi2 ⊥ as [->|H]; eauto.
      1,2: intros x y; unfold dec; decide equality.
      right. intros phi. intros [=]. resolve_existT. now apply H.
    - right. intros psi. congruence.
  Qed.

  Fact abstr_complete_decidable (T : form -> Prop) :
    enumerable T -> ~ T ⊢TC ⊥ -> complete T -> decidable (fun phi : form => bounded 0 phi /\ T ⊢TC phi).
  Proof.
    intros H1 H2 H3. apply dec_red with {phi | closed phi} (fun phi => T⊢TC (proj1_sig phi)).
    { exists (fun phi => match closed_dec phi with left H => exist _ phi H | _ => exist _ ⊥ bot_closed end).
      intros phi. rewrite bounded_closed. destruct closed_dec; cbn; tauto. }
    unshelve eapply completeness_decidable.
    - intros [phi Hp % bounded_closed]. exists (¬ phi). apply bounded_closed. repeat constructor. apply Hp.
    - apply closed_discrete.
    - apply enumerable_red with form (fun phi => closed phi /\ T ⊢TC phi).
      { exists (fun phi => proj1_sig phi). intros [phi Hp]. cbn. tauto. }
      { apply closed_enum. unshelve eapply form_enumerable; eauto. }
      { apply form_discrete. }
      apply enumerable_conj; try apply form_discrete.
      + apply dec_count_enum; try unshelve eapply form_enumerable; eauto.
        apply decidable_iff. constructor. intros phi. unshelve eapply closed_dec; eauto.
      + unshelve eapply tprv_enumerable; eauto.
    - intros [phi H]. cbn. destruct (neg_dec phi) as [[psi Hp]|Hp].
      + left. unshelve eexists.
        * exists psi. rewrite Hp in H. rewrite <- bounded_closed in *.
          inversion H. now repeat resolve_existT.
        * cbn. subst. f_equal. apply closed_mere.
      + right. intros [psi Hp']. intros [=]. now apply Hp in H4.
    - cbn. intros [phi H] [psi H']. cbn. intros [=]. resolve_existT. f_equal. apply closed_mere.
    - cbn. intros [phi Hp] [[A [HA1 HA2]] [B [HB1 HB2]]]. cbn in *. 
      apply H2. exists (A ++ B). split.
      + intros psi [H|H] % in_app_iff; intuition.
      + apply IE with phi. apply (Weak HB2). 1:apply incl_appr, incl_refl. apply (Weak HA2). apply incl_appl,incl_refl.
    - intros [phi Hp]; cbn. apply bounded_closed in Hp. now apply H3.
  Qed.

End Instantiation.
      


  
