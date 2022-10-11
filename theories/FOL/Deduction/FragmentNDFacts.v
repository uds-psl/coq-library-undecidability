(* * Natural Deduction *)

From Undecidability.Synthetic Require Import Definitions DecidabilityFacts EnumerabilityFacts ListEnumerabilityFacts ReducibilityFacts.
From Undecidability.FOL Require Import Syntax.Facts Syntax.Theories Syntax.Asimpl.
From Undecidability.FOL Require Export Deduction.FragmentND.
From Undecidability Require Import Shared.ListAutomation.
Import ListAutomationNotations.
Require Import Lia.
Require Import EqdepFacts.
Import FragmentSyntax.


Set Default Proof Using "Type".

Local Set Implicit Arguments.
Local Unset Strict Implicit.


#[local] Ltac comp := repeat (progress (cbn in *; autounfold in *)).

Section ND_def.

  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.

  Context {ff : falsity_flag}.
  Context {p : peirce}.


  Lemma impl_prv A B phi :
    (rev B ++ A) ⊢ phi -> A ⊢ (B ==> phi).
  Proof.
    revert A; induction B; intros A; cbn; simpl_list; intros.
    - firstorder.
    - eapply II. now eapply IHB.
  Qed.

  Theorem Weak A B phi :
    A ⊢ phi -> A <<= B -> B ⊢ phi.
  Proof.
    intros H. revert B.
    induction H; intros B HB; try unshelve (solve [econstructor; intuition]); try now econstructor.
  Qed.

  Hint Constructors prv : core.

  Theorem subst_Weak A phi xi :
    A ⊢ phi -> [phi[xi] | phi ∈ A] ⊢ phi[xi].
  Proof.
    induction 1 in xi |-*; comp.
    1-7:eauto using in_map.
    - apply AllI. setoid_rewrite map_map in IHprv. erewrite map_map, map_ext.
      apply IHprv. intros ?. cbn. now rewrite up_form.
    - specialize (IHprv xi). apply AllE with (t := t`[xi]) in IHprv. rewrite subst_comp in *.
      erewrite subst_ext; try apply IHprv. intros [|]; cbn; trivial.
      unfold funcomp. now setoid_rewrite subst_term_shift.
  Qed.

  Definition cycle_shift n x :=
    if Dec (n = x) then $0 else $(S x).
  Lemma cycle_shift_shift n phi :
    bounded n phi -> phi[cycle_shift n] = phi[↑].
  Proof.
    intros H. apply (bounded_subst H). intros k. unfold cycle_shift. destruct (Dec _); trivial; lia.
  Qed.

  Lemma cycle_shift_subject n phi :
    bounded (S n) phi -> phi[$n..][cycle_shift n] = phi.
  Proof.
    intros H. erewrite subst_comp, (bounded_subst H), subst_id; trivial.
    intros []; cbn; unfold cycle_shift; destruct (Dec _); trivial; lia.
  Qed.

  Lemma nameless_equiv_all' A phi n :
    bounded_L n A -> bounded (S n) phi -> [f[↑] | f ∈ A] ⊢ phi <-> A ⊢ phi[$n..].
  Proof.
    intros H1 H2. split; intros H.
    - apply (subst_Weak ($n..)) in H. rewrite map_map in *.
      erewrite map_ext, map_id in H; try apply H. intros. apply subst_shift.
    - apply (subst_Weak (cycle_shift n)) in H. rewrite (map_ext_in _ (subst_form ↑)) in H.
      + now rewrite cycle_shift_subject in H.
      + intros psi HP. now apply cycle_shift_shift, H1.
  Qed.

  Lemma nameless_equiv_all A phi :
    { t : nat | map (subst_form ↑) A ⊢ phi <-> A ⊢ phi[$t..] }.
  Proof.
    destruct (find_bounded_L (phi::A)) as [n H].
    exists n. apply nameless_equiv_all'.
    - intros ? ?. apply H. auto.
    - eapply bounded_up; try apply H; auto.
  Qed.

  Lemma AllI_named (A : list form) (phi : form) :
    (forall t, A ⊢ phi[t..]) -> A ⊢ ∀phi.
  Proof.
    intros H. apply AllI. 
    destruct (nameless_equiv_all A phi) as [t Ht].
    apply Ht, H.
  Qed.

  Lemma imps T phi psi :
    T ⊢ (phi → psi) <-> (phi :: T) ⊢ psi.
  Proof.
    split; try apply II.
    intros H. apply IE with phi; auto. apply (Weak H). auto.
  Qed.

  Lemma big_imps A B phi : (A ++ B) ⊢ phi <-> B ⊢ (impl A phi).
  Proof.
    induction A as [|psi A IH] in B,phi|-*; cbn; try tauto.
    split; intros Hprv.
    - apply II. apply IH. eapply Weak. 1: apply Hprv.
      intros x [->|[HA|HB]%in_app_iff]; apply in_app_iff.
      + right; now left.
      + now left.
      + right; now right.
    - eapply Weak. 1: apply (IH (psi::B)).
      + eapply IE. 1: eapply Weak; [apply Hprv|firstorder]. apply Ctx; now left.
      + intros x [HA|[->|HB]]%in_app_iff.
        * right. apply in_app_iff. now left.
        * now left.
        * right. apply in_app_iff. now right.
  Qed.

  Lemma big_imps_nil A phi : A ⊢ phi <-> [] ⊢ (impl A phi).
  Proof.
    specialize (big_imps A nil phi). rewrite <- (app_nil_end). easy.
  Qed.

  Lemma subst_forall_prv phi {N Gamma} :
    Gamma ⊢ (forall_times N phi) -> bounded N phi -> forall sigma, Gamma ⊢ phi[sigma].
  Proof.
    induction N in phi |-*; intros ?? sigma; cbn in *.
    - change sigma with (iter up 0 sigma).
      now rewrite (subst_bounded 0).
    - specialize (IHN (∀ phi) ).
      rewrite <-up_decompose.
      apply AllE. apply IHN. unfold forall_times.
      now rewrite <-iter_switch.
      now apply bounded_S_quant.
  Qed.

  Lemma prv_cut A B phi :
    A ⊢ phi -> (forall psi, psi el A -> B ⊢ psi) -> B ⊢ phi.
  Proof.
    induction A in phi |- *; intros H1 H2.
    - eapply Weak; eauto.
    - rewrite <- imps in H1. apply IHA in H1; auto. apply IE with a; trivial. now apply H2.
  Qed.

  Lemma prv_intu_peirce T φ : T ⊢I φ -> T ⊢ φ.
  Proof using.
    remember intu. induction 1. all: now eauto.
  Qed.

End ND_def.


Local Hint Constructors prv : core.

(* ** Rudimentary tactics for ND manipulations *)

Ltac subsimpl_in H :=
  rewrite ?up_term, ?subst_term_shift in H.

Ltac subsimpl :=
  rewrite ?up_term, ?subst_term_shift.

Ltac assert1 H :=
  match goal with |- (?phi :: ?T) ⊢ _ => assert (H : (phi :: T) ⊢ phi) by auto end.

Ltac assert2 H :=
  match goal with |- (?phi :: ?psi :: ?T) ⊢ _ => assert (H : (phi :: psi :: T) ⊢ psi) by auto end.

Ltac assert3 H :=
  match goal with |- (?phi :: ?psi :: ?theta :: ?T) ⊢ _ => assert (H : (phi :: psi :: theta :: T) ⊢ theta) by auto end.

Ltac assert4 H :=
  match goal with |- (?f :: ?phi :: ?psi :: ?theta :: ?T) ⊢ _ => assert (H : (f :: phi :: psi :: theta :: T) ⊢ theta) by auto end.

Ltac prv_all x :=
  apply AllI; edestruct (@nameless_equiv_all) as [x ->]; cbn; subsimpl.


(* ** Custom induction principle *)
Lemma prv_ind_full {Σ_funcs : funcs_signature} {Σ_preds : preds_signature} :
  forall P : peirce -> list (form falsity_on) -> (form falsity_on) -> Prop,
    (forall (p : peirce) (A : list form) (phi psi : form),
        (phi :: A) ⊢ psi -> P p (phi :: A) psi -> P p A (phi → psi)) ->
    (forall (p : peirce) (A : list form) (phi psi : form),
        A ⊢ (phi → psi) -> P p A (phi → psi) -> A ⊢ phi -> P p A phi -> P p A psi) -> 
    (forall (p : peirce) (A : list form) (phi : form),
        (map (subst_form ↑) A) ⊢ phi -> P p (map (subst_form ↑) A) phi -> P p A (∀ phi)) ->
    (forall (p : peirce) (A : list form) (t : term) (phi : form),
        A ⊢ (∀ phi) -> P p A (∀ phi) -> P p A (phi[t..])) ->
    (forall (p : peirce) (A : list form) (phi : form), A ⊢ ⊥ -> P p A ⊥ -> P p A phi) ->
    (forall (p : peirce) (A : list form) (phi : form), phi el A -> P p A phi) ->
    (forall (A : list form) (phi psi : form), P class A (((phi → psi) → phi) → phi)) ->
    forall (p : peirce) (l : list form) (f14 : form), l ⊢ f14 -> P p l f14.
Proof.
  intros. specialize (@prv_ind _ _ (fun ff => match ff with falsity_on => P | _ => (fun _ _ _ => True) end)). intros H'.
  apply H' with (ff := falsity_on); clear H'. all: intros; try destruct ff; trivial. all: intuition eauto 2.
Qed.




(* ** Enumerability of proofs *)

Section Enumerability.

  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.

  Variable list_Funcs : nat -> list syms.
  Hypothesis enum_Funcs' : list_enumerator__T list_Funcs syms.

  Variable list_Preds : nat -> list preds.
  Hypothesis enum_Preds' : list_enumerator__T list_Preds preds.

  Hypothesis eq_dec_Funcs : eq_dec syms.
  Hypothesis eq_dec_Preds : eq_dec preds.

  Instance eqdec_binop : eq_dec binop.
  Proof.
    intros x y. unfold dec. decide equality.
  Qed.

  Instance eqdec_quantop : eq_dec quantop.
  Proof.
    intros x y. unfold dec. decide equality.
  Qed.

  Definition list_binop (n : nat) := [Impl].

  Instance enum_binop :
    list_enumerator__T list_binop binop.
  Proof.
    intros []; exists 0; cbn; tauto.
  Qed.

  Definition list_quantop (n : nat) := [All].

  Instance enum_quantop :
    list_enumerator__T list_quantop quantop.
  Proof.
    intros []; exists 0; cbn; tauto.
  Qed.

  Lemma enumT_binop :
    enumerable__T binop.
  Proof.
    apply enum_enumT. exists list_binop. apply enum_binop.
  Qed.

  Lemma enumT_quantop :
    enumerable__T quantop.
  Proof.
    apply enum_enumT. exists list_quantop. apply enum_quantop.
  Qed.

  Instance enum_term' :
    list_enumerator__T (L_term _) term :=
    enum_term _.

  Instance enum_form' {ff : falsity_flag} :
    list_enumerator__T (L_form _ _ _ _) form :=
    enum_form _ _ _ _.

  Fixpoint L_ded {p : peirce} {b : falsity_flag} (A : list form) (n : nat) : list form :=
    match n with
    | 0 => A
    | S n =>   L_ded A n ++
    (* II *)   concat ([ [ phi → psi | psi ∈ L_ded (phi :: A) n ] | phi ∈ L_T form n ]) ++
    (* IE *)   [ psi | (phi, psi) ∈ (L_ded A n × L_T form n) , (phi → psi el L_ded A n) ] ++
    (* AllI *) [ ∀ phi | phi ∈ L_ded (map (subst_form ↑) A) n ] ++
    (* AllE *) [ phi[t..] | (phi, t) ∈ (L_T form n × L_T term n), (∀ phi) el L_ded A n ] ++
    (* Exp *)  (match b with falsity_on => fun A =>
                [ phi | phi ∈ L_T form n, ⊥ el @L_ded _ falsity_on A n ]
                | _ => fun _ => nil end A) ++
    (* Pc *)   (if p then
                [ (((phi → psi) → phi) → phi) | (pair phi psi) ∈ (L_T form n × L_T form n) ]
                else nil)
    end.

  Opaque in_dec.

  Lemma enum_prv {p : peirce} {b : falsity_flag} A :
    list_enumerator (L_ded A) (prv A).
  Proof with try (eapply cum_ge'; eauto; lia).
    split.
    - rename x into phi. induction 1; try congruence; subst.
      + destruct IHprv as [m1], (el_T phi) as [m2]. exists (1 + m1 + m2). cbn. in_app 2.
        eapply in_concat_iff. eexists. split. 2:in_collect phi... in_collect psi...
      + destruct IHprv1 as [m1], IHprv2 as [m2], (el_T psi) as [m3]; eauto.
        exists (1 + m1 + m2 + m3).
        cbn. in_app 3. in_collect (phi, psi)...
      + destruct IHprv as [m]. exists (1 + m). cbn. in_app 4. in_collect phi...
      + destruct IHprv as [m1], (el_T t) as [m2], (el_T phi) as [m3]. exists (1 + m1 + m2 + m3).
        cbn. in_app 5. in_collect (phi, t)...
      + destruct IHprv as [m1], (el_T phi) as [m2]. exists (1 + m1 + m2). cbn. in_app 6. in_collect phi...
      + now exists 0.
      + destruct (el_T phi) as [m1], (el_T psi) as [m2]. exists (1 + m1 + m2). cbn. in_app 7. in_collect (phi, psi)...
    - intros [m]; induction m in A, x, H |-*; cbn in *.
      + now apply Ctx.
      + destruct p, b; inv_collect. all: eauto 3.
        * eapply IE; apply IHm; eauto.
        * eapply IE; apply IHm; eauto.
        * eapply IE; apply IHm; eauto.
        * eapply IE; apply IHm; eauto.
  Qed.

  Fixpoint L_con `{falsity_flag} (L : nat -> list form) (n : nat) : list (list form) :=
    match n with
    | 0 => [ nil ]
    | S n => L_con L n ++ [ phi :: A | (pair phi A) ∈ (L n × L_con L n) ]
    end.

  Lemma enum_el X (p : X -> Prop) L x :
    list_enumerator L p -> p x -> exists m, x el L m.
  Proof.
    firstorder.
  Qed.
  Arguments enum_el {X p L} x _ _.

  Lemma enum_p X (p : X -> Prop) L x m :
    list_enumerator L p -> x el L m -> p x.
  Proof.
    firstorder.
  Qed.

  Definition containsL `{falsity_flag} A (T : form -> Prop) :=
    forall psi, psi el A -> T psi.

  Lemma enum_containsL `{falsity_flag} T L :
    cumulative L -> list_enumerator L T -> list_enumerator (L_con L) (fun A => containsL A T).
  Proof with try (eapply cum_ge'; eauto; lia).
    intros HL He. split.
    - induction x as [| phi A]; intros HT.
      + exists 0. firstorder.
      + destruct IHA as [m1], (enum_el phi He) as [m2]. 1,2,3: firstorder.
        exists (1 + m1 + m2). cbn. in_app 2. in_collect (phi, A)...
    - intros [m]. induction m in x, H0 |-*; cbn in *.
      + destruct H0 as [<- | []]. firstorder.
      + inv_collect. apply IHm in H2. apply (enum_p He) in H0. unfold containsL in *. firstorder congruence.
  Qed.

  Fixpoint L_tded {p : peirce} {b : falsity_flag} (L : nat -> list form) (n : nat) : list form :=
    match n with
    | 0 => nil
    | S n => L_tded L n ++ concat ([ L_ded A n | A ∈ L_con L n ])
    end.

  Lemma enum_tprv {p : peirce} {b : falsity_flag} T L :
    list_enumerator L T -> list_enumerator (L_tded (cumul L)) (tprv T).
  Proof with try (eapply cum_ge'; eauto; lia).
    intros He.
    assert (HL : list_enumerator (cumul L) T) by now apply list_enumerator_to_cumul.
    split.
    - intros (A & [m1] % (enum_el A (@enum_containsL _ _ (cumul L) (to_cumul_cumulative L) HL)) & [m2] % (enum_el x (enum_prv A))).
      exists (1 + m1 + m2). cbn. in_app 2. eapply in_concat_iff. eexists. split. 2: in_collect A... idtac...
    - intros [m]. induction m in x, H |-*; cbn in *. 1: contradiction. inv_collect. exists x1. split.
      + eapply (enum_p (enum_containsL (to_cumul_cumulative L) HL)); eauto.
      + eapply (enum_p (enum_prv x1)); eassumption.
  Qed.

End Enumerability.


Section TheoryManipulation.

  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.
  Context {p : peirce} {ff : falsity_flag}.
  Context {HF : eq_dec syms} {HP : eq_dec preds}.
  Lemma prv_T_impl T phi psi :
    (T ⋄ phi) ⊢T psi -> T ⊢T (phi → psi).
  Proof using HF HP ff p Σ_funcs Σ_preds.
    intros (A & HA1 & HA2). exists (remove (dec_form _ _ _ _) phi A); split.
    - intros f [[] % HA1 Hf2] % in_remove; subst; intuition.
    - eapply II, Weak. 1: apply HA2. transitivity (phi :: A). 1: eauto. intros a [-> | Ha].
      + now left.
      + destruct (dec_form _ _ _ _ a phi) as [->|Hr]. 1:now left.
        right. now eapply in_in_remove.
  Qed.

  Lemma prv_T_remove T phi psi :
    T ⊢T phi -> T ⋄ phi ⊢T psi -> T ⊢T psi.
  Proof using HF HP ff p Σ_funcs Σ_preds.
    intros (A & HA1 & HA2) (B & HB1 & HB2) % prv_T_impl.
    use_theory (A ++ B).
    - now intros psi1 [H1|H2]%in_app_iff; [apply HA1 | apply HB1].
    - eapply IE; eapply Weak. 1,3: eassumption.
      all: intros x Hx; apply in_app_iff; eauto.
  Qed.

  Lemma prv_T_comp T phi psi xi :
    T ⋄ phi ⊢T xi -> T ⋄ psi ⊢T phi -> T ⋄ psi ⊢T xi.
  Proof using HF HP.
    intros (A & HA1 & HA2) % prv_T_impl (B & HB1 & HB2) % prv_T_impl.
    use_theory (psi :: A ++ B).
    - now intros psi1 [->|[H1|H2]%in_app_iff]; [now right | |]; left; [apply HA1 | apply HB1].
    - eapply IE. 1: eapply Weak. 1: apply HA2. 2: eapply IE.
      2-3: eapply Weak. 2: eapply HB2. 3: apply (@Ctx _ _ _ _ (psi::nil)); now left.
      + intros a Ha; right; apply in_app_iff; now left.
      + intros b Hb; right; apply in_app_iff; now right.
      + intros x [->|[]]; now left.
  Qed.

  Lemma elem_prv T phi :
    phi ∈ T -> T ⊢T phi.
  Proof.
    intros ?. use_theory [phi]. 2:apply Ctx; now left.
    intros psi [->|[]]. apply H.
  Qed.

  Lemma Weak_T T1 T2 phi :
    T1 ⊢T phi -> T1 ⊑ T2 -> T2 ⊢T phi.
  Proof.
    intros (A & HA1 & HA2) HT2. exists A. split. 2:easy. intros psi H; now apply HT2, HA1.
  Qed.
End TheoryManipulation.

Section Closedness.

  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.
  Context {p : peirce} {ff : falsity_flag}.

  Definition capture_subs n x := $(x + n).

  Lemma capture_extract n A phi :
    A ⊢ subst_form (capture_subs n) (capture All n phi) -> A ⊢ subst_form (capture_subs 0) phi.
  Proof.
    induction n; comp; intuition. apply IHn. apply (AllE (var n)) in H. rewrite subst_comp in H.
    erewrite subst_ext. 1: apply H. intros [| x]; unfold capture_subs; cbn; f_equal; lia.
  Qed.
    
  Context {Funcs_eq_dec : eq_dec Σ_funcs}.
  Context {Preds_eq_dec : eq_dec Σ_preds}.

  Lemma close_extract A phi :
    A ⊢ close All phi -> A ⊢ phi.
  Proof.
    intros H. assert (Hclosed : closed (close All phi)) by apply close_closed.
    unfold close in *. destruct (find_bounded phi) as [n Hn]; cbn in *.
    erewrite <- subst_id with (sigma := fun x => $x) in H.
    erewrite (@bounded_subst _ _ _ _ _ _ _ (capture_subs n)) in H.
    2: exact Hclosed. 3:easy. 2: lia.
    apply capture_extract in H. rewrite subst_id in H; intuition. unfold capture_subs. f_equal. lia.
  Qed.

End Closedness.

Section DNFacts.

  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.
  Lemma DN A phi: A ⊢C (¬ (¬ phi)) -> A ⊢C phi.
  Proof.
    intros H. eapply IE. 1: apply Pc. eapply II.
    apply Exp. eapply IE. 2: apply Ctx; now left.
    eapply Weak. 1: apply H. intros a Ha; now right.
  Qed.
  Lemma DN_into {p:peirce} A phi: A ⊢ phi -> A ⊢ (¬ (¬ phi)).
  Proof.
    intros H. apply II. eapply IE. 1: apply Ctx; now left. eapply Weak; [apply H|].
    firstorder.
  Qed.

  Lemma XMc A (phi chi : form) : (phi::A) ⊢C chi -> ((¬ phi)::A) ⊢C chi -> A ⊢C chi.
  Proof.
    intros HA HB. eapply IE with ((phi → chi) → (¬phi → chi) → chi).
    - eapply II. eapply IE. 1: eapply IE. 1: apply Ctx; now left.
      1-2: eapply Weak; [eapply II|]. 1: apply HA. 2: apply HB. 1-2: intros a Ha; now right.
    - eapply DN. apply II. eapply IE. 1: apply Ctx; now left. eapply II. eapply II.
      eapply IE. 1: apply Ctx; now left.
      eapply II. eapply IE. 1: apply Ctx; do 3 right; now left. do 2 eapply II.
      eapply IE. 1: apply Ctx; right; now left.
      apply Ctx; now eauto.
  Qed.

  Lemma DN_T T phi : T ⊢TC (¬¬phi) -> T ⊢TC phi.
  Proof.
    intros (A & HT & HA). exists A. split; [apply HT|now apply DN].
  Qed.

End DNFacts.

Section RefutationComp.
  Context {Σ_funcs : funcs_signature} {Σ_preds : preds_signature}.
  Context {HF : eq_dec Σ_funcs} {HP : eq_dec Σ_preds}.
  
  Lemma refutation_prv T phi :
    T ⊢TC phi <-> (T ⋄ ¬ phi) ⊢TC ⊥.
  Proof using HF HP.
    split.
    - intros (A & HA1 & HA2). use_theory (¬ phi :: A).
      + intros psi [<-|Ha]. 1: now right. left. now apply HA1.
      + eapply IE. 1: apply Ctx; now left. eapply Weak. 1: apply HA2. intros a Ha; now right.
    - intros (A & HA1 & HA2) % prv_T_impl. use_theory A. now apply DN.
  Qed.
End RefutationComp.

Section FlagsTransport.
  Context {Σ_funcs : funcs_signature} {Σ_preds : preds_signature}.
  Context {p : peirce}.
  Context {ff : falsity_flag}.

  Lemma prv_transport_to_falsity  A phi :
    A ⊢ phi -> (map to_falsity A) ⊢ (to_falsity phi).
  Proof.
    intros H; induction H.
    - cbn. apply II. apply IHprv.
    - cbn. eapply IE. 1: now apply IHprv1. now apply IHprv2.
    - cbn. apply AllI. rewrite map_map in *.
      erewrite map_ext. 1: now apply IHprv.
      intros a. rewrite <- ! subst_falsity_id.
      rewrite subst_falsity_comm. now cbn.
    - rewrite <- subst_falsity_id.
      change (⊥) with (⊥[t..]). rewrite <- subst_falsity_comm.
      apply AllE. rewrite subst_falsity_id. now apply IHprv.
    - apply Exp. apply IHprv.
    - apply Ctx. now apply in_map.
    - apply Pc.
  Qed.

  Lemma prv_transport_to_class A phi :
    A ⊢ phi -> A ⊢C phi.
  Proof.
    induction 1.
    - now apply II.
    - eapply IE. 1: apply IHprv1. easy.
    - now apply AllI.
    - now apply AllE.
    - now apply Exp.
    - now apply Ctx.
    - apply Pc.
  Qed.
(*
  Ltac resolve_existT :=
    inversion 1; subst;
    repeat match goal with
             H : existT _ _ _ = existT _ _ _ |- _ => try apply Eqdep_dec.inj_pair2_eq_dec in H; [|try decide equality]
           end.


  Lemma prv_transport_from_falsity' 
    {ff1 ff2 : falsity_flag}
    A' (phi' : @form _ _ _ ff2)
    A (phi : @form _ _ _ ff1) 
    (Heqn : ff2 = falsity_on) : A' ⊢ phi' -> match ff2 
      as ff return list (@form _ _ _ ff) -> @form _ _ _ ff -> Prop 
      with falsity_off => fun A' phi' => False 
         | falsity_on => fun A' phi' => A' = map to_falsity A -> phi' = to_falsity phi -> A ⊢ phi
    end A' phi'.
  Proof.
    induction 1 in A,phi,Heqn|-*; try (destruct ff; try congruence); intros HeqA Heqphi.
    - destruct phi as [|t1 t2|ff [] phi psi'|ff [] phi]; cbn in Heqphi; try congruence.
      apply II. apply IHprv. 1:easy. cbn. f_equal. 2: easy.
      all: injection Heqphi; intros He1 He2.
      all: apply Eqdep_dec.inj_pair2_eq_dec in He1; [|decide equality].
      all: apply Eqdep_dec.inj_pair2_eq_dec in He2; [|decide equality].
      all: congruence.
    - eapply IE. *)
End FlagsTransport.

Section NegativeTranslation.
  Context {Σ_funcs : funcs_signature} {Σ_preds : preds_signature}.

  Fixpoint negative_translation {ff:falsity_flag} (phi : @form _ _ _ ff) : @form _ _ _ falsity_on := match phi with
    falsity => falsity
  | atom P v => ¬¬(atom P v)
  | bin Impl phi psi => (negative_translation phi) → (negative_translation psi)
  | quant All phi => ∀ (negative_translation phi)
  end.

  Lemma nt_impl {ff:falsity_flag} A phi : negative_translation (impl A phi) = impl (map negative_translation A) (negative_translation phi).
  Proof.
    induction A as [|psi A IH]; cbn; congruence.
  Qed.

  Lemma nt_subst {ff:falsity_flag} phi σ : negative_translation (phi[σ]) = (negative_translation phi)[σ].
  Proof.
    induction phi as [| |?[]|?[]] in σ|-*; try easy.
    - cbn. now rewrite IHphi1, IHphi2.
    - cbn. now rewrite IHphi.
  Qed.

  Lemma nt_dn_float' {p:peirce} {ff:falsity_flag} A phi:
   A ⊢ ((¬¬negative_translation phi) → negative_translation phi).
  Proof.
  revert A. induction phi as [| |?[]|?[]]; intros A; cbn.
  - apply II. eapply IE. 1: apply Ctx; now left. apply II. apply Ctx; now left.
  - apply II. apply II. eapply IE. 1: apply Ctx; right; now left.
    apply II. eapply IE. 1: apply Ctx; now left. apply Ctx; right; now left.
  - apply II. apply II. eapply IE. 1: apply IHphi2. apply II.
    eapply IE. 1: apply Ctx; right; right; now left. apply II.
    eapply IE. 1: apply Ctx; right; now left.
    eapply IE. 1: apply Ctx; now left.
    apply Ctx; right; right; now left.
  - apply II. apply AllI. cbn. eapply IE. 1: apply IHphi.
    apply II. eapply IE. 1: apply Ctx; right; now left.
    apply II. eapply IE. 1: apply Ctx; right; now left.
    assert ((negative_translation phi)[up ↑][$0..] = negative_translation phi) as <- by now asimpl.
    apply AllE. apply Ctx; left; now asimpl.
  Qed.

  Lemma nt_dn_float {p:peirce} {ff:falsity_flag} A phi : 
    A ⊢ (¬¬negative_translation phi) -> A ⊢ negative_translation phi.
  Proof.
    intros H. eapply IE. 1: apply nt_dn_float'. easy.
  Qed.

  Lemma nt_peirce {p:peirce} {ff:falsity_flag} A phi psi: 
    A ⊢ negative_translation (((phi → psi) → phi) → phi).
  Proof.
    cbn. apply II.
    apply nt_dn_float.
    apply II. eapply IE. 1: apply Ctx; now left.
    eapply IE. 1: apply Ctx; right; now left.
    apply II. apply Exp. eapply IE. 1: apply Ctx; right; now left.
    apply Ctx. now left.
  Qed.

  Lemma nt_Cprv_to_Iprv {p1 : peirce} {ff:falsity_flag} A phi :
    A ⊢C phi -> (map negative_translation A) ⊢ (negative_translation phi).
  Proof.
    remember class as p2. induction 1; cbn in *.
    all: try specialize (IHprv Heqp2).
    all: try specialize (IHprv1 Heqp2).
    all: try specialize (IHprv2 Heqp2).
    - eapply II. now apply IHprv.
    - eapply IE. 1: apply IHprv1. apply IHprv2.
    - eapply AllI. rewrite map_map in *. erewrite map_ext. 1: apply IHprv.
      intros a; cbn. now rewrite nt_subst.
    - rewrite nt_subst. eapply AllE. apply IHprv.
    - eapply Exp. apply IHprv.
    - eapply Ctx. now apply in_map.
    - apply nt_peirce.
  Qed.

  Lemma nt_Cprv_equiv A phi : 
    A ⊢C phi <-> A ⊢C (negative_translation phi).
  Proof.
    revert A. induction phi as [| |[]|[]] using form_ind_falsity; intros A; cbn; split; intros Hprv.
    - easy.
    - easy.
    - eapply DN_into. easy.
    - eapply DN. easy. 
    - apply II. apply IHphi2. eapply IE. 1: eapply Weak; [apply Hprv|firstorder].
      apply IHphi1. apply Ctx; now left.
    - apply II. apply IHphi2. eapply IE. 1: eapply Weak; [apply Hprv|firstorder].
      apply IHphi1. apply Ctx; now left.
    - apply (subst_Weak ↑) in Hprv. asimpl in Hprv.
      eapply (AllE $0) in Hprv. asimpl in Hprv.
      apply AllI. apply IHphi. apply Hprv.
    - apply (subst_Weak ↑) in Hprv. asimpl in Hprv.
      eapply (AllE $0) in Hprv. asimpl in Hprv.
      apply AllI. apply IHphi. apply Hprv.
  Qed.


  Lemma nt_bounded {ff:falsity_flag} n phi : bounded n phi -> bounded n (negative_translation phi).
  Proof.
    induction 1; cbn.
    - solve_bounds. now econstructor.
    - destruct binop. now solve_bounds.
    - destruct quantop. now solve_bounds.
    - solve_bounds.
  Qed.

  #[local] Existing Instance falsity_on.
  Lemma nt_correct A phi:
    (map negative_translation A) ⊢I negative_translation phi -> A ⊢C phi.
  Proof.
    intros H.
    apply big_imps_nil. apply nt_Cprv_equiv.
    eapply prv_transport_to_class.
    rewrite nt_impl. apply big_imps_nil in H. apply H.
  Qed.

  Lemma nt_correct_theory T phi:
    (tmap negative_translation T) ⊢TI negative_translation phi -> T ⊢TC phi.
  Proof.
    intros (? & (A & -> & HA1) % tmap_contains_L & HA2 % nt_correct).
    now exists A.
  Qed.

End NegativeTranslation.






