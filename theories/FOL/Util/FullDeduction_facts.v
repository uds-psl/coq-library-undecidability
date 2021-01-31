(* * Natural Deduction *)

From Undecidability.Synthetic Require Import Definitions DecidabilityFacts EnumerabilityFacts ListEnumerabilityFacts ReducibilityFacts.
From Undecidability.FOL.Util Require Import FullTarski_facts Syntax_facts.
From Undecidability.FOL.Util Require Export FullDeduction.
From Undecidability Require Import Shared.ListAutomation.
Import ListAutomationNotations.
Local Set Implicit Arguments.
Require Import Lia.




Ltac comp := repeat (progress (cbn in *; autounfold in *)).

Section ND_def.

  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.

  Context {ff : falsity_flag}.
  Context {p : peirce}.

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
    1-2,7-15: eauto using in_map.
    - apply AllI. setoid_rewrite map_map in IHprv. erewrite map_map, map_ext.
      apply IHprv. intros ?. cbn. now rewrite up_form.
    - specialize (IHprv xi). apply AllE with (t0 := t`[xi]) in IHprv. rewrite subst_comp in *.
      erewrite subst_ext; try apply IHprv. intros [|]; cbn; trivial.
      unfold funcomp. now setoid_rewrite subst_term_shift.
    - specialize (IHprv xi). eapply ExI with (t0 := t`[xi]). rewrite subst_comp in *.
      erewrite subst_ext; try apply IHprv. intros [|]; cbn; trivial.
      unfold funcomp. now setoid_rewrite subst_term_shift.
    - eapply ExE in IHprv1. eassumption. rewrite map_map.
      specialize (IHprv2 (up xi)). setoid_rewrite up_form in IHprv2.
      erewrite map_map, map_ext in IHprv2; try apply IHprv2. apply up_form.
  Qed.

  Definition cycle_shift n x :=
    if Dec (n = x) then $0 else $(S x).

  Lemma cycle_shift_shift n phi :
    bounded n phi -> phi[cycle_shift n] = phi[↑].
  Proof.
    intros H. apply (bounded_subst H). intros k. unfold cycle_shift. decide _; trivial; lia.
  Qed.

  Lemma cycle_shift_subject n phi :
    bounded (S n) phi -> phi[$n..][cycle_shift n] = phi.
  Proof.
    intros H. erewrite subst_comp, (bounded_subst H), subst_id; trivial.
    intros []; cbn; unfold cycle_shift; decide _; trivial; lia.
  Qed.

  Lemma nameless_equiv_all' A phi n :
    bounded_L n A -> bounded (S n) phi -> [p[↑] | p ∈ A] ⊢ phi <-> A ⊢ phi[$n..].
  Proof.
    intros H1 H2. split; intros H.
    - apply (subst_Weak ($n..)) in H. rewrite map_map in *.
      erewrite map_ext, map_id in H; try apply H. intros. apply subst_shift.
    - apply (subst_Weak (cycle_shift n)) in H. rewrite (map_ext_in _ (subst_form ↑)) in H.
      + now rewrite cycle_shift_subject in H.
      + intros psi HP. now apply cycle_shift_shift, H1.
  Qed.

  Lemma nameless_equiv_ex' A phi psi n :
    bounded_L n A -> bounded n phi -> bounded (S n) psi -> (psi::[p0[↑] | p0 ∈ A]) ⊢ phi[↑] <-> (psi[$n..]::A) ⊢ phi.
  Proof.
    intros HL Hphi Hpsi. split.
    - intros H % (subst_Weak ($n..)). cbn in *.
      rewrite map_map, (map_ext _ id), map_id in H.
      + now rewrite subst_shift in H.
      + intros. apply subst_shift.
    - intros H % (subst_Weak (cycle_shift n)). cbn in *.
      rewrite (map_ext_in _ (subst_form ↑)) in H.
      + now rewrite cycle_shift_subject, cycle_shift_shift in H.
      + intros theta HT. now apply cycle_shift_shift, HL.
  Qed.

  Lemma nameless_equiv_all A phi :
    { t : term | map (subst_form ↑) A ⊢ phi <-> A ⊢ phi[t..] }.
  Proof.
    destruct (find_bounded_L (phi::A)) as [n H].
    exists $n. apply nameless_equiv_all'.
    - intros ? ?. apply H. auto.
    - eapply bounded_up; try apply H; auto.
  Qed.

  Lemma nameless_equiv_ex A phi psi :
    { t : term | (phi :: map (subst_form ↑) A) ⊢ psi[↑] <-> (phi[t..]::A) ⊢ psi }.
  Proof.
    destruct (find_bounded_L (phi::psi::A)) as [n H].
    exists $n. apply nameless_equiv_ex'.
    - intros ? ?. apply H. auto.
    - apply H. auto.
    - eapply bounded_up; try apply H; auto.
  Qed.

  Lemma imps T phi psi :
    T ⊢ phi ~> psi <-> (phi :: T) ⊢ psi.
  Proof.
    split; try apply II.
    intros H. apply IE with phi; auto. apply (Weak H). auto.
  Qed.

  Lemma CE T phi psi :
    T ⊢ phi ∧ psi -> T ⊢ phi /\ T ⊢ psi.
  Proof.
    intros H. split.
    - apply (CE1 H).
    - apply (CE2 H).
  Qed.

  Lemma DE' A phi :
    A ⊢ phi ∨ phi -> A ⊢ phi.
  Proof.
    intros H. apply (DE H); auto.
  Qed.

  Lemma switch_conj_imp alpha beta phi A :
    A ⊢ alpha ∧ beta ~> phi <-> A ⊢ alpha ~> beta ~> phi.
  Proof.
    split; intros H.
    - apply II, II. eapply IE.
      apply (@Weak A). apply H. firstorder.
      apply CI; apply Ctx; firstorder.
    - apply II. eapply IE. eapply IE.
      eapply Weak. apply H.
      firstorder.
      eapply CE1, Ctx; firstorder.
      eapply CE2, Ctx; firstorder.
  Qed.

  Lemma impl_prv A B phi :
    (rev B ++ A) ⊢ phi <-> A ⊢ (B ==> phi).
  Proof.
    revert A; induction B; intros A; cbn; simpl_list; intros.
    - firstorder.
    - split; intros.
      + eapply II. now eapply IHB.
      + now apply imps, IHB in H.
  Qed.
    
End ND_def.


Hint Constructors prv : core.



(* ** Custom induction principle *)

Lemma prv_ind_full {Σ_funcs : funcs_signature} {Σ_preds : preds_signature} :
  forall P : peirce -> list (form falsity_on) -> (form falsity_on) -> Prop,
    (forall (p : peirce) (A : list form) (phi psi : form),
        (phi :: A) ⊢ psi -> P p (phi :: A) psi -> P p A (phi ~> psi)) ->
    (forall (p : peirce) (A : list form) (phi psi : form),
        A ⊢ phi ~> psi -> P p A (phi ~> psi) -> A ⊢ phi -> P p A phi -> P p A psi) ->
    (forall (p : peirce) (A : list form) (phi : form),
        (map (subst_form ↑) A) ⊢ phi -> P p (map (subst_form ↑) A) phi -> P p A (∀ phi)) ->
    (forall (p : peirce) (A : list form) (t : term) (phi : form),
        A ⊢ ∀ phi -> P p A (∀ phi) -> P p A phi[t..]) ->
    (forall (p : peirce) (A : list form) (t : term) (phi : form),
        A ⊢ phi[t..] -> P p A phi[t..] -> P p A (∃ phi)) ->
    (forall (p : peirce) (A : list form) (phi psi : form),
        A ⊢ ∃ phi ->
              P p A (∃ phi) ->
              (phi :: [p[↑] | p ∈ A]) ⊢ psi[↑] -> P p (phi :: [p[↑] | p ∈ A]) psi[↑] -> P p A psi) ->
    (forall (p : peirce) (A : list form) (phi : form), A ⊢ ⊥ -> P p A ⊥ -> P p A phi) ->
    (forall (p : peirce) (A : list form) (phi : form), phi el A -> P p A phi) ->
    (forall (p : peirce) (A : list form) (phi psi : form),
        A ⊢ phi -> P p A phi -> A ⊢ psi -> P p A psi -> P p A (phi ∧ psi)) ->
    (forall (p : peirce) (A : list form) (phi psi : form),
        A ⊢ phi ∧ psi -> P p A (phi ∧ psi) -> P p A phi) ->
    (forall (p : peirce) (A : list form) (phi psi : form),
        A ⊢ phi ∧ psi -> P p A (phi ∧ psi) -> P p A psi) ->
    (forall (p : peirce) (A : list form) (phi psi : form),
        A ⊢ phi -> P p A phi -> P p A (phi ∨ psi)) ->
    (forall (p : peirce) (A : list form) (phi psi : form),
        A ⊢ psi -> P p A psi -> P p A (phi ∨ psi)) ->
    (forall (p : peirce) (A : list form) (phi psi theta : form),
        A ⊢ phi ∨ psi ->
        P p A (phi ∨ psi) ->
        (phi :: A) ⊢ theta ->
        P p (phi :: A) theta -> (psi :: A) ⊢ theta -> P p (psi :: A) theta -> P p A theta) ->
    (forall (A : list form) (phi psi : form), P class A (((phi ~> psi) ~> phi) ~> phi)) ->
    forall (p : peirce) (l : list form) (f14 : form), l ⊢ f14 -> P p l f14.
Proof.
  intros. specialize (prv_ind (fun ff => match ff with falsity_on => P | _ => fun _ _ _ => True end)). intros H'.
  apply H' with (ff := falsity_on); clear H'. all: intros; try destruct ff; trivial. all: intuition eauto 2.
Qed.



(* ** Soundness *)

Section Soundness.

  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.

  Lemma soundness {ff : falsity_flag} A phi :
    A ⊢I phi -> valid_ctx A phi.
  Proof.
    remember intu as p.
    induction 1; intros D I rho HA; comp.
    - intros Hphi. apply IHprv; trivial. intros ? []; subst. assumption. now apply HA.
    - now apply IHprv1, IHprv2.
    - intros d. apply IHprv; trivial. intros psi [psi'[<- H' % HA]] % in_map_iff.
      eapply sat_comp. now comp.
    - eapply sat_comp, sat_ext. 2: apply (IHprv Heqp D I rho HA (eval rho t)). now intros [].
    - exists (eval rho t). cbn. specialize (IHprv Heqp D I rho HA).
      apply sat_comp in IHprv. eapply sat_ext; try apply IHprv. now intros [].
    - edestruct IHprv1 as [d HD]; eauto.
      assert (H' : forall psi, phi = psi \/ psi el map (subst_form ↑) A -> (d.:rho) ⊨ psi).
      + intros P [<-|[psi'[<- H' % HA]] % in_map_iff]; trivial. apply sat_comp. apply H'.
      + specialize (IHprv2 Heqp D I (d.:rho) H'). apply sat_comp in IHprv2. apply IHprv2.
    - apply (IHprv Heqp) in HA. firstorder.
    - firstorder.
    - firstorder.
    - firstorder. now apply H0.
    - firstorder. now apply H0.
    - firstorder.
    - firstorder.
    - edestruct IHprv1; eauto.
      + apply IHprv2; trivial. intros xi [<-|HX]; auto.
      + apply IHprv3; trivial. intros xi [<-|HX]; auto.
    - discriminate.
  Qed.

  Lemma soundness' {ff : falsity_flag} phi :
    [] ⊢I phi -> valid phi.
  Proof.
    intros H % soundness. firstorder.
  Qed.

  Corollary tsoundness {ff : falsity_flag} T phi :
    T ⊢TI phi -> forall D (I : interp D) rho, (forall psi, T psi -> rho ⊨ psi) -> rho ⊨ phi.
  Proof.
    intros (A & H1 & H2) D I rho HI. apply (soundness H2).
    intros psi HP. apply HI, H1, HP.
  Qed.
 
  Hypothesis LEM : forall P, P \/ ~ P.

  Lemma Peirce (P Q : Prop) :
    ((P -> Q) -> P) -> P.
  Proof.
    destruct (LEM (((P -> Q) -> P) -> P)); tauto.
  Qed.

  Lemma soundness_class {ff : falsity_flag} A phi :
    A ⊢C phi -> valid_ctx A phi.
  Proof.
    remember class as p.
    induction 1; intros D I rho HA; comp.
    - intros Hphi. apply IHprv; trivial. intros ? []; subst. assumption. now apply HA.
    - now apply IHprv1, IHprv2.
    - intros d. apply IHprv; trivial. intros psi [psi'[<- H' % HA]] % in_map_iff.
      eapply sat_comp. now comp.
    - eapply sat_comp, sat_ext. 2: apply (IHprv Heqp D I rho HA (eval rho t)). now intros [].
    - exists (eval rho t). cbn. specialize (IHprv Heqp D I rho HA).
      apply sat_comp in IHprv. eapply sat_ext; try apply IHprv. now intros [].
    - edestruct IHprv1 as [d HD]; eauto.
      assert (H' : forall psi, phi = psi \/ psi el map (subst_form ↑) A -> (d.:rho) ⊨ psi).
      + intros P [<-|[psi'[<- H' % HA]] % in_map_iff]; trivial. apply sat_comp. apply H'.
      + specialize (IHprv2 Heqp D I (d.:rho) H'). apply sat_comp in IHprv2. apply IHprv2.
    - apply (IHprv Heqp) in HA. firstorder.
    - firstorder.
    - clear LEM. firstorder.
    - firstorder. now apply H0.
    - firstorder. now apply H0.
    - clear LEM. firstorder.
    - clear LEM. firstorder.
    - edestruct IHprv1; eauto.
      + apply IHprv2; trivial. intros xi [<-|HX]; auto.
      + apply IHprv3; trivial. intros xi [<-|HX]; auto.
    - apply Peirce.
  Qed.

  Lemma soundness_class' {ff : falsity_flag} phi :
    [] ⊢C phi -> valid phi.
  Proof.
    intros H % soundness_class. clear LEM. firstorder.
  Qed.

  Corollary tsoundness_class {ff : falsity_flag} T phi :
    T ⊢TC phi -> forall D (I : interp D) rho, (forall psi, T psi -> rho ⊨ psi) -> rho ⊨ phi.
  Proof.
    intros (A & H1 & H2) D I rho HI. apply (soundness_class H2).
    intros psi HP. apply HI, H1, HP.
  Qed.

End Soundness.



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
  apply AllI; edestruct nameless_equiv_all as [x ->]; cbn; subsimpl.

Ltac use_exists H x :=
  apply (ExE _ H); edestruct nameless_equiv_ex as [x ->]; cbn; subsimpl.



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

  Definition list_binop (n : nat) := [Conj; Impl; Disj].

  Instance enum_binop :
    list_enumerator__T list_binop binop.
  Proof.
    intros []; exists 0; cbn; tauto.
  Qed.

  Definition list_quantop (n : nat) := [All; Ex].

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
    list_enumerator__T (L_term _ _) term :=
    enum_term _ _.

  Instance enum_form' {ff : falsity_flag} :
    list_enumerator__T (L_form _ _ _ _ _ _ _ _) form :=
    enum_form _ _ _ _ _ _ _ _.

  Fixpoint L_ded {p : peirce} {b : falsity_flag} (A : list form) (n : nat) : list form :=
    match n with
    | 0 => A
    | S n =>   L_ded A n ++
    (* II *)   concat ([ [ phi ~> psi | psi ∈ L_ded (phi :: A) n ] | phi ∈ L_T form n ]) ++
    (* IE *)   [ psi | (phi, psi) ∈ (L_ded A n × L_T form n) , (phi ~> psi el L_ded A n) ] ++
    (* AllI *) [ ∀ phi | phi ∈ L_ded (map (subst_form ↑) A) n ] ++
    (* AllE *) [ phi[t..] | (phi, t) ∈ (L_T form n × L_T term n), (∀ phi) el L_ded A n ] ++
    (* ExI *)  [ ∃ phi | (phi, t) ∈ (L_T form n × L_T term n), (phi[t..]) el L_ded A n ] ++
    (* ExE *)  [ psi | (phi, psi) ∈ (L_T form n × L_T form n),
                     (∃ phi) el L_ded A n /\ psi[↑] el L_ded (phi::(map (subst_form ↑) A)) n ] ++
    (* Exp *)  (match b with falsity_on => fun A =>
                [ phi | phi ∈ L_T form n, ⊥ el @L_ded _ falsity_on A n ]
                | _ => fun _ => nil end A) ++
    (* Pc *)   (if p then
                [ (((phi ~> psi) ~> phi) ~> phi) | (pair phi psi) ∈ (L_T form n × L_T form n)]
                else nil) ++
    (* CI *)   [ phi ∧ psi | (phi, psi) ∈ (L_ded A n × L_ded A n) ] ++
    (* CE1 *)  [ phi | (phi, psi) ∈ (L_T form n × L_T form n), phi ∧ psi el L_ded A n] ++
    (* CE2 *)  [ psi | (phi, psi) ∈ (L_T form n × L_T form n), phi ∧ psi el L_ded A n] ++
    (* DI1 *)  [ phi ∨ psi | (phi, psi) ∈ (L_T form n × L_T form n), phi el L_ded A n] ++
    (* DI2 *)  [ phi ∨ psi | (phi, psi) ∈ (L_T form n × L_T form n), psi el L_ded A n] ++
    (* DE *)   [ theta | (phi, (psi, theta)) ∈ (L_T form n × (L_T form n × L_T form n)),
                     theta el L_ded (phi::A) n /\ theta el L_ded (psi::A) n /\ phi ∨ psi el L_ded A n]
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
      + destruct IHprv as [m1], (el_T t) as [m2], (el_T phi) as [m3]. exists (1 + m1 + m2 + m3).
        cbn. in_app 6. in_collect (phi, t)...
      + destruct IHprv1 as [m1], IHprv2 as [m2], (el_T phi) as [m4], (el_T psi) as [m5].
        exists (1 + m1 + m2 + m4 + m5). cbn. in_app 7. cbn. in_collect (phi, psi)...
      + destruct IHprv as [m1], (el_T phi) as [m2]. exists (1 + m1 + m2). cbn. in_app 8. in_collect phi...
      + now exists 0.
      + destruct IHprv1 as [m1], IHprv2 as [m2]. exists (1 + m1 + m2). cbn. in_app 10. in_collect (phi, psi)...
      + destruct IHprv as [m1], (el_T phi) as [m2], (el_T psi) as [m3].
        exists (1 + m1 + m2 + m3). cbn. in_app 11. in_collect (phi, psi)...
      + destruct IHprv as [m1], (el_T phi) as [m2], (el_T psi) as [m3].
        exists (1 + m1 + m2 + m3). cbn. in_app 12. in_collect (phi, psi)...
      + destruct IHprv as [m1], (el_T phi) as [m2], (el_T psi) as [m3].
        exists (1 + m1 + m2 + m3). cbn. in_app 13. in_collect (phi, psi)...
      + destruct IHprv as [m1], (el_T phi) as [m2], (el_T psi) as [m3].
        exists (1 + m1 + m2 + m3). cbn. in_app 14. in_collect (phi, psi)...
      + destruct IHprv1 as [m1], IHprv2 as [m2], IHprv3 as [m3], (el_T phi) as [m4], (el_T psi) as [m5], (el_T theta) as [m6].
        exists (1 + m1 + m2 + m3 + m4 + m5 + m6). cbn. in_app 15. cbn. in_collect (phi, (psi, theta))...
      + destruct (el_T phi) as [m1], (el_T psi) as [m2]. exists (1 + m1 + m2). cbn. in_app 9. in_collect (phi, psi)...
    - intros [m]; induction m in A, x, H |-*; cbn in *.
      + now apply Ctx.
      + destruct p, b; inv_collect. all: eauto 3.
        * eapply IE; apply IHm; eauto.
        * eapply ExE; apply IHm; eauto.
        * eapply DE; apply IHm; eauto.
        * eapply IE; apply IHm; eauto.
        * eapply ExE; apply IHm; eauto.
        * eapply DE; apply IHm; eauto.
        * eapply IE; apply IHm; eauto.
        * eapply ExE; apply IHm; eauto.
        * eapply DE; apply IHm; eauto.
        * eapply IE; apply IHm; eauto.
        * eapply ExE; apply IHm; eauto.
        * eapply DE; apply IHm; eauto.
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
      + inv_collect. apply IHm in H2. apply (enum_p _ _ He) in H0. unfold containsL in *. firstorder congruence.
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
      + eapply (enum_p _ _ (enum_containsL (to_cumul_cumulative L) HL)); eauto.
      + eapply (enum_p _ _ (enum_prv x1)); eassumption.
  Qed.

End Enumerability.


