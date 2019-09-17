(** ** Connections to MPL  *)

From Undecidability.FOLC Require Import Extend BPCP_CND LEnum.
From Undecidability.L Require Import Synthetic Lists LOptions.

From Undecidability.Reductions Require Import L_to_mTM mTM_to_TM TM_to_SRH SRH_to_SR SR_to_MPCP MPCP_to_PCP PCP_to_BPCP.

Definition enumerable_sig (Sigma : Signature) := (enumT Funcs * enumT Preds) % type.
Definition discrete_sig (Sigma : Signature) := ((eq_dec Funcs) * (eq_dec Preds)) % type.

Definition cprv (a : {Sigma & (discrete_sig Sigma * enumerable_sig Sigma * list form * form)%type }) := match a with (existT _ Sigma (H1, H2, Gamma, phi)) => @prv Sigma class expl Gamma phi end.

Lemma halt_cprv :
  L.converges ⪯ cprv.
Proof.
  eapply reduces_transitive with (q := cbvLambda.HaltL).
  exists (fun s => s). firstorder. subst. unfold cbvLambda.HaltL.
  exists (L.lam x1). rewrite H. econstructor. reflexivity. econstructor. reflexivity.
  eapply reduces_transitive.
  eapply HaltL_HaltTM.
  eapply reduces_transitive.
  eapply  nTM_to_MTM.
  eapply reduces_transitive.
  eapply MTM_to_stM.
  eapply reduces_transitive.
  eapply Undecidability.PCP.singleTM.TM_conv.
  eapply reduces_transitive.
  eapply Undecidability.PCP.TM_SRH.Halt_SRH.
  eapply reduces_transitive.
  eapply Undecidability.PCP.SRH_SR.reduction.
  eapply reduces_transitive.
  eapply Undecidability.PCP.SR_MPCP.reduction.
  eapply reduces_transitive.
  eapply Undecidability.PCP.MPCP_PCP.reduction.
  eapply reduces_transitive.
  eapply Undecidability.ILL.PCP_BPCP.PCP_BPCP.
  eapply reduces_transitive.
  eapply cprv_red.
  unshelve eexists (fun phi => (existT _ min_sig (_, _, [], phi))). 3: reflexivity.
  econstructor; intros ? ?; hnf; repeat decide equality.
  econstructor; cbn.
  - exists (fun n => [t_f' true; t_f' false; t_e']). eauto.
    intros. exists 0. destruct x; try destruct b; eauto.
  - exists (fun n => [BPCP_FOL.P; Q]). eauto.
    intros. exists 0. destruct x; eauto.  
Qed.

Definition iprv (a : {Sigma & (discrete_sig Sigma * enumerable_sig Sigma * list form * form)%type }) := match a with (existT _ Sigma (H1, H2, Gamma, phi)) => @prv Sigma intu expl Gamma phi end.

Lemma cprv_iprv :
  cprv ⪯ iprv.
Proof.
  unshelve eexists.
  - intros (Sigma & [[H Gamma] phi]).
    exists Sigma. exact (H, List.map dnt Gamma, dnt phi).
  - intros (Sigma & [[[H1 H2] Gamma] phi]). cbn.
    split.
    eapply dnt_to_IE.
    eapply dnt_to_CE.
Qed.

Require Import ConstructiveEpsilon.

Section enum_inj.

  Variable (X : Type) (XD : eq_dec X) (H : enumT X).

  Definition ofNat n :=
    match R_nat_nat n with Some (n, m) => nthe n (L_T m) | None => None end.

  Lemma ofNat_correct x :
    exists n, ofNat n = Some x.
  Proof.
    destruct (el_T x) as [n Hn].
    eapply In_nth_error in Hn as [m].
    destruct (pairs_retract (m, n)) as [k].
    exists k. unfold ofNat. now rewrite H1.
  Qed.

  Definition mu (p : nat -> Prop) :
    (forall x, dec (p x)) -> ex p -> sig p.
  Proof.
    apply constructive_indefinite_ground_description_nat_Acc.
  Defined.

  Definition natinj x :=
    proj1_sig (mu _ (ofNat_correct x)).

  Lemma natinj_inj x y :
    natinj x = natinj y -> x = y.
  Proof.
    unfold natinj.
    destruct mu as [k Hk], mu as [l Hl].
    cbn. congruence.
  Qed.

  Lemma ofnat_natinj x :
    ofNat (natinj x) = Some x.
  Proof.
    unfold natinj. apply proj2_sig.
  Qed.


End enum_inj.



Section inj_enum.

  Variable Sigma : Signature.
  Variable e : enumerable_sig Sigma.
  Variable d : discrete_sig Sigma.
  
  Definition inj : Signature_inj Sigma max.
  Proof.
    destruct e as [e1 e2], d as [d1 d2]. unshelve econstructor; cbn.
    - exact (fun f => (natinj d1 e1 f, fun_ar f)).
    - exact (fun p => ofNat e1 (fst p)).
    - exact (fun P => (natinj d2 e2 P, pred_ar P)).
    - exact (fun p => ofNat e2 (fst p)).
    - apply ofnat_natinj.
    - reflexivity.
    - apply ofnat_natinj.
    - reflexivity.
  Qed.
  
End inj_enum.

Definition isprv (a : {Sigma & (discrete_sig Sigma * enumerable_sig Sigma * list form * form)%type }) := match a with (existT _ Sigma (H1, H2, Gamma, phi)) => @sprv Sigma expl Gamma None phi end.

Lemma iprv_maxprv :
  iprv ⪯ (fun '(A, phi) => @prv max intu expl A phi).
Proof.
  unshelve eexists.
  - intros (Sigma & [[[] A] phi]).
    exact (map (embed (inj e d)) A, embed (inj e d) phi).
  - intros (Sigma & [[[] A] phi]). cbn.
    split; intros.
    + now eapply prv_embed.
    + now eapply prv_back in H.
Qed.

Lemma maxprv_sprv :
  (fun '(A, phi) => @prv max intu expl A phi) ⪯ (fun '(A,psi,phi) => @sprv max expl A psi phi).
Proof.
  unshelve eexists.
  - intros [A phi]. exact (A, None, phi).
  - intros [A phi]. eapply sprv_prv_iff.
Qed.    
    
Lemma sprv_sprvie :
  (fun '(A,psi,phi) => @sprv max expl A psi phi) ⪯ (fun '(A, psi, phi) => sprvie A psi phi).
Proof.
  unshelve eexists (fun '(A,psi,phi) => (List.map of_form A, option_map of_form psi, of_form phi)).
  intros [[A psi] phi].
  split.
  - intros. now eapply prv_prvie.
  - intros. now eapply prvie_prv.
Qed.

Lemma iprv_halt :
  iprv ⪯ L.converges.
Proof.
  eapply reduces_transitive. eapply iprv_maxprv.
  eapply reduces_transitive. eapply maxprv_sprv.
  eapply reduces_transitive. eapply sprv_sprvie.
  eapply L_enumerable_halt.
  - exists enum_eqb. split. econstructor. exact _.
    intros [[[A psi] phi] [[A' psi'] phi']]. cbn.
    unfold list_form_eqb, option_form_eqb.
    destruct (list_eqb_spec form_eqb_spec A A'), (option_eqb_spec form_eqb_spec psi psi'), (form_eqb_spec phi phi'); subst.
    all: split; intros; cbn in *; try firstorder congruence.
  - eapply L_enumerable_enum.
    exists L_sprvie. split. econstructor. exact _.
    eapply enum_sprvie.
Qed.
