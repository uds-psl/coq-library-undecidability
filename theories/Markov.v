(** ** Connections to MPL  *)

From Undecidability.FOL Require Import MarkovPost.
From Undecidability.L Require Import Synthetic Lists LOptions Seval.

From Undecidability Require Import SR.SR_undec PCP.PCP_undec.
From Undecidability.Reductions Require Import L_to_mTM mTM_to_TM.
From Undecidability Require Import Reductions.PCPb_iff_BPCP.

Definition MPL := forall s, stable (L.converges s).

Instance enumT_term : enumT term.
Proof.
  exists (fix f n := match n with
               | 0 => []
               | S n => f n ++ [ var m | m ∈ L_T n]
                         ++ [ lam s | s ∈ f n ]
                         ++ [ app s t | (s,t) ∈ (f n × f n) ]
               end).
  - eauto.
  - intros. induction x.
    + destruct (el_T n) as [m]. exists (S m). cbn. in_app 2.
      in_collect n. eapply cum_ge'; eauto; omega.
    + destruct (IHx1) as [m1]. destruct (IHx2) as [m2].
      exists (1 + m1 + m2). cbn. in_app 4.
      in_collect (x1, x2). eapply cum_ge'; eauto; omega.
      eapply cum_ge'; eauto; omega.
    + destruct (IHx) as [m1]. 
      exists (1 + m1). cbn. in_app 3.
      in_collect x. eapply cum_ge'; eauto; omega.
Qed.

Instance eq_dec_term : eq_dec L.term.
Proof.
  intros ? ?. hnf. repeat decide equality.  
Qed.

Instance help : forall n s, Prelim.dec (eva n s <> None).
Proof.
  intros. eapply not_dec. eapply option_eq_dec. exact _.
Qed.

Fixpoint f n :=
  match n with
  | 0 => []
  | S n => f n ++ [ s | (s, m) ∈ (@L_T _ enumT_term n × @L_T _ enumT_nat n), eva m s <> None ]
  end.

Lemma converges_eva s : L.converges s <-> exists n, eva n s <> None.
Proof.
  split.
  - intros [t [n H % seval_eva] % eval_seval] % Eval.eval_converges. exists n. congruence.
  - intros [n H]. destruct (eva n s) eqn:Ht; try congruence.
    eapply eval_converges. eapply seval_eval. eapply eva_seval. eauto.
Qed.

Lemma enum_halt : enumerable L.converges.
Proof.
  eapply enum_count with f. econstructor.
  - eauto.
  - intros s. split.
    + intros [n H] % converges_eva.
      destruct (el_T n) as [m1], (el_T s) as [m2]. exists (1 + m1 + m2).
      cbn. in_app 2. in_collect (s, n).
      eapply cum_ge'; eauto; omega.
      eapply cum_ge'; eauto; omega.
    + intros [m H]. induction m.
      * inv H.
      * cbn in *. inv_collect.
        eapply converges_eva. eauto.        
Qed.        
      
Lemma MP_MPL :
  MP -> MPL.
Proof.
  intros. unfold MPL. intros. eapply MP_enum_stable.
  - eassumption.
  - eapply enum_halt.
  - unfold discrete. eapply decidable_iff. econstructor.
    intros []. hnf. repeat decide equality.
Qed.

Definition IP := forall (X : Prop) (P : nat -> Prop), (X -> exists n, P n) -> exists n, X -> P n.

Definition halting_dec := forall s, (L.converges s) \/ ~ (L.converges s).

Lemma MPL_independent : IP -> MPL -> halting_dec. 
Proof.
  intros H1 H2 s.
  assert (exists n, forall k, eva k s <> None -> eva n s <> None) as [n Hn].
  - specialize (H2 s). unfold stable in H2. rewrite converges_eva in H2. apply H1 in H2 as [n Hn].
    exists n. intros k H. apply Hn. intros H'. apply H'. now exists k.
  - destruct (eva n s) eqn : H.
    + left. eapply converges_eva. exists n. congruence.
    + right. intros [k Hk % Hn] % converges_eva. congruence.
Qed.

From Undecidability.FOLC Require Import Extend BPCP_CND LEnum.

Definition enumerable_sig (Sigma : Signature) := (enumT Funcs * enumT Preds) % type.
Definition discrete_sig (Sigma : Signature) := ((eq_dec Funcs) * (eq_dec Preds)) % type.

Definition cprv (a : {Sigma & (discrete_sig Sigma * enumerable_sig Sigma * list form * form)%type }) := match a with (existT Sigma (H1, H2, Gamma, phi)) => @prv Sigma class expl Gamma phi end.

Lemma halt_cprv :
  L.converges ⪯ cprv.
Proof.
  eapply reduces_transitive with (Q := cbvLambda.HaltL).
  exists (fun s => s). firstorder. subst. unfold cbvLambda.HaltL.
  exists (L.lam x1). rewrite H. econstructor. reflexivity. econstructor. reflexivity.
  eapply reduces_transitive.
  eapply HaltL_HaltTM.
  eapply reduces_transitive.
  eapply  nTM_to_MTM.
  eapply reduces_transitive.
  eapply MTM_to_stM.
  eapply reduces_transitive.
  eapply Undecidability.PCP.PCP_undec.dPCPb_undec.
  eapply reduces_transitive.
  eapply PCPb_iff_dPCPb.reductionRL.
  eapply reduces_transitive.
  eapply reductionLR.
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

Fact stable_red X Y (p : X -> Prop) (q : Y -> Prop) :
  p ⪯ q -> (forall y, stable (q y)) -> (forall x, stable (p x)).
Proof.
  intros [f H] H' x. unfold stable.
  repeat rewrite H. apply H'.
Qed.

Corollary halt_cprv_stable :
  (forall x, stable (cprv x)) -> MPL.
Proof.
  unfold MPL. apply stable_red.
  eapply halt_cprv.
Qed.

Definition iprv (a : {Sigma & (discrete_sig Sigma * enumerable_sig Sigma * list form * form)%type }) := match a with (existT Sigma (H1, H2, Gamma, phi)) => @prv Sigma intu expl Gamma phi end.

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

Corollary cprv_iprv_stable :
  (forall x, stable (iprv x)) -> (forall x, stable (cprv x)).
Proof.
  apply stable_red. eapply cprv_iprv.
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

Definition isprv (a : {Sigma & (discrete_sig Sigma * enumerable_sig Sigma * list form * form)%type }) := match a with (existT Sigma (H1, H2, Gamma, phi)) => @sprv Sigma expl Gamma None phi end.

Lemma iprv_maxprv :
  iprv ⪯ (fun '(A, phi) => @prv max intu expl A phi).
Proof.
  unshelve eexists.
  - intros (Sigma & [[[] A] phi]).
    exact (List.map (embed (inj e d)) A, embed (inj e d) phi).
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

Corollary iprv_halt_stable :
  MPL -> (forall x, stable (iprv x)).
Proof.
  unfold MPL. apply stable_red.
  eapply iprv_halt.
Qed.
