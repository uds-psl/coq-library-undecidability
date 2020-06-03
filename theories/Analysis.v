From Undecidability.FOLC Require Import WKL Markov GenTarski GenCompleteness Stability.

(** ** Theorems 15 and 42  *)

(* Theorem 15 *)

Lemma completeness_context_iff_MPL : 
  completeness (fun Sigma T => exists A, forall phi : form, phi ∈ T <-> phi el A) (@SM) <-> MPL.
Proof.
  split.
  - intros H P.
    eapply halt_cprv_stable.
    intros (Sigma & [[[d d0] [e e0]] (Gamma & phi & HGamma & Hphi)]).
    epose proof (H Sigma d d0 e e0 (fun x => In x Gamma) _ (ltac:(exists Gamma; reflexivity)) phi _) as Hcomp.
    eapply completeness_standard_stability in Hcomp.
    + intros ?. destruct Hcomp.
      * intros ?. eapply H0. intros H2. eapply H1. exists Gamma. firstorder.
      * eapply Weak. eapply H1. eapply H1.
    + rewrite List.Forall_forall in HGamma. intros ? ? ?. eapply HGamma. eassumption.
    + eassumption.
  - intros dne Sigma HdF HdP HeF HeP T clT (A & HA) phi clphi.
    eapply completeness_standard_stability; eauto.
    enough (stable (A ⊢CE phi)).
    + intros ?. exists A. split.
      * intros ? ?. now eapply HA.
      * eapply H. intros ?. eapply H0. intros [B HB].
        eapply H1. eapply Weak. eapply HB. intros ? ? % HB. now eapply HA.
    + intros H. unshelve epose proof (cprv_iprv_stable _ _).
      2:{ exists Sigma. repeat split. 1-4: eauto.
          exists A, phi. split. 2:eauto.
          eapply List.Forall_forall.  intros ? ? ?. now eapply clT, HA. }
      2:{ cbn. exact H. }
      2:{ cbn in *. eassumption. }
      eapply iprv_halt_stable; eauto.
      Unshelve.
      *  rewrite List.Forall_forall in HGamma.
         intros ? ? ?. now eapply HGamma.
      * eassumption.
Qed.

Lemma completeness_enum_iff_MP : 
  completeness (fun Sigma T => enumerable T) (@SM) <-> MP.
Proof.
  split.
  - intros H P.
    eapply ste_to_mp. red. red. intros Sigma T phi clT clphi (? & ? & ? & ? & ? & ?).
    eapply completeness_standard_stability; eauto.
    intros. eapply H; eauto.
    eapply enum_count; eauto.
  - intros dne Sigma HdF HdP HeF HeP T clT He phi clphi.
    eapply completeness_standard_stability; eauto.
    eapply mp_to_ste; eauto.
    exists HdF, HdP, HeF, HeP. eapply enumerable_enum; eauto.
Qed.

Lemma completeness_iff_XM :
  completeness (fun _ _ => True) (@SM) <-> XM.
Proof.
  assert (XM <-> DN) as ->. {
    split.
    - intros xm P H. destruct (xm P); tauto.
    - intros dne P. eapply dne. tauto.
  }
  split.
  - intros H P.
    eapply sta_to_dn. red. red. intros Sigma T phi clT clphi (HdF & HdP & HeF & HeP & _).
    eapply completeness_standard_stability; eauto.
  - intros dne Sigma HdF HdP HeF HeP T clT _ phi clphi.
    eapply completeness_standard_stability; eauto.
Qed.

(* Theorem 42

  (1a)    (1b)
   ^       ^
   |       |
   v       v
  (2a) -> (2b)
   |       |
   v       v
  (3a)    (3b)
    \      /
     \    /
      \  /
       vv
       (4)
        |
        v
       (5)
        |
        v
       (2a)

*)

Lemma completeness_transport (CT : forall Sigma, @theory Sigma -> Prop) (C1 C2 : forall Sigma D, @interp Sigma D -> Prop) :
  (forall Sigma D I, C2 Sigma D I -> C1 Sigma D I) ->
  completeness CT C2 -> completeness CT C1.
Proof.
  intros HImpl Hcomp Sigma HdF HdP HeF HeP T T_closed TC phi clphi HH.
  eapply Hcomp; eauto.
  intros ? ? ? ? ?; eauto.
Qed.

Lemma modex_comp  (C : forall Sigma D, @interp Sigma D -> Prop) :
  (forall Sigma D I, C Sigma D I -> SM I) ->
  XM -> model_existence (fun _ _ => True) C -> completeness (fun _ _ => True) C.
Proof.
  intros Himpl xm modex Sigma Hdf HdP HeF HeP T T_closed TC phi phi_closed H.
  assert (dne : forall P, ~~ P -> P). { red in xm. intros. specialize (xm P). tauto. }
  eapply dne. intros Hcons. rewrite refutation_prv in Hcons. 
  assert (Hcl : closed_T (T ⋄ (¬ phi))) by (intros ? ? [] ; subst; try econstructor; eauto; econstructor).
  eapply modex in Hcl as (D & I & rho & H1 & H2); eauto.
  eapply Himpl; eauto.
  eapply (H1 (¬ phi)). now right.
  fold sat. eapply H; firstorder.
Qed.

Lemma iff_1a_2a :
  completeness (fun _ _ => True) (@OM) <->
  XM /\ model_existence (fun _ _ => True) (@OM).
Proof.
  split.
  - intros ?. 
    assert (xm : XM). {
      eapply completeness_iff_XM.
      eapply completeness_transport.
      2:eauto. intros ? ? ? ?.
      econstructor. eapply omniscient_to_classical. eapply H0. eapply H0.
    }
    split.
    + eauto.
    + eapply comp_modex; eauto.
  - intros [xm modex].
    eapply modex_comp; firstorder.
Qed.

Lemma iff_1b_2b :
  completeness (fun _ _ => True) (@DM) <->
  XM /\ model_existence (fun _ _ => True) (@DM).
Proof.
  split.
  - intros ?. 
    assert (xm : XM). {
      eapply completeness_iff_XM.
      eapply completeness_transport.
      2:eauto. intros ? ? ? ?.
      eapply H0.
    }
    split.
    + eauto.
    + eapply comp_modex; eauto.
  - intros [xm modex].
    eapply modex_comp; firstorder.
Qed.

Lemma impl_2a_2b :
  model_existence (fun _ _ => True) (@OM) -> model_existence (fun _ _ => True) (@DM).
Proof.
  eapply modex_impl_OM_DM.
Qed.

Lemma impl_2a_3a :
  model_existence (fun _ _ => True) (@OM) -> compactness (fun _ _ => True) (@OM).
Proof.
  eapply modex_compact; firstorder.
Qed.

Lemma impl_2b_3b :
  model_existence (fun _ _ => True) (@DM) -> compactness (fun _ _ => True) (@DM).
Proof.
  eapply modex_compact; firstorder.
Qed.

Lemma impl_3a_4 :
  XM -> compactness (fun _ _ => True) (@OM) -> WKL (fun _ => True).
Proof.
  eapply compact_OM_implies_WKL.
Qed.

Lemma impl_3b_4 :
  XM -> compactness (fun _ _ => True) (@DM) -> WKL (fun _ => True).
Proof.
  eapply compact_implies_WKL.
Qed.

Lemma impl_4_5 :
  XM -> WKL (fun _ => True) -> (forall X, forall p : X -> Prop, discrete X -> enumerable__T X -> decidable p).
Proof.
  intros. eapply CO_iff_EM_WKL; eauto.
Qed.

Lemma impl_5_2a :
  XM -> (forall X, forall p : X -> Prop, discrete X -> enumerable__T X -> decidable p) -> model_existence (fun _ _ => True) (@OM).
Proof.
  intros. eapply PCO_implies_modex; eauto.
  intros. eapply H0. eapply discrete_iff. econstructor. eauto.
  eapply enum_enumT. econstructor. eauto.
Qed.

(* Theorem 56 *)

Require Import Undecidability.FOLC.KripkeCompleteness.

Definition kcompleteness (CT : forall Sigma, @theory Sigma -> Prop) (C : forall Sigma D, @kmodel Sigma D -> Prop) :=
  forall {Sigma : Signature},
  forall {HdF : eq_dec Funcs} {HdP : eq_dec Preds},
  forall {HeF : enumT Funcs} {HeP : enumT Preds},
  forall T (T_closed : closed_T T), CT _ T ->
                               forall phi, closed phi -> kvalid_T (C Sigma) T phi ->
                               T ⊩IE phi.

Lemma nd_to_sequent {Sigma : Signature} T phi :
  eq_dec Funcs -> eq_dec Preds ->
  T ⊩IE phi -> T ⊩SE phi.
Proof.
  intros eF eP (A & HA & Hprv).
  exists A. split; eauto. eapply Extend.sprv_prv_iff; eauto.
Qed.

Lemma kcompleteness_iff_MPL : 
  kcompleteness (fun Sigma T => exists A, forall phi : form, phi ∈ T <-> phi el A) (@kstandard) <-> MPL.
Proof.
  split.
  - intros H P.
    eapply halt_cprv_stable.
    intros (Sigma & [[[d d0] [e e0]] (Gamma & phi & HGamma & Hphi)]). cbn.
    unshelve epose proof (cend_dn (C := fun Sigma T => exists A, forall phi : form, phi ∈ T <-> phi el A) _ _).
    + intros ? (A & HA). exists (map dnt A).
      intros. unfold tmap. rewrite in_map_iff. unfold contains.
      setoid_rewrite HA. clear. split; intros (? & ? & ?); subst; eauto.
    + intros. eapply nd_to_sequent; eauto. 
    + cbn in *.
      intros H1.
      destruct (H0 (fun phi => In phi Gamma) phi).
      * intros ? ? ?. rewrite Forall_forall in HGamma. eapply HGamma; eauto.
      * eauto.
      * exists Gamma. reflexivity.
      * intros ?. eapply H1. intros H3. eapply H2. exists Gamma. firstorder.
      * eapply Weak, H2. eapply H2.
  - intros mpl Sigma HdF HdP HeF HeP T clT [A HA] phi clphi Hvalid.
    exists A. split. firstorder.
    unshelve epose proof (iprv_halt_stable mpl _).
    + exists Sigma. split.
      * split; econstructor; eauto.
      * exists A, phi. split; eauto.
        eapply List.Forall_forall.  intros ? ? ?. now eapply clT, HA.
    + cbn. rewrite Extend.sprv_prv_iff.
      eapply K_std_completeness. intros ? ? ? ? ? ?.
      eapply Hvalid; firstorder.
    + cbn in *. eassumption.
Qed.

Lemma kcompleteness_enum_implies_MP :
  kcompleteness (fun Sigma T => enumerable T) (@kstandard) -> MP.
Proof.
  intros H P.
  eapply ste_to_mp. red. red. intros Sigma T phi clT clphi (? & ? & ? & ? & ? & ?).
  unfold stable. eapply (cend_dn (C := (fun Sigma T => enumerable T))); eauto.
  - clear. intros T' [f Hf].
    exists (fun n => match f n with Some phi => Some (dnt phi) | _ => None end).
    intros phi.
    split.
    + intros (? & ? & <-). eapply Hf in H as [n Hn].
      exists n. rewrite Hn. reflexivity.
    + intros [n Hn]. destruct (f n) as [psi |] eqn:E; inv Hn.
      exists psi. split; eauto. eapply Hf. eauto.
  - intros. eapply nd_to_sequent; eauto.
  - now eapply enum_count.
Qed.

Lemma kcompleteness_implies_XM :
  kcompleteness (fun Sigma T => True) (@kstandard) -> XM.
Proof.
  assert (XM <-> DN) as ->. {
    split.
    - intros xm P H. destruct (xm P); tauto.
    - intros dne P. eapply dne. tauto.
  }
  intros H P. eapply sta_to_dn. red. red. intros Sigma T phi clT clphi (HdF & HdP & HeF & HeP & _).
  unfold stable. eapply (cend_dn (C := fun _ _ => True)); eauto.
  econstructor.
  intros. eapply nd_to_sequent; eauto.
Qed.
