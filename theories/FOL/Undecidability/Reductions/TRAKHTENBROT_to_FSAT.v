From Undecidability.FOL Require Import Syntax.Facts Semantics.Tarski.FullFacts Syntax.BinSig Semantics.FiniteTarski.Full.
From Undecidability.TRAKHTENBROT Require bpcp. (* keep this Require to avoid universe problems *)
From Undecidability.TRAKHTENBROT Require Import fo_sat fo_sig fo_terms fo_logic fol_ops.
Require Import Undecidability.Synthetic.DecidabilityFacts.
Require Import Vector Lia.

Set Default Goal Selector "!".
Set Default Proof Using "Type".

(* Reduction from the TRAKHTENBROT development to the FSAT problems in FOL *)

(** syntax translation **)

Definition term' := @fo_term Empty_set (fun f => match f with end).
Definition form' := fol_form (Σrel 2).

Definition translate_term (t : term') : term :=
  match t with
  | in_var n => $n
  | _ => $0
  end.

Fixpoint translate (phi : form') : form :=
  match phi with
  | @fol_false _  => ⊥
  | fol_atom tt v => atom tt (map translate_term v)
  | fol_bin fol_conj phi psi => translate phi ∧ translate psi
  | fol_bin fol_disj phi psi => translate phi ∨ translate psi
  | fol_bin fol_imp phi psi => translate phi → translate psi
  | fol_quant fol_ex phi => ∃ translate phi
  | fol_quant fol_fa phi => ∀ translate phi
  end.

(** verification **)

Section Forward.
  
  Variable D : Type.
  Variable M : fo_model (Σrel 2) D.

  Instance M1 :
    interp D.
  Proof using M.
    split.
    - intros [].
    - intros [] v. exact (fom_rels M tt v).
  Defined.

  Lemma fwd_eval rho t :
    fo_term_sem M rho t = eval rho (translate_term t).
  Proof.
    destruct t as [n|[]]; cbn. reflexivity.
  Qed.

  Lemma fwd_sat rho phi :
    fol_sem M rho phi <-> rho ⊨ translate phi.
  Proof.
    induction phi in rho |- *; try destruct p; try destruct f; cbn; try now intuition; try firstorder.
    - unfold sat. rewrite map_map. erewrite map_ext. 
      1:{ match goal with [ |- ?P <-> ?Q ] => enough (P = Q) as ->  end. 1: reflexivity. reflexivity. } 
      eapply fwd_eval.
    - split; intros [d H]; exists d; apply IHphi.
      + eapply fol_sem_ext; try apply H. now intros [].
      + eapply sat_ext; try apply H. now intros [].
    - split; intros H d; apply IHphi.
      + eapply fol_sem_ext; try apply H. now intros [].
      + eapply sat_ext; try apply H. now intros [].
  Qed.

End Forward.

Section Backward.

  Variable D : Type.
  Variable M : interp D.

  Definition M2 :
    fo_model (Σrel 2) D.
  Proof using M.
    split.
    - intros [].
    - intros [] v. exact (i_atom (P:=tt) v).
  Defined.

  Lemma bwd_eval rho t :
    fo_term_sem M2 rho t = eval rho (translate_term t).
  Proof.
    destruct t as [n|[]]; cbn. reflexivity.
  Qed.

  Lemma bwd_sat rho phi :
    fol_sem M2 rho phi <-> rho ⊨ translate phi.
  Proof.
    induction phi in rho |- *; try destruct p; try destruct f; cbn; try now intuition; try firstorder.
    - unfold sat. rewrite map_map. erewrite map_ext.
      1:{ match goal with [ |- ?P <-> ?Q ] => enough (P = Q) as ->  end. 1: reflexivity. reflexivity. }
      eapply bwd_eval.
    - split; intros [d H]; exists d; apply IHphi.
      + eapply fol_sem_ext; try apply H. now intros [].
      + eapply sat_ext; try apply H. now intros [].
    - split; intros H d; apply IHphi.
      + eapply fol_sem_ext; try apply H. now intros [].
      + eapply sat_ext; try apply H. now intros [].
  Qed.

End Backward.

(** reduction theorems **)

Lemma reduction :
  @fo_form_fin_dec_SAT (Σrel 2) ⪯ Full.FSAT.
Proof.
  exists translate. intros phi. split.
  - intros (D & M & [L HL] & HD & rho & H). exists D, (@M1 D M), rho. repeat split.
    + exists L. apply HL.
    + intros [ ]. apply decidable_iff. constructor. apply HD.
    + now apply fwd_sat.
  - intros (D & M & rho & [L HL] & HD & H). specialize (HD tt). apply decidable_iff in HD. destruct HD as [HD]. exists D, (@M2 D M), (exist _ L HL). eexists.
    + intros []. apply HD.
    + exists rho. now apply bwd_sat.
Qed.

Lemma reduction_disc :
  @fo_form_fin_discr_dec_SAT (Σrel 2) ⪯ FSATd.
Proof.
  exists translate. intros phi. split.
  - intros (D & HE & M & [L HL] & HD & rho & H). exists D, (@M1 D M), rho. repeat split.
    + exists L. apply HL.
    + apply discrete_iff. constructor. apply HE.
    + intros [ ]. apply decidable_iff. constructor. apply HD.
    + now apply fwd_sat.
  - intros (D & M & rho & [L HL] & [HE] % discrete_iff & HD & H).
    specialize (HD tt).
    apply decidable_iff in HD. destruct HD as [HD].
    exists D, HE, (@M2 D M), (exist _ L HL). eexists.
    + intros []. apply HD.
    + exists rho. now apply bwd_sat.
Qed.


  



