(* * Tarski Semantics *)

Require Import Undecidability.FOL.Syntax.Facts.
Require Export Undecidability.FOL.Semantics.Tarski.FullCore.
From Undecidability Require Import Shared.ListAutomation.
Import ListAutomationNotations.
From Stdlib Require Import Vector Lia.


Local Set Implicit Arguments.
Local Unset Strict Implicit.


Local Notation vec := Vector.t.


(* Tarski Semantics ***)


Section Tarski.

  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.

  (* Semantic notions *)
  
  Section Substs.
    
    Variable D : Type.
    Variable I : interp D.
        
    Lemma eval_ext rho xi t :
      (forall x, rho x = xi x) -> eval rho t = eval xi t.
    Proof.
      intros H. induction t; cbn.
      - now apply H.
      - f_equal. apply map_ext_in. now apply IH.
    Qed.

    Lemma eval_comp rho xi t :
      eval rho (subst_term xi t) = eval (xi >> eval rho) t.
    Proof.
      induction t; cbn.
      - reflexivity.
      - f_equal. rewrite map_map. apply map_ext_in, IH.
    Qed.
    Lemma eval_up ρ s t :
      eval (s .: ρ) t`[↑] = eval ρ t.
    Proof.
      rewrite eval_comp. apply eval_ext. reflexivity.
    Qed.

    Lemma sat_ext {ff : falsity_flag} rho xi phi :
      (forall x, rho x = xi x) -> rho ⊨ phi <-> xi ⊨ phi.
    Proof.
      induction phi  as [ | b P v | | ] in rho, xi |- *; cbn; intros H.
      - reflexivity.
      - erewrite map_ext; try reflexivity. intros t. now apply eval_ext.
      - specialize (IHphi1 rho xi). specialize (IHphi2 rho xi). destruct b0; intuition.
      - destruct q.
        + split; intros H' d; eapply IHphi; try apply (H' d). 1,2: intros []; cbn; intuition.
        + split; intros [d H']; exists d; eapply IHphi; try apply H'. 1,2: intros []; cbn; intuition.
    Qed.

    Lemma sat_ext' {ff : falsity_flag} rho xi phi :
      (forall x, rho x = xi x) -> rho ⊨ phi -> xi ⊨ phi.
    Proof.
      intros Hext H. rewrite sat_ext. exact H.
      intros x. now rewrite (Hext x).
    Qed.

    Lemma sat_comp {ff : falsity_flag} rho xi phi :
      rho ⊨ (subst_form xi phi) <-> (xi >> eval rho) ⊨ phi.
    Proof.
      induction phi as [ | b P v | | ] in rho, xi |- *; cbn.
      - reflexivity.
      - erewrite map_map, map_ext; try reflexivity. intros t. apply eval_comp.
      - specialize (IHphi1 rho xi). specialize (IHphi2 rho xi). destruct b0; intuition.
      - destruct q.
        + setoid_rewrite IHphi. split; intros H d; eapply sat_ext. 2, 4: apply (H d).
          all: intros []; cbn; trivial; now setoid_rewrite eval_comp.
        + setoid_rewrite IHphi. split; intros [d H]; exists d; eapply sat_ext. 2, 4: apply H.
          all: intros []; cbn; trivial; now setoid_rewrite eval_comp.
    Qed.

    Lemma sat_subst {ff : falsity_flag} rho sigma phi :
      (forall x, eval rho (sigma x) = rho x) -> rho ⊨ phi <-> rho ⊨ (subst_form sigma phi).
    Proof.
      intros H. rewrite sat_comp. apply sat_ext. intros x. now rewrite <- H.
    Qed.

    Lemma sat_single {ff : falsity_flag} (rho : nat -> D) (Phi : form) (t : term) :
      (eval rho t .: rho) ⊨ Phi <-> rho ⊨ subst_form (t..) Phi.
    Proof.
      rewrite sat_comp. apply sat_ext. now intros [].
    Qed.

    Lemma impl_sat {ff : falsity_flag} A rho phi :
      sat rho (A ==> phi) <-> ((forall psi, psi el A -> sat rho psi) -> sat rho phi).
    Proof.
      induction A; cbn; firstorder congruence.
    Qed.

    Lemma impl_sat' {ff : falsity_flag} A rho phi :
      sat rho (A ==> phi) -> ((forall psi, psi el A -> sat rho psi) -> sat rho phi).
    Proof.
      eapply impl_sat.
    Qed.

    Lemma bounded_eval_t n t sigma tau :
      (forall k, n > k -> sigma k = tau k) -> bounded_t n t -> eval sigma t = eval tau t.
    Proof.
      intros H. induction 1; cbn; auto.
      f_equal. now apply Vector.map_ext_in.
    Qed.
    
    Lemma bound_ext {ff : falsity_flag} N phi rho sigma :
      bounded N phi -> (forall n, n < N -> rho n = sigma n) -> (rho ⊨ phi <-> sigma ⊨ phi).
    Proof.
      induction 1 in sigma, rho |- *; cbn; intros HN; try tauto.
      - enough (map (eval rho) v = map (eval sigma) v) as E. now setoid_rewrite E.
        apply Vector.map_ext_in. intros t Ht.
        eapply bounded_eval_t; try apply HN. now apply H.
      - destruct binop; now rewrite (IHbounded1 rho sigma), (IHbounded2 rho sigma).
      - destruct quantop.
        + split; intros Hd d; eapply IHbounded.
          all : try apply (Hd d); intros [] Hk; cbn; auto.
          symmetry. all: apply HN; lia.
        + split; intros [d Hd]; exists d; eapply IHbounded.
          all : try apply Hd; intros [] Hk; cbn; auto.
          symmetry. all: apply HN; lia.
    Qed. 

    Corollary sat_closed {ff : falsity_flag} rho sigma phi :
      bounded 0 phi -> rho ⊨ phi <-> sigma ⊨ phi.
    Proof.
      intros H. eapply bound_ext. apply H. lia.
    Qed.

    Lemma subst_exist_sat {ff : falsity_flag} rho phi N :
      rho ⊨ phi -> bounded N phi -> forall rho, rho ⊨ (exist_times N phi).  
    Proof.
      induction N in phi, rho |-*; intros.
      - cbn. eapply sat_closed; eassumption.
      - cbn -[sat]. rewrite iter_switch. apply (IHN (S >> rho)).
        exists (rho 0). eapply sat_ext. 2: apply H.
        now intros [].
        now apply bounded_S_quant.
    Qed.

    Fact subst_exist_sat2 {ff : falsity_flag} N :
      forall rho phi, rho ⊨ (exist_times N phi) -> (exists sigma, sigma ⊨ phi).
    Proof.
      induction N.
      - eauto.
      - intros rho phi [? H]. now apply IHN in H.
    Qed.

    Lemma exists_close_form {ff : falsity_flag} N phi :
      bounded 0 (exist_times N phi) <-> bounded N phi.
    Proof.
      induction N in phi |- *.
      - reflexivity.
      - cbn. rewrite iter_switch.
        change (iter _ _ _) with (exist_times N (∃ phi)).
        setoid_rewrite IHN. symmetry.
        now apply bounded_S_quant.
    Qed.
    

  End Substs.

End Tarski.



(* Trivial Model *)

Section TM.

  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.

  Instance TM : interp unit :=
    {| i_func := fun _ _ => tt; i_atom := fun _ _ => True; |}.

  Fact TM_sat (rho : nat -> unit) (phi : form falsity_off) :
    rho ⊨ phi.
  Proof.
    revert rho. remember falsity_off as ff. induction phi; cbn; trivial.
    - discriminate.
    - destruct b0; auto.
    - destruct q; firstorder. exact tt.
  Qed.

  Fact TM_sat_decidable {ff} (rho : nat -> unit) (phi : form ff) :
    rho ⊨ phi \/ ~(rho ⊨ phi).
  Proof.
    revert rho. induction phi as [|? ? ?|ff [| |] phi IHphi psi IHpsi|ff [|] phi IHphi]; cbn; intros rho; eauto; try tauto.
    - destruct (IHphi rho), (IHpsi rho); tauto.
    - destruct (IHphi rho), (IHpsi rho); tauto.
    - destruct (IHphi rho), (IHpsi rho); tauto.
    - destruct (IHphi (tt .: rho)).
      + left; now intros [].
      + right; intros Hcc. apply H, Hcc.
    - destruct (IHphi (tt .: rho)).
      + left; now exists tt.
      + right; now intros [[] Hx].
  Qed.

End TM.
