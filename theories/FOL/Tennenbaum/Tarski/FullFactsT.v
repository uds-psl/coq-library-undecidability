(* * Tarski Semantics *)

Require Import Undecidability.FOL.Syntax.Facts.
Require Export Undecidability.FOL.Tennenbaum.Tarski.FullCoreT.
From Undecidability Require Import Shared.ListAutomation.
Import ListAutomationNotations.
Require Import Vector Lia.
Require Import Undecidability.FOL.Tennenbaum.Utils.Iff.

Local Set Implicit Arguments.
Local Unset Strict Implicit.

Set Default Proof Using "Type".

Local Notation vec := Vector.t.

Local Notation "A <=> B" := (prod(A -> B)(B -> A)) (at level 70).




(** Tarski Semantics ***)


Section Tarski.

  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.

  (* Semantic notions *)
  
  Section Substs.
    
    Variable D : Type.
    Variable I : interp D.

    Lemma eval_ext ρ xi t :
      (forall x, ρ x = xi x) -> eval ρ t = eval xi t.
    Proof.
      intros H. induction t; cbn.
      - now apply H.
      - f_equal. apply map_ext_in. now apply IH.
    Qed.

    Lemma eval_comp ρ xi t :
      eval ρ (subst_term xi t) = eval (xi >> eval ρ) t.
    Proof.
      induction t; cbn.
      - reflexivity.
      - f_equal. rewrite map_map. apply map_ext_in, IH.
    Qed.


    Lemma saT_ext {ff : falsity_flag} ρ xi ϕ :
      (forall x, ρ x = xi x) -> ρ ⊨ ϕ <=> xi ⊨ ϕ.
    Proof.
      induction ϕ  as [ | b P v | | ] in ρ, xi |- *; cbn; intros H.
      - tauto.
      - erewrite map_ext. 2: intros t; now apply eval_ext. tauto.
      - specialize (IHϕ1 ρ xi). specialize (IHϕ2 ρ xi). destruct b0; intuition.
      - destruct q.
        + split; intros H' d; eapply IHϕ; try apply (H' d). 1,2: intros []; cbn; intuition.
        + split; intros [d H']; exists d; eapply IHϕ; try apply H'. 1,2: intros []; cbn; intuition.
    Qed.

    Lemma saT_ext' {ff : falsity_flag} ρ xi ϕ :
      (forall x, ρ x = xi x) -> ρ ⊨ ϕ -> xi ⊨ ϕ.
    Proof.
      intros Hext. eapply saT_ext in Hext as []; eauto. 
    Qed.

    Lemma saT_comp {ff : falsity_flag} ρ xi ϕ :
      ρ ⊨ (subst_form xi ϕ) <=> (xi >> eval ρ) ⊨ ϕ.
    Proof.
      induction ϕ as [ | b P v | | ] in ρ, xi |- *; cbn.
      - tauto.
      - erewrite map_map, map_ext. 2: intros t; apply eval_comp. tauto.
      - specialize (IHϕ1 ρ xi). specialize (IHϕ2 ρ xi). destruct b0; intuition.
      - destruct q; split; intros H.
        + intros d. specialize (H d). apply IHϕ in H.
          eapply saT_ext. 2: apply H.
          intros []; cbn; trivial. now setoid_rewrite eval_comp.
        + intros d. specialize (H d). apply IHϕ.
          eapply saT_ext. 2: apply H.
          intros []; cbn; trivial. now setoid_rewrite eval_comp.
        + destruct H as [d H]. exists d. 
          apply IHϕ in H. eapply saT_ext. 2: apply H.
          intros []; cbn; trivial. now setoid_rewrite eval_comp.
        + destruct H as [d H]. exists d. 
          apply IHϕ. eapply saT_ext. 2: apply H.
          intros []; cbn; trivial. now setoid_rewrite eval_comp.
    Qed.

    Lemma saT_subst {ff : falsity_flag} ρ sigma ϕ :
      (forall x, eval ρ (sigma x) = ρ x) -> ρ ⊨ ϕ <=> ρ ⊨ (subst_form sigma ϕ).
    Proof.
      intros H. eapply Iff_trans.
      2: apply Iff_sym, saT_comp.
      eapply saT_ext. intros x. now rewrite <-H.
    Qed.

    Lemma saT_single {ff : falsity_flag} (ρ : nat -> D) (ϕ : form) (t : term) :
      (eval ρ t .: ρ) ⊨ ϕ <=> ρ ⊨ subst_form (t..) ϕ.
    Proof.
      eapply Iff_trans.
      2: apply Iff_sym, saT_comp.
      apply saT_ext. now intros [].
    Qed.

    Lemma impl_saT {ff : falsity_flag} A ρ ϕ :
      saT ρ (A ==> ϕ) <=> ((forall psi, psi el A -> saT ρ psi) -> saT ρ ϕ).
    Proof.
      induction A; cbn; [firstorder|].
      split; [firstorder|].
      intros H Ha. apply IHA. intros HA.
      apply H. intros α TODO.
      (*  Need to use a lemma which shows that TODO is decidable.
          Otherwise I cannot destruct it to proceed.
       *)
    Admitted.

    Lemma impl_saT' {ff : falsity_flag} A ρ ϕ :
      saT ρ (A ==> ϕ) -> ((forall psi, psi el A -> saT ρ psi) -> saT ρ ϕ).
    Proof.
      eapply impl_saT.
    Qed.

    Lemma bounded_eval_t n t sigma tau :
      (forall k, n > k -> sigma k = tau k) -> bounded_t n t -> eval sigma t = eval tau t.
    Proof.
      intros H. induction 1; cbn; auto.
      f_equal. now apply Vector.map_ext_in.
    Qed.
    
    Lemma bound_ext {ff : falsity_flag} N ϕ ρ sigma :
      bounded N ϕ -> (forall n, n < N -> ρ n = sigma n) -> (ρ ⊨ ϕ <=> sigma ⊨ ϕ).
    Proof.
    (*  This also needs a type-level definition of
        the boundedness predicate I think. 
    *)

(*  induction 1 in sigma, ρ |- *; cbn; intros HN; try tauto.
      - enough (map (eval ρ) v = map (eval sigma) v) as E. now setoid_rewrite E.
        apply Vector.map_ext_in. intros t Ht.
        eapply bounded_eval_t; try apply HN. now apply H.
      - destruct binop; now rewrite (IHbounded1 ρ sigma), (IHbounded2 ρ sigma).
      - destruct quantop.
        + split; intros Hd d; eapply IHbounded.
          all : try apply (Hd d); intros [] Hk; cbn; auto.
          symmetry. all: apply HN; lia.
        + split; intros [d Hd]; exists d; eapply IHbounded.
          all : try apply Hd; intros [] Hk; cbn; auto.
          symmetry. all: apply HN; lia. *)
    Admitted. 

    Corollary saT_closed {ff : falsity_flag} ρ sigma ϕ :
      bounded 0 ϕ -> ρ ⊨ ϕ <=> sigma ⊨ ϕ.
    Proof.
      intros H. eapply bound_ext. apply H. lia.
    Qed.

    Lemma subst_exist_saT {ff : falsity_flag} ρ ϕ N :
      ρ ⊨ ϕ -> bounded N ϕ -> forall ρ, ρ ⊨ (exist_times N ϕ).  
    Proof.
      induction N in ϕ, ρ |-*; intros.
      - cbn. eapply saT_closed; eassumption.
      - cbn -[saT]. rewrite iter_switch. apply (IHN (S >> ρ)).
        exists (ρ 0). eapply saT_ext. 2: eassumption.
        now intros [].
        now apply bounded_S_quant.
    Qed.

    Fact subst_exist_saT2 {ff : falsity_flag} N :
      forall ρ ϕ, ρ ⊨ (exist_times N ϕ) -> { sigma & sigma ⊨ ϕ }.
    Proof.
      induction N; eauto.
      intros ρ ϕ [? H]. now apply IHN in H.
    Qed.

    Lemma exists_close_form {ff : falsity_flag} N ϕ :
      bounded 0 (exist_times N ϕ) <=> bounded N ϕ.
    Proof.
      induction N in ϕ |- *.
      - tauto.
      - cbn. rewrite iter_switch.
        change (iter _ _ _) with (exist_times N (∃ ϕ)).
        eapply Iff_trans. 1 : apply IHN.
        symmetry.
        (* apply bounded_S_quant. *)
    Admitted.
    

  End Substs.

End Tarski.