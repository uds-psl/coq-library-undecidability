(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List Arith Bool Lia.

From Undecidability.Shared.Libs.DLW.Utils
  Require Import utils_tac utils_list utils_nat finite.

From Undecidability.Shared.Libs.DLW.Vec 
  Require Import pos vec.

From Undecidability.Shared.Libs.DLW.Wf 
  Require Import wf_finite.

From Undecidability.TRAKHTENBROT
  Require Import notations fol_ops fo_terms fo_logic fol_bpcp.

Set Implicit Arguments.

Local Notation ø := vec_nil.

(** A signature with 7 binary relations *)

Definition Σ2 : fo_signature.
Proof.
  exists Empty_set (bpcp_syms+bpcp_rels)%type.
  + intros [].
  + exact (fun _ => 2).
Defined.

Section Σbpcp_Σ2.

  Notation term := (fo_term nat (ar_syms Σbpcp)).
  Notation form := (fol_form Σbpcp).

  Notation e := (in_fot fe ø).
  Notation "∗" := (in_fot fs ø).
 
  Notation "¬" := (fun x => x ⤑ ⊥).
  Notation 𝓟  := (fun x y => fol_atom Σbpcp p_P (x##y##ø)).
  Notation "x ≡ y" := (fol_atom Σbpcp p_eq (x##y##ø)) (at level 59).
  Notation "x ≺ y" := (fol_atom Σbpcp p_lt (x##y##ø)) (at level 59).

  Notation f_ := (fun b x => @in_fot _ _ _ (fb b) (x##ø) : term).

  Variable (X : Type) (M : fo_model Σbpcp X).

  Definition K : fo_model Σ2 X.
  Proof.
    exists.
    + intros [].
    + intros [ [ b | | ] | r ]; simpl; intros v;
        set (x := vec_head v); set (y := vec_head (vec_tail v)).
      * exact (fom_syms M (fb b) (x##ø) = y).
      * exact (fom_syms M fe ø = y).
      * exact (fom_syms M fs ø = y).
      * exact (fom_rels M r v).
  Defined.

  Check fom_syms M.

  Notation "⟦ t ⟧" := (fun φ => fo_term_sem (fom_syms M) φ t).
  Notation "⟪ A ⟫" := (fun φ => fol_sem M φ A).

  Notation "⟦ t ⟧'" := (fun φ => fo_term_sem (fom_syms K) φ t) (at level 1, format "⟦ t ⟧'").
  Notation "⟪ A ⟫'" := (fun φ => fol_sem K φ A)  (at level 1, format "⟪ A ⟫'").

(*  Ltac eqgoal := let E := fresh in match goal with |- ?a -> ?b => cut (a=b); [ intros E; rewrite E; trivial | ] end. *)

  Hypothesis M_strict : forall x y, fom_rels M p_eq (x##y##ø) <-> y = x.

  Notation "⇡ f" := (fol_subst (fun n => 
                         match n with 
                           | 0 => £0 
                           | _ => £ (1+n) 
                         end) f).

  (** This is painless with fo_term_recursion .... try it by structural induction ;-) 

      From a term t we build a formula st 

            [[ t ]] phi = y <-> << A_t >> (phi lift y)

    *)

  Definition fot_fol (t : term) : fol_form Σ2.
  Proof.
    induction t as [ i | [ b | | ] v w ] using fo_term_recursion; try simpl ar_syms at 2 in v.
    + apply (fol_atom Σ2 (inr p_eq) (£0##£(1+i)##ø)).
    + refine (∃ ( ⇡(vec_head w) ⟑ fol_atom Σ2 (inl (fb b)) (£0##£1##ø))).
    + exact (fol_atom Σ2 (inl fe) (£0##£0##ø)).
    + exact (fol_atom Σ2 (inl fs) (£0##£0##ø)).
  Defined.

  Fact fot_fol_fix_var i : 
        fot_fol (£i) = fol_atom Σ2 (inr p_eq) (£0##£(1+i)##ø).
  Proof. apply fo_term_recursion_fix_0. Qed.

  Fact fot_fol_fix_b b t : 
        fot_fol (f_ b t) = ∃ ( ⇡(fot_fol t) ⟑ fol_atom Σ2 (inl (fb b)) (£0##£1##vec_nil)).
  Proof. apply fo_term_recursion_fix_1. Qed.

  Fact fot_fol_fix_e : 
        fot_fol e = fol_atom Σ2 (inl fe) (£0##£0##ø).
  Proof. apply fo_term_recursion_fix_1. Qed.

  Fact fot_fol_fix_s : 
        fot_fol ∗ = fol_atom Σ2 (inl fs) (£0##£0##ø).
  Proof. apply fo_term_recursion_fix_1. Qed.

  Opaque fot_fol.

  (** The embedding preserve the semantics *)

  Lemma fot_fol_sem t φ x : ⟪ fot_fol t ⟫' (φ↑x) <-> ⟦t⟧ φ = x.
  Proof.
    revert φ x; induction t as [ i | [ b | | ] v IH ]; intros phi x; simpl; rew fot.
    + rewrite fot_fol_fix_var; simpl; rew fot; simpl; auto; simpl.
    + revert IH; simpl ar_syms at 2 in v; vec split v with t. 
      vec nil v; clear v; intros IH.
      specialize (IH _ (or_introl eq_refl)).
      rewrite fot_fol_fix_b.
      split.
      * intros (z & H1 & H2); revert H1 H2. 
        rewrite fol_sem_subst; simpl; rew fot; simpl.
        intros H E; rewrite <- E; do 2 f_equal; apply IH.
        revert H; apply fol_sem_ext.
        intros [ | [ | n ] ]; simpl; rew fot; simpl; auto.
      * intros <-.
        exists (⟦t⟧ phi); split.
        - rewrite fol_sem_subst.
          generalize (proj2 (IH phi _) eq_refl).
          apply fol_sem_ext; intros [ | n ]; simpl; rew fot; simpl; auto.
        - simpl; rew fot; simpl; auto. 
    + clear IH; vec nil v; rew fot; simpl; tauto.
    + clear IH; vec nil v; rew fot; simpl; tauto.
  Qed.

  Definition fot_fol0 t := fol_subst (fun n => 
                             match n with 
                               | 0 => £0 
                               | _ => £ (1+n) 
                             end) (fot_fol t).

  Definition fot_fol1 t := fol_subst (fun n => 
                             match n with 
                               | 0 => £1 
                               | _ => £ (1+n) 
                             end) (fot_fol t).

  Fact fot_fol0_sem t φ x y : ⟪ fot_fol0 t ⟫' (φ↑y↑x) <-> ⟦t⟧ φ = x.
  Proof.
    unfold fot_fol0; simpl.
    rewrite fol_sem_subst.
    rewrite <- fot_fol_sem.
    apply fol_sem_ext.
    intros [ | [ | n ] ]; simpl; rew fot; simpl; auto.
  Qed.

  Fact fot_fol1_sem t φ x y : ⟪ fot_fol1 t ⟫' (φ↑y↑x) <-> ⟦t⟧ φ = y.
  Proof.
    unfold fot_fol1; simpl.
    rewrite fol_sem_subst.
    rewrite <- fot_fol_sem.
    apply fol_sem_ext.
    intros [ | [ | n ] ]; simpl; rew fot; simpl; auto.
  Qed.

  Fixpoint fol_fol (A : fol_form Σbpcp) : fol_form Σ2.
  Proof.
    destruct A as [ | r v | b A B | q A ].
    + apply fol_false.
    + simpl ar_rels at 1 in v.
      exact (∃∃ (fol_atom Σ2 (inr r) (£0##£1##ø) ⟑ fot_fol0 (vec_head v) ⟑ fot_fol1 (vec_head (vec_tail v)))).
    + apply (fol_bin b (fol_fol A) (fol_fol B)).
    + apply (fol_quant q (fol_fol A)).
  Defined.

  (** The encoding is faithfull on the models *)

  Theorem fol_fol_sem A φ : ⟪fol_fol A⟫' φ <-> ⟪A⟫ φ.
  Proof.
    revert φ; induction A as [ | r v | b A HA B HB | q A HA ]; intro phi; simpl; try tauto.
    + vec split v with x; vec split v with y; vec nil v; clear v; simpl.
      split.
      * intros (u & v & H1 & H2 & H3); revert H1 H2 H3.
        rewrite fot_fol0_sem, fot_fol1_sem; intros; subst; auto.
      * intros H.
        exists (⟦y⟧ phi), (⟦x⟧ phi); msplit 2; simpl; rew fot; simpl; auto.
        - rewrite fot_fol0_sem; auto.
        - rewrite fot_fol1_sem; auto.
    + apply fol_bin_sem_ext; auto.
    + apply fol_quant_sem_ext; auto.
  Qed. 
 
End Σbpcp_Σ2.

Section Σ2_Σbpcp.

End Σ2_Σbpcp. 

(** A reduction from SAT(Σbpcp) to SAT(Σ2) when eq is interpreted with identity 
    
    Question: if we axiomatize congruence for eq and add it to the encoding,
              can we get the reduction w/o assuming interpreted identity

*)

Check fol_fol_sem.


