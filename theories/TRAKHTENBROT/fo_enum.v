(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List Arith Lia Max.

From Undecidability.Shared.Libs.DLW.Utils
  Require Import utils_tac utils_list utils_nat.

From Undecidability.Shared.Libs.DLW.Vec 
  Require Import pos vec.

From Undecidability.TRAKHTENBROT
  Require Import notations utils decidable enumerable
                 fol_ops fo_sig fo_terms fo_logic.

Set Implicit Arguments.

(** * Enumerability of the type of FO formulas *)

Section fol_enumerable.

  (** Enumeration of FOL formulas *)

  Variable (Σ : fo_signature) 
           (H1 : discrete (syms Σ)) 
           (H2 : discrete (rels Σ))
           (H3 : type_enum_t (syms Σ))
           (H4 : type_enum_t (rels Σ)).

  Let Hunit : opt_enum_t (fun _ : unit => True).
  Proof. 
    apply type_enum_opt_enum_t.
    exists (fun _ => Some tt).
    intros []; exists 0; auto. 
  Qed.

  Let Hnat : opt_enum_t (fun _ : nat => True).
  Proof.
    apply type_enum_opt_enum_t.
    exists Some.
    intros n; exists n; auto.
  Qed.

  Let Hfol_bop : opt_enum_t (fun _ : fol_bop => True).
  Proof. 
    apply type_enum_opt_enum_t.
    exists (fun n => Some (match n with 0 => fol_conj | 1 => fol_disj | _ => fol_imp end)).
    intros [].
    + exists 0; auto.
    + exists 1; auto.
    + exists 2; auto.
  Qed.

  Let Hfol_qop : opt_enum_t (fun _ : fol_qop => True).
  Proof. 
    apply type_enum_opt_enum_t.
    exists (fun n => Some (match n with 0 => fol_fa | _ => fol_ex end)).
    intros [].
    + exists 1; auto.
    + exists 0; auto.
  Qed.

  Lemma type_enum_t_fo_term : type_enum_t (fo_term (ar_syms Σ)).
  Proof.
    apply type_enum_t_by_measure with (m := @fo_term_height _ _).
    induction n as [ | n Hn ].
    + generalize Hnat.
      apply opt_enum_t_image with in_var.
      intros [ i | s v ]; simpl.
      * split; auto; exists i; auto.
      * split; try lia; intros (? & _ & ?); discriminate.
    + generalize (opt_enum_t_dep_sum _ _ H1 H3 (fun s => opt_enum_t_vec (ar_syms Σ s) Hn)); intros H5.
      generalize (opt_enum_t_sum Hnat H5).
      apply opt_enum_t_image with 
        (f := fun p => 
                match p with 
                  | inl i => in_var i
                  | inr (existT _ s v) => @in_fot _ _ s v
                end).
      intros t; split.
      * destruct t as [ i | s v ]; intros H.
        - exists (inl i); auto.
        - exists (inr (existT _ s v)); simpl; split; auto.
          intros p; generalize (fo_term_height_lt _ v p); lia.
      * intros ([ i | (s,v) ] & H); revert H; simpl.
        - intros (_ & ->); simpl; lia.
        - intros (G & ->); simpl; apply le_n_S, lmax_spec, Forall_forall.
          intros x Hx; apply vec_list_inv in Hx.
          destruct Hx as (p & Hp); revert Hp; rew vec; intros ->; auto.
  Qed.

  Theorem type_enum_t_fol_form : type_enum_t (fol_form Σ).
  Proof.
    apply type_enum_t_by_measure with (m := @fol_height _).
    induction n as [ | n Hn ].
    + exists (fun n => None).
      intros [ | | | ]; simpl; split; try lia; intros (? & ?); discriminate.
    + generalize type_enum_t_fo_term; intros H5.
      apply type_enum_opt_enum_t in H5.
      generalize (opt_enum_t_dep_sum _ _ H2 H4 (fun r => opt_enum_t_vec (ar_rels Σ r) H5)); intros H6.
      generalize (opt_enum_t_prod Hfol_bop (opt_enum_t_prod Hn Hn)); intros H7.
      generalize (opt_enum_t_prod Hfol_qop Hn); intros H8.
      generalize (opt_enum_t_sum (opt_enum_t_sum Hunit H6) (opt_enum_t_sum H7 H8)).
      apply opt_enum_t_image with 
        (f := fun p => 
                match p with 
                  | inl (inl _) => ⊥
                  | inl (inr (existT _ r v)) => fol_atom r v
                  | inr (inl (b,(A,B)))      => fol_bin b A B
                  | inr (inr (q,A))          => fol_quant q A
                end).
      intros A; split.
      * revert A; intros [ | r v | b A B | q A ]; simpl; intros H.
        - exists (inl (inl tt)); auto.
        - exists (inl (inr (existT _ r v))); simpl; auto.
        - apply le_S_n in H.
          exists (inr (inl (b,(A,B)))); simpl; repeat split; auto; 
            apply le_trans with (2 := H).
          ++ apply le_max_l.
          ++ apply le_max_r.
        - apply le_S_n in H.
          exists (inr (inr (q,A))); simpl; repeat split; auto. 
      * intros ([ [ [] | (r&v) ] | [ (b,(B,C)) | (q,B) ] ] & H); revert H; simpl.
        - intros (_ & ->); simpl; lia.
        - intros (_ & ->); simpl; lia.
        - intros ((_ & G1 & G2) & ->); simpl.
          apply le_n_S, max_lub; auto.
        - intros ((_ & G1) & ->); simpl; lia.
  Qed.

End fol_enumerable.
