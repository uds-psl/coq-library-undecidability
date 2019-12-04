(**************************************************************)
(*   Copyright Dominik Kirst              [+]                 *)
(*             Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [+] Affiliation U. Sarrbrucken *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

(** The code was initially developed by Dominik Kirst to be 
    reimported to this alternate syntax & framework by @DLW 
*) 

Require Import List Arith Lia.

From Undecidability.Shared.Libs.DLW.Utils
  Require Import utils_tac.

From Undecidability.Shared.Libs.DLW.Vec 
  Require Import pos vec.

From Undecidability.TRAKHTENBROT
  Require Import notations utils fol_ops fo_terms fo_logic.

Set Implicit Arguments.

Local Reserved Notation "⟦ t ⟧'" (at level 1, format "⟦ t ⟧'").
Local Reserved Notation "⟪ A ⟫'" (at level 1, format "⟪ A ⟫'").

Local Notation ø := vec_nil.

Fact cast_vec_map X Y (f : X -> Y) n m (v : vec X n) (H : n = m) :
       cast (vec_map f v) H = vec_map f (cast v H).
Proof. subst; auto. Qed.

Section Uniform_arities_to_one.

  Variable (Σ : fo_signature) 
           (a : nat) (Ha : forall r, ar_rels Σ r = S a).

  Definition Σone_rel : fo_signature.
  Proof.
    exists (syms Σ + (unit + rels Σ))%type unit.
    + intros [ s | ].
      * exact (ar_syms _ s).
      * exact 0.
    + exact (fun _ => 2+a).
  Defined.

  Notation Σ' := Σone_rel.

  Notation 𝕋 := (fo_term nat (ar_syms Σ)).
  Notation 𝔽 := (fol_form Σ).

  Notation 𝕋' := (fo_term nat (ar_syms Σ')).
  Notation 𝔽' := (fol_form Σ').

  Let Fixpoint convert_t (t : 𝕋) : 𝕋' :=
    match t with
    | in_var s   => in_var s
    | in_fot s v => in_fot (inl s) (vec_map convert_t v)
    end.

  Let convert_v n (v : vec _ n) := vec_map convert_t v.

  Let D x := fol_atom Σ' tt (in_fot (inr (inl tt)) ø##vec_set_pos (fun _ => £x)).

  (** This encoding uses a extra (unary) relation to represent the domain 
      and allow for the below simulation relation to be limited to the domain *)

  Fixpoint Σunif_one_rel (A : 𝔽) : 𝔽' :=
    match A with
      | ⊥              => ⊥
      | fol_atom _ r v => fol_atom Σ' tt (in_fot (inr (inr r)) ø##cast (convert_v v) (Ha _))
      | fol_bin b A B  => fol_bin b (Σunif_one_rel A) (Σunif_one_rel B)
      | ∀ A            => ∀ D 0 ⤑ Σunif_one_rel A
      | ∃ A            => ∃ D 0 ⟑ Σunif_one_rel A
    end.

  Notation encode := Σunif_one_rel.

  Section simulation.

    (* We prove a general simulation result *)
  
    Variables (X : Type) (M : fo_model Σ X)
              (Y : Type) (M' : fo_model Σ' Y).

    Variable (R : X -> Y -> Prop).

    Let d y := fom_rels M' tt (fom_syms M' (inr (inl tt)) ø##vec_set_pos (fun _ => y)).

    Infix "⋈" := R (at level 70, no associativity).
    Notation "v '⋈v' w" := (forall p, vec_pos v p ⋈ vec_pos w p) (at level 70, no associativity).

    Hypothesis (HR1 : forall s v w, v ⋈v w -> fom_syms M s v ⋈ fom_syms M' (inl s) w)
               (HR2 : forall r v w, v ⋈v w -> fom_rels M r v 
                                           <-> fom_rels M' tt (fom_syms M' (inr (inr r)) ø##cast w (Ha _)))
               (HR3 : forall x, exists y, d y /\ x ⋈ y)
               (HR4 : forall y, d y -> exists x, x ⋈ y).
    
    Notation "⟦ t ⟧" := (fun φ => fo_term_sem (fom_syms M) φ t).
    Notation "⟦ t ⟧'" := (fun ψ => fo_term_sem (fom_syms M') ψ t).

    Let convert_t_simul (t : 𝕋) φ ψ : 
             (forall n, In n (fo_term_vars t) -> φ n ⋈ ψ n)
          -> ⟦t⟧ φ ⋈ ⟦convert_t t⟧' ψ.
    Proof.
      intros H.
      induction t as [ n | s v IHt ] using fo_term_pos_rect in φ, ψ, H |- *; simpl.
      + apply H; simpl; auto.
      + simpl; apply HR1; intros p; rew vec; rewrite vec_pos_map; apply IHt.
        intros n Hn; apply H; rew fot.
        rewrite in_flat_map; exists (vec_pos v p); split; auto.
        apply in_vec_list, in_vec_pos.
    Qed.

    Notation "⟪ A ⟫" := (fun φ => fol_sem M φ A).
    Notation "⟪ A ⟫'" := (fun ψ => fol_sem M' ψ A).

    Local Fact encode_simul A φ ψ : 
              (forall n, In n (fol_vars A) -> φ n ⋈ ψ n)
           -> ⟪A⟫ φ <-> ⟪encode A⟫' ψ.
    Proof.
      intros H.
      induction A as [ | r v | b A HA B HB | [] A HA ] in φ, ψ, H |- *; 
        try tauto.
      + unfold encode, fol_sem, convert_v.
        rewrite (HR2 _ _ (vec_map (fo_term_sem (fom_syms M') ψ) (convert_v v))).
        * apply fol_equiv_ext; f_equal; simpl; rewrite cast_vec_map; auto.
        * unfold convert_v; intros p; rew vec; apply convert_t_simul.
          intros n Hn; apply H; simpl; rew fot.
          rewrite in_flat_map; exists (vec_pos v p); split; auto.
          apply in_vec_list, in_vec_pos.
      + apply fol_bin_sem_ext.
        * apply HA; intros; apply H, in_app_iff; auto.
        * apply HB; intros; apply H, in_app_iff; auto.
      + simpl; split.
        * intros (x & Hx).
          destruct (HR3 x) as (y & Hd & Hy).
          exists y; split; auto.
          - red in Hd; revert Hd; simpl.
            apply fol_equiv_ext; do 3 f_equal.
            apply vec_pos_ext; intros p; rew vec.
          - revert Hx; apply HA.
            intros [|n] Hn; simpl; auto.
            apply H, in_flat_map; exists (S n); simpl; auto.
        * intros (y & Hd & Hy).
          destruct (HR4 y) as (x & Hx).
          - red; revert Hd; simpl.
            apply fol_equiv_ext; do 3 f_equal.
            apply vec_pos_ext; intros p; rew vec.
          - exists x; revert Hy; apply HA.
            intros [|n] Hn; simpl; auto.
            apply H, in_flat_map; exists (S n); simpl; auto.
      + simpl; split.
        * intros H1 y Hd.
          destruct (HR4 y) as (x & Hx).
          - red; revert Hd; simpl.
            apply fol_equiv_ext; do 3 f_equal.
            apply vec_pos_ext; intros p; rew vec.
          - generalize (H1 x); apply HA.
            intros [|n] Hn; simpl; auto.
            apply H, in_flat_map; exists (S n); simpl; auto.
        * intros H1 x.
          destruct (HR3 x) as (y & Hd & Hy).
          rewrite HA.
          - apply (H1 y).
            red in Hd; revert Hd; simpl.
            apply fol_equiv_ext; do 3 f_equal.
            apply vec_pos_ext; intros p; rew vec.
          - intros [|n] Hn; simpl; auto.
            apply H, in_flat_map; exists (S n); simpl; auto.
    Qed.

  End simulation.

  Section soundness.

    Variable (X : Type) (M : fo_model Σ X).

    Notation Y := (X + (unit + rels Σ))%type.

    Let vec_inv n (w : vec Y n) : { v | w = vec_map inl v } + { p : _ & { k | vec_pos w p = inr k } }.
    Proof.
      induction w as [ | n [ x | k ] w IHw ].
      + left; exists ø; auto. 
      + destruct IHw as [ (v & Hv) | (p & k & Hk) ].
        * left; exists (x##v); subst; auto.
        * right; exists (pos_nxt p), k; subst; subst; auto.
      + right; exists pos0, k; auto.
    Qed.

    Tactic Notation "dest" "vec_inv" ident(v) ident(p) ident(H) := 
      match goal with |- context[vec_inv ?t] => destruct (vec_inv t) as [ (v & H) | (p & ? & H) ] end.

    Definition Σunif_one_rel_model : fo_model Σ' Y.
    Proof.
      split.
      + exact (fun x => 
         match x as x' return vec Y (ar_syms Σ' x') -> _ with
           | inl s => fun w => 
           match vec_inv w with
             | inl (exist _ v _) => inl (fom_syms M s v)
             | inr _            => inr (inl tt)
           end
           | inr (inl _) => fun _ => inr (inl tt)
           | inr (inr r) => fun _ => inr (inr r)
         end).
      + exact (fun _ w => 
          match vec_head w with
            | inr (inr r) => 
            match vec_inv (vec_tail w) with
             | inl (exist _ v _) => fom_rels M r (cast v (eq_sym (Ha _)))
             | inr _             => True
            end
            | inr (inl tt) => 
            match vec_inv (vec_tail w) with
             | inl (exist _ v _) => True
             | inr _             => False
            end
            | inl _ => False
          end).
    Defined.

    Notation M' := Σunif_one_rel_model.

    Let R (x : X) (y : Y) :=
       match y with 
         | inl x' => x = x'
         | inr _  => False
       end.

    Notation "⟪ A ⟫" := (fun φ => fol_sem M φ A).
    Notation "⟪ A ⟫'" := (fun ψ => fol_sem M' ψ A).


    Lemma Σunif_one_rel_sound A φ : ⟪A⟫ φ <-> ⟪encode A⟫' (fun n => inl (φ n)).
    Proof.
      apply encode_simul with (R := R); unfold R; auto.
      + intros s v w H.
        simpl; destruct (vec_inv w) as [ (v' & Hv) | (p & k & Hk) ]; auto.
        * f_equal; apply vec_pos_ext; intros p.
          specialize (H p); subst w; revert H; rew vec.
        * generalize (H p); rewrite Hk; auto.
      + intros r; simpl.
        generalize (Ha r); intros E; rewrite <- E; simpl.
        intros v w H.
        destruct (vec_inv w) as [ (v' & Hv) | (p & k & Hk) ]; auto.
        * apply fol_equiv_ext; f_equal; apply vec_pos_ext.
          intros p; generalize (H p); subst w; rew vec.
        * specialize (H p); rewrite Hk in H; tauto.
      + intros x; exists (inl x); simpl; dest vec_inv v p G; auto.
        exfalso; revert G; invert pos p; rew vec; discriminate.
      + intros [ x | [ [] | r ] ].
        * exists x; auto.
        * simpl; dest vec_inv v p G; try tauto. 
          revert G; vec split v with x; discriminate.
        * simpl; dest vec_inv v p G; try tauto.
          revert G; vec split v with x; discriminate.
    Qed.

  End soundness.

  Section completeness.

    Variable (Y : Type) (M' : fo_model Σ' Y) (HM' : fo_model_dec M').

    Let d x := if @HM' tt (fom_syms M' (inr (inl tt)) ø##vec_set_pos (fun _ => x)) then true else false.

    Let d_prop x : d x = true <-> fom_rels M' tt (fom_syms M' (inr (inl tt)) ø##vec_set_pos (fun _ => x)).
    Proof.
      unfold d.
      destruct (@HM' tt (fom_syms M' (inr (inl tt)) ø##vec_set_pos (fun _ => x))); split; try tauto; discriminate.
    Qed.

    Let X := sig (fun x => d x = true).

    (** The model is recovered using constants as indices for each relation *)

    Definition Σone_unif_rel_model : fo_model Σ X.
    Proof.
      split.
      + exact (fun s v => fom_syms M' (inl s) v).
      + exact (fun r v => fom_rels M' tt (fom_syms M' (inr (inr r)) ø##cast v (Ha _))).
    Defined.

    Notation M := Σone_unif_rel_model.

    Notation "⟪ A ⟫" := (fun φ => fol_sem M φ A).
    Notation "⟪ A ⟫'" := (fun ψ => fol_sem M' ψ A).

    Let R (x : X) (y : X) := x = y.

    Lemma Σunif_one_rel_complete A φ : ⟪A⟫ φ <-> ⟪encode A⟫' φ.
    Proof.
      apply encode_simul with (R := eq).
      + intros s v w H; simpl; f_equal; apply vec_pos_ext; auto.
      + intros r v w H; simpl.
        apply fol_equiv_ext; do 3 f_equal.
        apply vec_pos_ext; auto.
      + intros x; exists x; split; auto; simpl.

      induction A as [ | r v | | ] in φ |- *; cbn; try tauto.
      + apply fol_equiv_ext; do 2 f_equal.
        revert v; generalize (Ha r); rewrite Ha; intros E v. 
        rewrite eq_nat_uniq with (H := E).
        unfold convert_v; rewrite !cast_refl, vec_map_map.
        apply vec_pos_ext; intro; rew vec.
        generalize (vec_pos v p); intros []; simpl; auto; exfalso; auto.
      + apply fol_bin_sem_ext; auto.
      + apply fol_quant_sem_ext; intro; auto.
    Qed.

  End completeness.

End Uniform_arities_to_one.
