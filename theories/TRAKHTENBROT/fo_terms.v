(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List Arith Lia.

From Undecidability.Shared.Libs.DLW.Utils
  Require Import utils_tac utils_list utils_nat finite.

From Undecidability.Shared.Libs.DLW.Vec 
  Require Import pos vec.

From Undecidability.TRAKHTENBROT
  Require Import notations utils fol_ops fo_sig.

Set Implicit Arguments.

(** Then first order terms with signature *)

Local Hint Resolve in_vec_list in_vec_pos.

Section first_order_terms.

  Variable (syms : Type) (ar_syms : syms -> nat).

  Unset Elimination Schemes.       (* we do not want the autogen recursors *)

  (** The Type of first order terms over signature s *)

  Inductive fo_term : Type :=
    | in_var : nat -> fo_term
    | in_fot : forall s, vec fo_term (ar_syms s) -> fo_term.

  Set Elimination Schemes.

  Section fo_term_rect.
   
    Variable (P   : fo_term -> Type)
             (HP0 : forall x, P (in_var x))
             (IHP : forall s v, (forall p, P (vec_pos v p)) -> P (@in_fot s v)).

    Fixpoint fo_term_rect t : P t :=
      match t with
        | in_var x => HP0 x 
        | in_fot v => IHP v (fun p => fo_term_rect (vec_pos v p))
      end.

  End fo_term_rect.

  Definition fo_term_rec (P : _ -> Set) := @fo_term_rect P.
  Definition fo_term_ind (P : _ -> Prop) := @fo_term_rect P.

  Fixpoint fo_term_vars t :=
    match t with 
      | in_var x    => x::nil
      | @in_fot s v => concat (vec_list (vec_map fo_term_vars v))
    end.

  Fact fo_term_vars_fix_0 x : fo_term_vars (in_var x) = x :: nil.
  Proof. trivial. Qed.

  Fact fo_term_vars_fix_1 s v : fo_term_vars (@in_fot s v) = flat_map fo_term_vars (vec_list v).
  Proof. simpl; rewrite vec_list_vec_map, <- flat_map_concat_map; auto. Qed.

  Fixpoint fo_term_syms t :=
    match t with 
      | in_var x    => nil
      | @in_fot s v => s::concat (vec_list (vec_map fo_term_syms v))
    end.

  Fact fo_term_syms_fix_0 x : fo_term_syms (in_var x) = nil.
  Proof. trivial. Qed.

  Fact fo_term_syms_fix_1 s v : fo_term_syms (@in_fot s v) = s::flat_map fo_term_syms (vec_list v).
  Proof. simpl; rewrite vec_list_vec_map, <- flat_map_concat_map; auto. Qed.

  Fixpoint fo_term_subst σ t :=
    match t with 
      | in_var x => σ x
      | in_fot v => in_fot (vec_map (fo_term_subst σ) v)
    end.

  Notation "t ⟬ σ ⟭" := (fo_term_subst σ t).

  Fact fo_term_subst_fix_0 σ x : (in_var x)⟬σ⟭  = σ x.
  Proof. trivial. Qed.

  Fact fo_term_subst_fix_1 σ s v : 
          (@in_fot s v)⟬σ⟭  = in_fot (vec_map (fo_term_subst σ) v).
  Proof. trivial. Qed.

  Fact fo_term_subst_ext f g t : 
     (forall x, In x (fo_term_vars t) -> f x = g x) -> t⟬f⟭ = t⟬g⟭.
  Proof.
    induction t as [ | s v IHv ]; intros Hfg; simpl.
    + apply Hfg; simpl; auto.
    + f_equal; apply vec_map_ext.
      intros x Hx. 
      apply in_vec_list, vec_list_inv in Hx.
      destruct Hx as (p & ->).
      apply IHv.
      intros y Hy; apply Hfg.
      rewrite fo_term_vars_fix_1, in_flat_map.
      exists (vec_pos v p).
      split; auto; apply in_vec_list; auto.
  Qed.

  Section fo_term_subst_comp.

    Variables (f g : nat -> fo_term).

    Fact fo_term_subst_comp t : t⟬f⟭ ⟬g⟭ = t⟬fun x => (f x)⟬g⟭ ⟭ . 
    Proof.
      induction t; simpl; auto.
      rewrite vec_map_map; f_equal.
      apply vec_pos_ext; intros p; rew vec.
    Qed.

  End fo_term_subst_comp.

End first_order_terms.

Notation fol_term := (fun Σ => fo_term (ar_syms Σ)).

Arguments in_var { _ _ }.
Arguments in_fot { _ _ }.

Create HintDb fo_term_db.
Tactic Notation "rew" "fot" := autorewrite with fo_term_db.

Hint Rewrite fo_term_vars_fix_0   fo_term_vars_fix_1 
             fo_term_syms_fix_0   fo_term_syms_fix_1 
             fo_term_subst_fix_0  fo_term_subst_fix_1 
             fo_term_subst_comp 
           : fo_term_db.

Notation "t ⟬ σ ⟭" := (fo_term_subst σ t).

Section fo_term_extra.

  Variable (Σ : fo_signature).

  Notation 𝕋 := (fol_term Σ).

  Implicit Type t : 𝕋.

  Section map.

    Variable (f : nat -> nat).

    Fixpoint fo_term_map t := 
      match t with
        | in_var x   => in_var (f x)
        | in_fot s v => in_fot s (vec_map fo_term_map v)
      end.

    Fact fo_term_map_fix_0 x : fo_term_map (in_var x) = in_var (f x).
    Proof. trivial. Qed.

    Fact fo_term_map_fix_1 s v : 
         fo_term_map (in_fot s v) = in_fot s (vec_map fo_term_map v).
    Proof. trivial. Qed.

  End map.

  Opaque fo_term_map.

  Hint Rewrite fo_term_map_fix_0 fo_term_map_fix_1 : fo_term_db.

  Fact fo_term_subst_map f t : t⟬fun x => in_var (f x)⟭ = fo_term_map f t.
  Proof. 
    induction t; rew fot; f_equal.
    apply vec_pos_ext; intro; rew vec. 
  Qed.

  Fact fo_term_map_ext f g t : 
           (forall x, In x (fo_term_vars t) -> f x = g x)
        -> fo_term_map f t = fo_term_map g t.
  Proof.
    intros Hfg. 
    do 2 rewrite <- fo_term_subst_map.
    apply fo_term_subst_ext.
    intros; f_equal; auto.
  Qed.

  Fact fo_term_vars_subst f t : 
         fo_term_vars (t⟬f⟭) = flat_map (fun n => fo_term_vars (f n)) (fo_term_vars t).
  Proof.
    induction t as [ n | s v IHv ]; rew fot; auto.
    + simpl; rewrite <- app_nil_end; auto.
    + rewrite vec_list_vec_map.
      rewrite flat_map_flat_map.
      rewrite flat_map_concat_map, map_map, <- flat_map_concat_map.
      do 2 rewrite flat_map_concat_map; f_equal.
      apply map_ext_in; intros x Hx.
      apply vec_list_inv in Hx.
      destruct Hx as (p & ->).
      rewrite IHv; auto.
  Qed.

  Fact fo_term_vars_map f t : fo_term_vars (fo_term_map f t) = map f (fo_term_vars t).
  Proof.
    rewrite <- fo_term_subst_map, fo_term_vars_subst.
    generalize (fo_term_vars t); clear t.
    induction l; simpl; f_equal; auto.
  Qed.

  Fact fo_term_syms_map f t : fo_term_syms (fo_term_map f t) = fo_term_syms t.
  Proof.
    induction t as [ n | s v IHv ]; rew fot; auto; f_equal.
    do 2 rewrite flat_map_concat_map; f_equal.
    rewrite vec_list_vec_map, map_map.
    apply map_ext_in.
    intros x Hx; apply vec_list_inv in Hx.
    destruct Hx as (p & ->); apply IHv.
  Qed.

  (** The identity is going to be complicated only permutation will do
      the syms in the substitution are those in the original term + all
      those occuring in the substitution on the variables in t 

      We show the weaker  *)

  Fact fo_term_syms_subst P f t : 
        (forall n, In n (fo_term_vars t) -> Forall P (fo_term_syms (f n)))  
     -> Forall P (fo_term_syms t) -> Forall P (fo_term_syms (t⟬f⟭)).
  Proof.
    induction t as [ n | s v IH ]; intros H1 H2; rew fot.
    + apply H1; simpl; auto.
    + constructor.
      * rewrite Forall_forall in H2; apply H2; rew fot; left; auto.
      * rewrite Forall_forall; intros x; rewrite in_flat_map.
        intros (s' & H3 & H4).
        rewrite vec_list_vec_map, in_map_iff in H3.
        destruct H3 as (t & <- & H3).
        apply vec_list_inv in H3.
        destruct H3 as (p & ->).
        revert x H4; apply Forall_forall, IH; auto.
        - intros; apply H1; rew fot; apply in_flat_map.
          exists (vec_pos v p); split; auto. 
          apply in_vec_list, in_vec_pos.
        - revert H2; do 2 rewrite Forall_forall.
          intros H2 x Hx; apply H2; rew fot.
          right; apply in_flat_map.
          exists (vec_pos v p); split; auto.
          apply in_vec_list, in_vec_pos.
  Qed.

End fo_term_extra.

Arguments fo_term_vars {_ _}.
Arguments fo_term_syms {_ _}.

Opaque fo_term_map.

Hint Rewrite fo_term_map_fix_0 fo_term_map_fix_1 
           : fo_term_db.

Definition fo_term_subst_lift Σ (σ : nat -> fol_term Σ) n :=
  match n with 
    | 0   => in_var 0
    | S n => fo_term_map S (fo_term_subst σ (in_var n))
  end.

Arguments fo_term_subst_lift {Σ} σ n /.

Notation "⇡ σ" := (fo_term_subst_lift σ).

Section semantics.

  Variable (Σ : fo_signature) 
           (X : Type) (M : fo_model Σ X).

  Notation 𝕋 := (fol_term Σ).

  Implicit Type φ : nat -> X.

  Fixpoint fo_term_sem φ (t : 𝕋) :=
    match t with
      | in_var x   => φ x
      | in_fot s v => fom_syms M s (vec_map (fo_term_sem φ) v)
    end.

  Notation "⟦ t ⟧" := (fun φ => @fo_term_sem φ t).

  Fact fo_term_sem_fix_0 φ n : ⟦in_var n⟧ φ = φ n.
  Proof. trivial. Qed.

  Fact fo_term_sem_fix_1 φ s v : ⟦in_fot s v⟧ φ = fom_syms M s (vec_map (fun t => ⟦t⟧ φ) v).
  Proof. trivial. Qed.

  Opaque fo_term_sem.

  Hint Rewrite fo_term_sem_fix_0 fo_term_sem_fix_1 : fo_term_db.

  Fact fo_term_sem_ext t φ ψ : 
        (forall n, In n (fo_term_vars t) -> φ n = ψ n) -> ⟦t⟧ φ = ⟦t⟧ ψ.
  Proof.
    induction t as [ n | s v IHv ] in φ, ψ |- *; intros H; rew fot.
    + apply H; simpl; auto.
    + f_equal; apply vec_map_ext.
      intros x Hx.
      apply in_vec_list, vec_list_inv in Hx.
      destruct Hx as (p & ->).
      apply IHv; auto.
      intros n Hn; apply H; rew fot.
      apply in_flat_map; exists (vec_pos v p); split; auto.
      apply in_vec_list; auto.
  Qed.

  Fact fo_term_sem_subst φ σ t : ⟦t⟬σ⟭⟧ φ = ⟦t⟧ (fun n => ⟦σ n⟧ φ).
  Proof.
    induction t; rew fot; f_equal; auto.
    apply vec_pos_ext; intros; rew vec.
  Qed.

End semantics.

Opaque fo_term_sem.

Hint Rewrite fo_term_sem_fix_0 fo_term_sem_fix_1 fo_term_sem_subst : fo_term_db.
