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

From Undecidability.Shared.Libs.DLW.Wf
  Require Import acc_irr.

From Undecidability.Shared.Libs.DLW.Vec 
  Require Import pos vec.

From Undecidability.TRAKHTENBROT
  Require Import notations fol_ops utils.

Set Implicit Arguments.

(** Then first order terms with signature *)

Local Hint Resolve in_vec_list in_vec_pos.

Section first_order_terms.

  Variable (var sym : Type)        (* a type of variables and symbols *)
           (sym_ar : sym -> nat).  (* arities for symbols *)

  Unset Elimination Schemes.       (* we do not want the autogen recursors *)

  (** The Type of first order terms over signature s *)

  Inductive fo_term : Type :=
    | in_var : var -> fo_term
    | in_fot : forall s, vec fo_term (sym_ar s) -> fo_term.

  Set Elimination Schemes.

  Section fo_term_rect.

    (** We build a Type level dependent recursor together with
        a fixpoint equation *)

    Let sub_fo_term x t := 
      match t with 
        | in_var _    => False 
        | @in_fot s v => in_vec x v 
      end.  

    (** This proof has to be carefully crafted for guardness *)
 
    Let Fixpoint Acc_sub_fo_term t : Acc sub_fo_term t.
    Proof.
      destruct t as [ x | s v ]; constructor 1; simpl.
      + intros _ [].
      + intros x.
        revert v; generalize (sym_ar s).
        induction v as [ | n y w IHw ].
        * destruct 1.
        * intros [ H | H ].
          - rewrite <- H; apply Acc_sub_fo_term.
          - apply IHw, H.
    Qed.

    (** This is a Type level (_rect) dependent recursor with induction
        hypothesis using Prop level in_vec *) 

    Variable (P   : fo_term -> Type)
             (HP0 : forall x, P (in_var x))
             (IHP : forall s v, (forall t, in_vec t v -> P t) -> P (@in_fot s v)).

    Let Fixpoint Fix_IHP t (Ht : Acc sub_fo_term t) { struct Ht } : P t :=
      match t as t' return Acc sub_fo_term t'-> P t' with
        | in_var x    => fun _  => HP0 x
        | @in_fot s v => fun Ht => @IHP s v (fun x Hx => @Fix_IHP x (Acc_inv Ht _ Hx))
      end Ht.

    Let Fix_IHP_fix t Ht :
        @Fix_IHP t Ht 
      = match t as t' return Acc sub_fo_term t' -> _ with 
          | in_var x    => fun _   => HP0 x
          | @in_fot s v => fun Ht' => @IHP s v (fun y H => Fix_IHP (Acc_inv Ht' H)) 
        end Ht.
    Proof. destruct Ht; reflexivity. Qed.

    Definition fo_term_rect' t : P t.
    Proof. apply Fix_IHP with (1 := Acc_sub_fo_term t). Defined.

    Hypothesis IHP_ext : forall s v f g, (forall y H, f y H = g y H) -> @IHP s v f = IHP v g.

    Let Fix_IHP_Acc_irr : forall t f g, @Fix_IHP t f = Fix_IHP g.
    Proof.
      apply Acc_irrelevance.
      intros [] f g H; auto; apply IHP_ext; auto.
    Qed.

    Theorem fo_term_rect_fix' s v : 
            fo_term_rect' (@in_fot s v) = @IHP s v (fun t _ => fo_term_rect' t).
    Proof.
      unfold fo_term_rect' at 1.
      rewrite Fix_IHP_fix.
      apply IHP_ext.
      intros; apply Fix_IHP_Acc_irr.
    Qed.

  End fo_term_rect.

  Definition fo_term_rec' (P : _ -> Set) := @fo_term_rect' P.
  Definition fo_term_ind' (P : _ -> Prop) := @fo_term_rect' P.

  Section fo_term_pos_rect.

    (** This one is nicer to compute *)
   
    Variable (P   : fo_term -> Type)
             (HP0 : forall x, P (in_var x))
             (IHP : forall s v, (forall p, P (vec_pos v p)) -> P (@in_fot s v)).

    Fixpoint fo_term_pos_rect t : P t :=
      match t with
        | in_var x => HP0 x 
        | in_fot v => IHP v (fun p => fo_term_pos_rect (vec_pos v p))
      end.

  End fo_term_pos_rect.

  Definition fo_term_rect (P : _ -> Type) := @fo_term_pos_rect P.
  Definition fo_term_rec (P : _ -> Set) := @fo_term_rect P.
  Definition fo_term_ind (P : _ -> Prop) := @fo_term_rect P.
 
  Section fo_term_recursion.

    (** We specialize the nice recursor to fixed output type.
        The fixpoint equation are better behaved *)

    Variable (X : Type)
             (F0 : var -> X)
             (F  : forall s, vec fo_term (sym_ar s) -> vec X (sym_ar s) -> X).

    Definition fo_term_recursion : fo_term -> X.
    Proof.
      induction 1 as [ x | s v IHv ].
      + exact (F0 x).
      + apply (@F s v), vec_set_pos, IHv.
    Defined.

    Theorem fo_term_recursion_fix_0 x :
      fo_term_recursion (in_var x) = F0 x.
    Proof. reflexivity. Qed.

    Theorem fo_term_recursion_fix_1 s v :
      fo_term_recursion (@in_fot s v) = F v (vec_map fo_term_recursion v).
    Proof.
      unfold fo_term_recursion at 1.
      simpl; f_equal; apply vec_pos_ext; intro; rew vec.
    Qed.

  End fo_term_recursion.

  (** We can now define eg the size of terms easily with the
      corresponding fixpoint equation *)

  Fixpoint fo_term_size c t :=
    match t with
      | in_var _    => 1
      | @in_fot s v => c s + vec_sum (vec_map (fo_term_size c) v)
    end.

  Fact fo_term_size_fix_0 c x : fo_term_size c (in_var x) = 1.
  Proof. trivial. Qed.
  
  Fact fo_term_size_fix_1 c s v :
         fo_term_size c (@in_fot s v) = c s + vec_sum (vec_map (fo_term_size c) v).
  Proof. trivial. Qed.

  (*

  Definition fo_term_size' (c : sym -> nat) : fo_term -> nat.
  Proof.
    induction 1 as [ _ | s _ w ] using fo_term_recursion.
    + exact 1.
    + exact (c s+vec_sum w).
  Defined.

  Fact fo_term_size_fix_0' c x : fo_term_size' c (in_var x) = 1.
  Proof. apply fo_term_recursion_fix_0. Qed.
  
  Fact fo_term_size_fix_1' c s v :
         fo_term_size' c (@in_fot s v) = c s + vec_sum (vec_map (fo_term_size' c) v).
  Proof. apply fo_term_recursion_fix_1. Qed.

  *)

  Fixpoint fo_term_vars t :=
    match t with 
      | in_var x    => x::nil
      | @in_fot s v => concat (vec_list (vec_map fo_term_vars v))
    end.

  Fact fo_term_vars_fix_0 x : fo_term_vars (in_var x) = x :: nil.
  Proof. trivial. Qed.

  Fact fo_term_vars_fix_1 s v : fo_term_vars (@in_fot s v) = flat_map fo_term_vars (vec_list v).
  Proof. simpl; rewrite vec_list_vec_map, <- flat_map_concat_map; auto. Qed.

  (*

  Definition fo_term_vars : fo_term -> list var.
  Proof.
    induction 1 as [ x | s _ w ] using fo_term_recursion.
    + exact (x::nil).
    + exact (concat (vec_list w)).
  Defined.

  Fact fo_term_vars_fix_0 x : fo_term_vars (in_var x) = x :: nil.
  Proof. apply fo_term_recursion_fix_0. Qed.

  Fact fo_term_vars_fix_2 s v : fo_term_vars (@in_fot s v) = concat (vec_list (vec_map fo_term_vars v)).
  Proof. apply fo_term_recursion_fix_1. Qed.

  Fact fo_term_vars_fix_1 s v : fo_term_vars (@in_fot s v) = flat_map fo_term_vars (vec_list v).
  Proof. rewrite fo_term_vars_fix_2, vec_list_vec_map, <- flat_map_concat_map; auto. Qed.

  *)

  Fixpoint fo_term_syms t :=
    match t with 
      | in_var x    => nil
      | @in_fot s v => s::concat (vec_list (vec_map fo_term_syms v))
    end.

  Fact fo_term_syms_fix_0 x : fo_term_syms (in_var x) = nil.
  Proof. trivial. Qed.

  Fact fo_term_syms_fix_1 s v : fo_term_syms (@in_fot s v) = s::flat_map fo_term_syms (vec_list v).
  Proof. simpl; rewrite vec_list_vec_map, <- flat_map_concat_map; auto. Qed.

   (*

  Definition fo_term_syms : fo_term -> list sym.
  Proof.
    induction 1 as [ x | s _ w ] using fo_term_recursion.
    + exact nil.
    + exact (s::concat (vec_list w)).
  Defined.

  Fact fo_term_syms_fix_0 x : fo_term_syms (in_var x) = nil.
  Proof. apply fo_term_recursion_fix_0. Qed.

  Fact fo_term_syms_fix_2 s v : fo_term_syms (@in_fot s v) = s::concat (vec_list (vec_map fo_term_syms v)).
  Proof. apply fo_term_recursion_fix_1. Qed.

  Fact fo_term_syms_fix_1 s v : fo_term_syms (@in_fot s v) = s::flat_map fo_term_syms (vec_list v).
  Proof. rewrite fo_term_syms_fix_2, vec_list_vec_map, <- flat_map_concat_map; auto. Qed.

  *)

End first_order_terms.

Arguments in_var { var sym sym_ar }.

Create HintDb fo_term_db.
Tactic Notation "rew" "fot" := autorewrite with fo_term_db.

Hint Rewrite fo_term_vars_fix_0 fo_term_vars_fix_1 
             fo_term_syms_fix_0 fo_term_syms_fix_1 : fo_term_db.

Section fo_term_subst.

  Variable (sym : Type) (sym_ar : sym -> nat)
           (X Y : Type).

  Implicit Type (σ : X -> fo_term Y sym_ar).

  Fixpoint fo_term_subst σ (t : fo_term X sym_ar) :=
    match t with 
      | in_var x   => σ x
      | in_fot s v => in_fot s (vec_map (fo_term_subst σ) v)
    end.

  Notation "t ⟬ σ ⟭" := (fo_term_subst σ t).

  Fact fo_term_subst_fix_0 σ x : (in_var x)⟬σ⟭  = σ x.
  Proof. trivial. Qed.

  Fact fo_term_subst_fix_1 σ s v : (in_fot s v)⟬σ⟭ 
                                  = in_fot s (vec_map (fo_term_subst σ) v).
  Proof. trivial. Qed.

  (*

  Definition fo_term_subst σ : fo_term X sym_ar -> fo_term Y sym_ar.
  Proof.
    induction 1 as [ x | s _ w ] using fo_term_recursion.
    + apply σ, x.
    + exact (in_fot s w).
  Defined.

  Notation "t ⟬ σ ⟭" := (fo_term_subst σ t).

  Fact fo_term_subst_fix_0 σ x : (in_var x)⟬σ⟭  = σ x.
  Proof. apply fo_term_recursion_fix_0. Qed.

  Fact fo_term_subst_fix_1 σ s v : (in_fot s v)⟬σ⟭ 
                                  = in_fot s (vec_map (fo_term_subst σ) v).
  Proof. apply fo_term_recursion_fix_1. Qed.

  *)

  Opaque fo_term_subst.

  Hint Rewrite fo_term_subst_fix_0 fo_term_subst_fix_1 : fo_term_db.

  Fact fo_term_subst_ext f g t : 
     (forall x, In x (fo_term_vars t) -> f x = g x) -> t⟬f⟭ = t⟬g⟭.
  Proof.
    induction t as [ | s v IHv ]; intros Hfg; rew fot.
    + apply Hfg; rew fot; simpl; auto.
    + simpl; f_equal; apply vec_map_ext.
      intros x Hx. 
      apply in_vec_list, vec_list_inv in Hx.
      destruct Hx as (p & ->).
      apply IHv.
      intros y Hy; apply Hfg; rew fot. 
      apply in_flat_map; exists (vec_pos v p).
      split; auto; apply in_vec_list; auto.
  Qed.

  Section map.

    Variable (f : X -> Y).

    Fixpoint fo_term_map (t : fo_term X sym_ar) := 
      match t with
        | in_var x   => in_var (f x)
        | in_fot s v => in_fot s (vec_map fo_term_map v)
      end.

    Fact fo_term_map_fix_0 x : fo_term_map (in_var x) = in_var (f x).
    Proof. trivial. Qed.

    Fact fo_term_map_fix_1 s v : 
         fo_term_map (in_fot s v) = in_fot s (vec_map fo_term_map v).
    Proof. trivial. Qed.

    (*

    Definition fo_term_map : fo_term X sym_ar -> fo_term Y sym_ar.
    Proof.
      induction 1 as [ x | s _ w ] using fo_term_recursion.
      + exact (in_var (f x)).
      + exact (in_fot s w).
    Defined.

    Fact fo_term_map_fix_0 x : fo_term_map (in_var x) = in_var (f x).
    Proof. apply fo_term_recursion_fix_0. Qed.

    Fact fo_term_map_fix_1 s v : 
         fo_term_map (in_fot s v) = in_fot s (vec_map fo_term_map v).
    Proof. apply fo_term_recursion_fix_1. Qed.

    *)

  End map.

  Opaque fo_term_map.

  Hint Rewrite fo_term_map_fix_0 fo_term_map_fix_1 : fo_term_db.

  Fact fo_term_subst_map f t : t⟬fun x => in_var (f x)⟭ = fo_term_map f t.
  Proof. 
    induction t; rew fot; f_equal.
    apply vec_pos_ext; intro; rew vec. 
  Qed.

  Fact fo_term_map_ext f g t : (forall x, In x (fo_term_vars t) -> f x = g x)
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

End fo_term_subst.

Opaque fo_term_map fo_term_subst.

Hint Rewrite fo_term_subst_fix_0 fo_term_subst_fix_1
             fo_term_map_fix_0 fo_term_map_fix_1 : fo_term_db.

Notation "t ⟬ σ ⟭" := (fo_term_subst σ t).

Section fo_term_subst_comp.

  Variables (sym : Type) (sym_ar : sym -> nat) (X Y Z : Type) 
            (f : X -> fo_term Y sym_ar) 
            (g : Y -> fo_term Z sym_ar).

  Fact fo_term_subst_comp t : t⟬f⟭ ⟬g⟭ = t⟬fun x => (f x)⟬g⟭ ⟭ . 
  Proof.
    induction t; rew fot; auto; rew fot.
    rewrite vec_map_map; f_equal.
    apply vec_pos_ext; intros p; rew vec.
  Qed.

End fo_term_subst_comp.

Hint Rewrite fo_term_subst_comp : fo_term_db.

Definition fo_term_subst_lift s ar (σ : nat -> @fo_term nat s ar) n :=
  match n with 
    | 0   => in_var 0
    | S n => fo_term_map S (fo_term_subst σ (in_var n))
  end.

Arguments fo_term_subst_lift {s ar } σ n /.

Notation "⇡ σ" := (fo_term_subst_lift σ).

Section semantics.

  Variable (sym : Type) (sym_ar : sym -> nat) (X : Type)
           (M : Type) (sem_sym : forall s, vec M (sym_ar s) -> M).

  Notation 𝕋 := (fo_term X sym_ar).

  Implicit Type φ : X -> M.

  Fixpoint fo_term_sem φ (t : 𝕋) :=
    match t with
      | in_var x   => φ x
      | in_fot s v => sem_sym (vec_map (fo_term_sem φ) v)
    end.

  Notation "⟦ t ⟧" := (fun φ => @fo_term_sem φ t).

  Fact fo_term_sem_fix_0 φ n : ⟦in_var n⟧ φ = φ n.
  Proof. trivial. Qed.

  Fact fo_term_sem_fix_1 φ s v : ⟦in_fot s v⟧ φ = sem_sym (vec_map (fun t => ⟦t⟧ φ) v).
  Proof. trivial. Qed.

  (*

  Definition fo_term_sem φ : 𝕋 -> M.
  Proof.
    induction 1 as [ x | s _ w ] using fo_term_recursion.
    + exact (φ x).
    + exact (sem_sym w).
  Defined.

  Notation "⟦ t ⟧" := (fun φ => @fo_term_sem φ t).

  Fact fo_term_sem_fix_0 φ n : ⟦in_var n⟧ φ = φ n.
  Proof. apply fo_term_recursion_fix_0. Qed.

  Fact fo_term_sem_fix_1 φ s v : ⟦in_fot s v⟧ φ = sem_sym (vec_map (fun t => ⟦t⟧ φ) v).
  Proof. apply fo_term_recursion_fix_1. Qed.

  *)

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

Section rel_semantics.

  Variable (sym : Type) (sym_ar : sym -> nat) (X : Type)
           (M : Type) (sem_sym : forall s, vec M (sym_ar s) -> M -> Prop).

  Notation 𝕋 := (fo_term X sym_ar).

  Implicit Type φ : X -> M -> Prop.

  Fixpoint fo_term_rsem φ (t : 𝕋) : M -> Prop :=
    match t with
      | in_var x   => φ x
      | in_fot s v => fun m => exists w, @sem_sym s w m /\ forall p, fo_term_rsem φ (vec_pos v p) (vec_pos w p)
    end.

  Notation "⟦ t ⟧" := (fun φ => @fo_term_rsem φ t).

  Fact fo_term_rsem_fix_0 φ n : ⟦in_var n⟧ φ = φ n.
  Proof. trivial. Qed.

  Fact fo_term_rsem_fix_1 φ s v r : 
           ⟦in_fot s v⟧ φ r 
       <-> exists w, @sem_sym s w r 
                  /\ forall p, ⟦vec_pos v p⟧ φ (vec_pos w p).
  Proof. simpl; tauto. Qed.

  (*

  Definition fo_term_rsem φ : 𝕋 -> M -> Prop.
  Proof.
    induction 1 as [ x | s _ w ] using fo_term_recursion.
    + exact (φ x).
    + intros r.
      exact (exists v, @sem_sym s v r /\ forall p, vec_pos w p (vec_pos v p)). 
  Defined.

  Notation "⟦ t ⟧" := (fun φ => @fo_term_rsem φ t).

  Fact fo_term_rsem_fix_0 φ n : ⟦in_var n⟧ φ = φ n.
  Proof. apply fo_term_recursion_fix_0. Qed.

  Fact fo_term_rsem_fix_1 φ s v r : 
           ⟦in_fot s v⟧ φ r 
       <-> exists w, @sem_sym s w r 
                  /\ forall p, ⟦vec_pos v p⟧ φ (vec_pos w p).
  Proof.
    unfold fo_term_rsem at 1; rewrite fo_term_recursion_fix_1.
    apply exists_equiv; intros w.
    apply fol_bin_sem_ext with (b := fol_conj); try tauto.
    apply forall_equiv; intros p.
    rewrite vec_pos_map.
    apply fol_equiv_ext; auto.
  Qed.

  *)

  Opaque fo_term_rsem.

  Hint Rewrite fo_term_rsem_fix_0 fo_term_rsem_fix_1 : fo_term_db.

  Fact fo_term_rsem_ext t φ ψ : 
        (forall n r, In n (fo_term_vars t) -> φ n r <-> ψ n r) -> forall r, ⟦t⟧ φ r <-> ⟦t⟧ ψ r.
  Proof.
    induction t as [ n | s v IHv ] in φ, ψ |- *; intros H; rew fot.
    + intro; apply H; simpl; auto.
    + intros r; rew fot.
      apply exists_equiv; intros w.
      apply fol_bin_sem_ext with (b := fol_conj); try tauto.
      apply forall_equiv; intros p.
      apply IHv.
      intros; apply H; rew fot.
      apply in_flat_map.
      exists (vec_pos v p); split; auto.
      apply in_vec_list; auto.
  Qed.

End rel_semantics.

Opaque fo_term_rsem.

Hint Rewrite fo_term_rsem_fix_0 fo_term_rsem_fix_1 : fo_term_db.

Section equiv.

  Variable (sym : Type) (sym_ar : sym -> nat) (X : Type)
           (M : Type) (sM : forall s, vec M (sym_ar s) -> M).

  Theorem fo_term_sem_rsem_equiv (t : fo_term X sym_ar) φ r : 
           r = fo_term_sem sM φ t <-> fo_term_rsem (fun s v r => r = @sM s v) (fun n r => r = φ n) t r.
  Proof.
    revert φ r; induction t as [ n | s v IHv ]; intros phi r; rew fot; try tauto.
    split.
    + intros ->.
      exists (vec_map (fo_term_sem sM phi) v); split; auto.
      intros p; apply IHv; rew vec.
    + intros (w & -> & Hw); f_equal.
      apply vec_pos_ext; intros p; rew vec.
      apply IHv, Hw.
  Qed.

End equiv.

Section rel_simulation.

  Variable (sym : Type) (sym_ar : sym -> nat) (X : Type)
           (M : Type) (sM : forall s, vec M (sym_ar s) -> M -> Prop)
           (N : Type) (sN : forall s, vec N (sym_ar s) -> N -> Prop).

  Notation 𝕋 := (fo_term X sym_ar).

  Implicit Type (φ : X -> M -> Prop) (ψ : X -> N -> Prop).

  Variable (simul : M -> N -> Prop).

  Infix "⋈" := simul (at level 70, no associativity).
  
  Theorem fo_term_rsem_simul (t : fo_term X sym_ar) φ ψ :
             (forall n x y, In n (fo_term_vars t) -> x ⋈ y -> φ n x <-> ψ n y)
          -> (forall s, In s (fo_term_syms t) -> forall x v y, x ⋈ y -> sM v x -> exists w, @sN s w y 
                                                                                         /\ forall p, vec_pos v p ⋈ vec_pos w p) 
          -> (forall s, In s (fo_term_syms t) -> forall x w y, x ⋈ y -> sN w y -> exists v, @sM s v x 
                                                                                         /\ forall p, vec_pos v p ⋈ vec_pos w p)   
          -> forall x y, x ⋈ y -> fo_term_rsem sM φ t x <-> fo_term_rsem sN ψ t y.
  Proof.
    induction t as [ n | s v IHv ]; intros H1 H2 H2' x y Hxy; rew fot; try tauto.
    + apply H1; simpl; auto.
    + split.
      * intros (v' & H3 & H4).
        destruct H2 with (2 := Hxy) (3 := H3) as (w' & H5 & H6).
        - simpl; auto.
        - exists w'; split; auto.
          intros p. 
          apply (IHv p) with (x := vec_pos v' p); auto.
          ++ intros ? ? ? ?; apply H1; rew fot. 
             apply in_flat_map; exists (vec_pos v p); split; auto.
             apply in_vec_list, in_vec_pos.
          ++ intros ? ? ? ? ?; apply H2; rew fot; auto; simpl; right.
             apply in_flat_map; exists (vec_pos v p); split; auto.
             apply in_vec_list, in_vec_pos.
          ++ intros ? ? ? ? ?; apply H2'; rew fot; auto; simpl; right.
             apply in_flat_map; exists (vec_pos v p); split; auto.
             apply in_vec_list, in_vec_pos.
      * intros (w' & H3 & H4).
        destruct H2' with (2 := Hxy) (3 := H3) as (v' & H5 & H6).
        - simpl; auto.
        - exists v'; split; auto.
          intros p. 
          apply (IHv p) with (y := vec_pos w' p); auto.
          ++ intros ? ? ? ?; apply H1; rew fot. 
             apply in_flat_map; exists (vec_pos v p); split; auto.
             apply in_vec_list, in_vec_pos.
          ++ intros ? ? ? ? ?; apply H2; rew fot; auto; simpl; right.
             apply in_flat_map; exists (vec_pos v p); split; auto.
             apply in_vec_list, in_vec_pos.
          ++ intros ? ? ? ? ?; apply H2'; rew fot; auto; simpl; right.
             apply in_flat_map; exists (vec_pos v p); split; auto.
             apply in_vec_list, in_vec_pos.
  Qed.

End rel_simulation.

Check fo_term_rsem_simul.



