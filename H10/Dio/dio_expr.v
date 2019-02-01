(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import Arith Nat Omega.

Set Implicit Arguments.

Section diophantine_expressions.

  Inductive dio_op := do_add | do_mul.

  Definition do_eval o :=
    match o with
      | do_add => plus
      | do_mul => mult
    end.

  Inductive dio_expr : Set :=
    | de_cst  : nat -> dio_expr
    | de_var  : nat -> dio_expr
    | de_comp : dio_op -> dio_expr -> dio_expr -> dio_expr.

  Definition de_add := de_comp do_add.
  Definition de_mul := de_comp do_mul.

  Fixpoint de_size e :=
    match e with
      | de_cst n => 1
      | de_var x => 1
      | de_comp _ p q => 1 + de_size p + de_size q
    end.

  Fixpoint de_size_Z e :=
    (match e with
      | de_cst n => 1
      | de_var x => 1
      | de_comp _ p q => 1 + de_size_Z p + de_size_Z q
    end)%Z.

  Fact de_size_Z_spec e : de_size_Z e = Z.of_nat (de_size e).
  Proof.
    induction e as [ | | o f Hf g Hg ]; auto.
    simpl de_size; unfold de_size_Z; fold de_size_Z.
    rewrite Nat2Z.inj_succ, Nat2Z.inj_add; omega.
  Qed.

  Fixpoint de_eval ν e  :=
    match e with
      | de_cst n => n
      | de_var x => ν x
      | de_comp o p q => do_eval o (de_eval ν p) (de_eval ν q)
    end.

  Fact de_eval_ext e ν ω : (forall x, ν x = ω x) -> de_eval ν e = de_eval ω e.
  Proof.
    intros H; induction e as [ | | [] ]; simpl; auto.
  Qed.

  (* ρ σ ν *)

  Fixpoint de_subst σ e :=
    match e with
      | de_cst n => de_cst n
      | de_var x => σ x
      | de_comp o p q => de_comp o (de_subst σ p) (de_subst σ q)
    end.

  Fact de_eval_subst σ ν e : de_eval ν (de_subst σ e) = de_eval (fun x => de_eval ν (σ x)) e.
  Proof. induction e as [ | | [] ]; simpl; auto. Qed.

  Fact de_subst_subst σ1 σ2 e : de_subst σ1 (de_subst σ2 e) = de_subst (fun x => de_subst σ1 (σ2 x)) e.
  Proof. induction e as [ | | [] ]; simpl; f_equal; auto. Qed.

  Definition de_ren ρ := de_subst (fun x => de_var (ρ x)).

  Fact de_ren_size ρ e : de_size (de_ren ρ e) = de_size e.
  Proof.
    revert ρ; induction e as [ | | o e He f Hf ]; intros rho; auto.
    unfold de_ren; simpl de_subst; unfold de_size; fold de_size. 
    f_equal; [ f_equal | ].
    * apply He.
    * apply Hf.
  Qed.

  Fact de_ren_size_Z ρ e : de_size_Z (de_ren ρ e) = de_size_Z e.
  Proof. do 2 rewrite de_size_Z_spec; f_equal; apply de_ren_size. Qed.

  Fact de_eval_ren ρ ν e : de_eval ν (de_ren ρ e)  = de_eval (fun x => ν (ρ x)) e.
  Proof. apply de_eval_subst. Qed.

  Definition de_lift := de_ren S.

  Fact de_eval_lift ν e : de_eval ν (de_lift e) = de_eval (fun x => ν (S x)) e.
  Proof. apply de_eval_ren. Qed.

End diophantine_expressions.

