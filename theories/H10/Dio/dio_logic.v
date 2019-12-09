(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

(** * Object-level representation of Diophantine equations *)
(** ** Diophantine logic *)

Require Import Arith Nat Omega.
From Undecidability.Shared.Libs.DLW.Utils Require Import gcd.

Set Implicit Arguments.

Fixpoint env_lift {X} (φ : nat -> X) k n { struct n } :=
  match n with
    | 0   => k
    | S n => φ n
  end.

Notation "phi ↑ k" := (env_lift phi k) (at level 1, format "phi ↑ k", left associativity).
Notation "phi ↓"   := (fun n => phi (S n)) (at level 1, format "phi ↓", no associativity).

Inductive dio_op := do_add | do_mul.

Definition de_op_sem (o : dio_op) :=
  match o with
    | do_add => plus
    | do_mul => mult
  end.

Definition df_op_sem (o : dio_op) :=
  match o with
    | do_add => or
    | do_mul => and
  end.

(** De Bruin syntax for diophantine formulas of the form

         A,B ::= x = n | x = y o z | A /\ B | A \/ B | ∃x.A with o in {+,*}     
*)

Inductive dio_formula : Set :=
  | df_cst  : forall (x : nat) (n : nat), dio_formula
  | df_op   : forall (o : dio_op) (x y z : nat), dio_formula 
  | df_bin  : forall (o : dio_op) (_ _ : dio_formula), dio_formula
  | df_exst : dio_formula -> dio_formula.

Notation df_add := (df_op do_add).
Notation df_mul := (df_op do_mul).
Notation df_conj := (df_bin do_mul).
Notation df_disj := (df_bin do_add).

Section diophantine_logic.

  Fixpoint df_size f :=
    match f with
      | df_cst _ _    => 3
      | df_op _ _ _ _ => 5
      | df_bin _ f g  => 1 + df_size f + df_size g   
      | df_exst f     => 1 + df_size f
    end.

  Fixpoint df_size_Z f :=
    (match f with
      | df_cst _ _    => 3
      | df_op _ _ _ _ => 5
      | df_bin _ f g  => 1 + df_size_Z f + df_size_Z g   
      | df_exst f     => 1 + df_size_Z f
    end)%Z.

  Fact df_size_Z_spec f : df_size_Z f = Z.of_nat (df_size f).
  Proof.
    induction f as [ | | ? f Hf g Hg | f Hf ]; simpl df_size;
      rewrite Nat2Z.inj_succ; try rewrite Nat2Z.inj_add; unfold df_size_Z; fold df_size_Z; auto; try omega.
  Qed.

  (* dv_lift : lifting of a diophantive valuation *)

  Definition dv_lift X ν (x : X) n :=
     match n with 
       | 0   => x 
       | S n => ν n 
     end.

  Reserved Notation "'⟦' t '⟧'" (at level 1, format "⟦ t ⟧").

  Fixpoint df_pred f ν :=
    match f with
      | df_cst x n     => ν x = n
      | df_op  o x y z => ν x = de_op_sem o (ν y) (ν z)
      | df_bin o f g   => df_op_sem o (⟦f⟧ ν) (⟦g⟧ ν)
      | df_exst f      => exists n, ⟦f⟧ ν↑n
    end
  where "⟦ f ⟧" := (df_pred f).

  Fact df_pred_cst x n ν : ⟦df_cst x n⟧ ν = (ν x = n).
  Proof. reflexivity. Qed.

  Fact df_pred_add x y z ν : ⟦df_add x y z⟧ ν = (ν x = ν y + ν z).
  Proof. reflexivity. Qed.

  Fact df_pred_mul x y z ν : ⟦df_mul x y z⟧ ν = (ν x = ν y * ν z).
  Proof. reflexivity. Qed.
  
  Fact df_pred_conj f g ν : ⟦df_conj f g⟧ ν = (⟦f⟧ ν /\ ⟦g⟧ ν).
  Proof. reflexivity. Qed.

  Fact df_pred_disj f g ν : ⟦df_disj f g⟧ ν = (⟦f⟧ ν \/ ⟦g⟧ ν).
  Proof. reflexivity. Qed.

  Fact df_pred_exst f ν : ⟦df_exst f⟧ ν = exists n, ⟦f⟧ ν↑n.
  Proof. reflexivity. Qed.

  Fact df_pred_ext f ν ω : (forall x, ν x = ω x) -> ⟦f⟧ ν <-> ⟦f⟧ ω.
  Proof.
    revert ν ω; induction f as [ | [] | [] f Hf g Hg | f Hf ]; intros ν ω H; simpl.
    1-3: rewrite !H; tauto.
    1-2: rewrite Hf, Hg; auto; tauto.
    split; intros (n & Hn); exists n; revert Hn; apply Hf;
        intros []; simpl; auto.
  Qed.

  (* Lifting of a diophantine expression renaming *)

  Definition der_lift ρ x := match x with 0 => 0 | S x => S (ρ x) end.

  Fixpoint df_ren ρ f :=
    match f with
      | df_cst x n    => df_cst (ρ x) n
      | df_op o x y z => df_op o (ρ x) (ρ y) (ρ z)
      | df_bin o f g  => df_bin o (df_ren ρ f) (df_ren ρ g)
      | df_exst f     => df_exst (df_ren (der_lift ρ) f)
    end.

  Fact df_ren_size ρ f : df_size (df_ren ρ f) = df_size f.
  Proof.
    revert ρ; induction f; intros; simpl; auto; do 2 f_equal; auto.
  Qed.

  Fact df_ren_size_Z ρ f : df_size_Z (df_ren ρ f) = df_size_Z f.
  Proof.
    do 2 rewrite df_size_Z_spec; f_equal; apply df_ren_size.
  Qed.

  Fact df_pred_ren f ν ρ : df_pred (df_ren ρ f) ν <-> df_pred f (fun x => ν (ρ x)).
  Proof.
    revert ν ρ; induction f as [ | [] | [] f Hf g Hg | f Hf ]; intros ν ρ; simpl; try tauto.
    1-2: rewrite Hf, Hg; tauto.
    split; intros (n & Hn); exists n; revert Hn; rewrite Hf;
        apply df_pred_ext; intros []; simpl; auto.
  Qed.

  Definition df_lift := df_ren S.

  Fact df_pred_lift f ν : df_pred (df_lift f) ν <-> df_pred f ν↓.
  Proof. apply df_pred_ren. Qed. 

End diophantine_logic.

Definition dio_rel R := { f | forall ν, df_pred f ν <-> R ν }.
Notation 𝔻R := dio_rel.

Section dio_rel.

  (** How to analyse diophantine relations ... these are proved by
      explicitely given the witness which we will avoid later on *)
  
  Implicit Types R S : (nat -> nat) -> Prop.

  Fact dio_rel_cst x n : 𝔻R (fun ν => ν x = n).
  Proof.
    exists (df_cst x n); intro; simpl; tauto.
  Defined.

  Fact dio_rel_add x y z : 𝔻R (fun ν => ν x = ν y + ν z).
  Proof.
    exists (df_add x y z); intro; simpl; tauto.
  Defined.

  Fact dio_rel_mul x y z : 𝔻R (fun ν => ν x = ν y * ν z).
  Proof.
    exists (df_mul x y z); intro; simpl; tauto.
  Defined.
 
  Fact dio_rel_conj R S : 𝔻R R -> 𝔻R S -> 𝔻R (fun ν => R ν /\ S ν).
  Proof.
    intros (fR & H1) (fS & H2).
    exists (df_conj fR fS); intros v.
    rewrite df_pred_conj, H1, H2; tauto.
  Defined.

  Fact dio_rel_disj R S : 𝔻R R -> 𝔻R S -> 𝔻R (fun ν => R ν \/ S ν).
  Proof.
    intros (fR & H1) (fS & H2).
    exists (df_disj fR fS); intros v.
    rewrite df_pred_disj, H1, H2; tauto.
  Defined.

  Fact dio_rel_exst (K : nat -> (nat -> nat) -> Prop) : 
                 𝔻R (fun ν => K (ν 0) ν↓) -> 𝔻R (fun ν => exists x, K x ν).
  Proof.
    intros (f & Hf).
    exists (df_exst f); intros v.
    rewrite df_pred_exst.
    split; intros (n & Hn); exists n; revert Hn; rewrite Hf; simpl; auto.
  Defined.

  Lemma dio_rel_equiv R S : (forall ν, S ν <-> R ν) -> 𝔻R R -> 𝔻R S.
  Proof. 
    intros H (f & Hf); exists f; intro; rewrite Hf, H; tauto.
  Defined.

  Lemma dio_rel_ren R f : 𝔻R R -> 𝔻R (fun ν => R (fun n => ν (f n))).
  Proof.
    intros (r & HR).
    exists (df_ren f r).
    intros; rewrite df_pred_ren, HR; tauto.
  Defined.

End dio_rel.

Create HintDb dio_rel_db.

Hint Resolve dio_rel_cst dio_rel_add dio_rel_mul : dio_rel_db.

Ltac dio_rel_auto := repeat (apply dio_rel_exst 
                           || apply dio_rel_conj 
                           || apply dio_rel_disj); auto with dio_rel_db.

Tactic Notation "by" "dio" "equiv" uconstr(f) :=
  apply dio_rel_equiv with (R := f); [ | dio_rel_auto ].

Fact dio_rel_True : 𝔻R (fun _ => True).
Proof.
  by dio equiv (fun _ => exists x, x = 0).
  split; try tauto; exists 0; auto.
Defined.

Fact dio_rel_False : 𝔻R (fun _ => False).
Proof.
  by dio equiv (fun _ => exists x, x = 1 /\ x = x + x).
  split; try tauto; intros (? & ? & ?); abstract omega.
Defined.

Fact dio_rel_eq_var x y : 𝔻R (fun ν => ν x = ν y).
Proof.
  by dio equiv (fun ν => exists k, k = 0 /\ ν x = ν y + k).
  intros v; split.
  + intros ->; exists 0; auto.
  + intros (? & -> & H); abstract omega.
Qed.

Hint Resolve dio_rel_True dio_rel_False dio_rel_eq_var : dio_rel_db. 

Definition dio_expr t := 𝔻R (fun ν => ν 0 = t ν↓).

Notation 𝔻P := dio_expr.

Fact dio_expr_var i : 𝔻P (fun ν => ν i).
Proof. red; dio_rel_auto. Defined.

Fact dio_expr_cst c : 𝔻P (fun _ => c).
Proof. red; dio_rel_auto. Defined.

Fact dio_rel_eq r t : 𝔻P r -> 𝔻P t -> 𝔻R (fun ν => r ν = t ν).
Proof.
  intros H1 H2; red in H1, H2.
  by dio equiv (fun ν => exists x, x = r ν /\ x = t ν).
  intros v; split.
  + intros ->; exists (t v); auto.
  + intros (? & -> & ?); auto.
Defined.

Fact dio_expr_ren t f : 𝔻P t -> 𝔻P (fun ν => t (fun n => ν (f n))).
Proof. apply dio_rel_ren with (f := der_lift f). Qed.

Hint Resolve dio_expr_var dio_expr_cst dio_rel_eq dio_expr_ren : dio_rel_db.

Fact dio_expr_plus r t : 𝔻P r -> 𝔻P t -> 𝔻P (fun ν => r ν + t ν).
Proof.
  intros H1 H2.
  by dio equiv (fun ν => exists b c, ν 0 = b + c /\ b = r ν↓ /\ c = t ν↓).
  intros v; split.
  + exists (r v↓), (t v↓); auto.
  + intros (? & ? & -> & -> & ->); auto.
Defined.

Fact dio_expr_mult r t : 𝔻P r -> 𝔻P t -> 𝔻P (fun ν => r ν * t ν).
Proof.
  intros H1 H2.
  by dio equiv (fun ν => exists b c, ν 0 = b * c /\ b = r ν↓ /\ c = t ν↓).
  intros v; split.
  + exists (r v↓), (t v↓); auto.
  + intros (? & ? & -> & -> & ->); auto.
Defined.

Hint Resolve dio_expr_plus dio_expr_mult : dio_rel_db.

Fact dio_rel_le r t : 𝔻P r -> 𝔻P t -> 𝔻R (fun ν => r ν <= t ν).
Proof.
  intros H1 H2.
  by dio equiv (fun ν => exists a, t ν = a + r ν).
  intros v; split.
  + intros H; exists (t v - r v); abstract omega.
  + intros (? & ->); abstract omega.
Defined.

Fact dio_rel_lt r t : 𝔻P r -> 𝔻P t -> 𝔻R (fun ν => r ν < t ν).
Proof.
  intros H1 H2.
  by dio equiv (fun ν => exists a, t ν = (1+a) + r ν).
  intros v; split.
  + intros H; exists (t v - S (r v)); abstract omega.
  + intros (? & ->); abstract omega.
Defined.

Hint Resolve dio_rel_le dio_rel_lt : dio_rel_db.

Fact dio_rel_neq r t : 𝔻P r -> 𝔻P t -> 𝔻R (fun ν => r ν <> t ν).
Proof.
  intros.
  by dio equiv (fun ν => r ν < t ν \/ t ν < r ν).
  abstract (intros; omega).
Defined.

Fact dio_rel_div r t : 𝔻P r -> 𝔻P t -> 𝔻R (fun ν => divides (r ν) (t ν)).
Proof.
  intros.
  by dio equiv (fun ν => exists x, t ν = x * r ν).
  intros; unfold divides; tauto.
Defined.

Hint Resolve dio_rel_neq dio_rel_div : dio_rel_db.

Section more_examples.

  Let rem_equiv p x r : r = rem x p <-> (p = 0 /\ x = r)
                                      \/ (p <> 0 /\ r < p /\ exists n, x = n*p + r).
  Proof.
    split.
    + intro; subst.
      destruct (eq_nat_dec p 0) as [ Hp | Hp ].
      * left; split; auto; subst; rewrite rem_0; auto.
      * right; split; auto; split.
        - apply div_rem_spec2; auto.
        - exists (div x p);apply div_rem_spec1.
    + intros [ (H1 & H2) | (H1 & H2 & n & H3) ].
      * subst; rewrite rem_0; auto.
      * symmetry; apply rem_prop with n; auto.
  Qed.
 
  Fact dio_expr_rem p x : 𝔻P p -> 𝔻P x -> 𝔻P (fun ν => rem (x ν) (p ν)).
  Proof.
    intros.
    apply dio_rel_equiv with (1 := fun v => rem_equiv (p v↓) (x v↓) (v 0)).
    dio_rel_auto.
  Defined.
  
  Hint Resolve dio_expr_rem : dio_rel_db.

  Fact dio_rel_remainder p x r : 𝔻P p -> 𝔻P x -> 𝔻P r -> 𝔻R (fun ν => r ν = rem (x ν) (p ν)).
  Proof. intros; dio_rel_auto. Defined.
 
  Hint Resolve dio_rel_remainder : dio_rel_db.

  Fact dio_rel_congruence x y p : 𝔻P x -> 𝔻P y -> 𝔻P p  
                                -> 𝔻R (fun ν => rem (x ν) (p ν) = rem (y ν) (p ν)).
  Proof. intros; dio_rel_auto. Qed.

  Hint Resolve dio_rel_congruence : dio_rel_deb.

  (** The way it is done in the FSCD paper *)

  Let ndivides_eq x y : ~ (divides x y) <-> x = 0 /\ y <> 0 \/ exists a b, y = a*x+b /\ 0 < b < x.
  Proof.
    split.
    + intros H.
      destruct x as [ | x ].
      * left; split; auto; contradict H; subst; apply divides_0.
      * right; exists (div y (S x)), (rem y (S x)); split.
        - apply div_rem_spec1.
        - rewrite divides_rem_eq in H.
          generalize (@div_rem_spec2 y (S x)); intros; omega.
    + intros [ (H1 & H2) | (a & b & H1 & H2) ].
      * subst; contradict H2; revert H2; apply divides_0_inv.
      * rewrite divides_rem_eq.
        rewrite (div_rem_spec1 y x) in H1.
        apply div_rem_uniq in H1; try omega.
        apply div_rem_spec2; omega.
  Qed.
  
  Fact dio_rel_ndivides x y : 𝔻P x -> 𝔻P y -> 𝔻R (fun ν => ~ divides (x ν) (y ν)).
  Proof.
    intros.
    apply dio_rel_equiv with (1 := fun v => ndivides_eq (x v) (y v)).
    dio_rel_auto.
  Defined.

  Hint Resolve dio_rel_ndivides : dio_rel_db.

  (** A shorter way *)

  Let not_divides_eq p x : ~ divides p x <-> exists r, r = rem x p /\ r <> 0.
  Proof.
    rewrite divides_rem_eq.
    split.
    + exists (rem x p); auto.
    + intros (? & ? & ?); subst; auto.
  Qed.

  Lemma dio_rel_not_divides x p : 𝔻P x -> 𝔻P p -> 𝔻R (fun ν => ~ divides (x ν) (p ν)).
  Proof.
    intros.
    apply dio_rel_equiv with (1 := fun v => not_divides_eq (x v) (p v)).
    dio_rel_auto.
  Defined.

End more_examples.

Hint Resolve dio_expr_rem dio_rel_not_divides : dio_rel_deb.

Section dio_rel_compose.

  Variable (f : (nat -> nat) -> nat) (R : nat -> (nat -> nat) -> Prop).
  Hypothesis (Hf : 𝔻R (fun ν => ν 0 = f (fun x => ν (S x)))) 
             (HR : 𝔻R (fun ν => R (ν 0) (fun x => ν (S x)))).

  Lemma dio_rel_compose : 𝔻R (fun ν => R (f ν) ν).
  Proof.
    apply dio_rel_equiv with (R := fun v => exists y, y = f v /\ R y v).
    + intros v; split.
      * exists (f v); auto.
      * intros (? & -> & ?); auto.
    + dio_rel_auto.
  Defined.

End dio_rel_compose.

Section multiple_exists.

  Fixpoint df_mexists n f :=
    match n with 
      | 0   => f
      | S n => df_mexists n (df_exst f)
    end.

  Fact df_mexists_size n f : df_size (df_mexists n f) = n + df_size f.
  Proof. 
    revert f; induction n as [ | n IHn ]; intros f; auto; simpl df_mexists.
    rewrite IHn; simpl; omega. 
  Qed.

  Fact df_mexists_size_Z n f : df_size_Z (df_mexists n f) = (Z.of_nat n + df_size_Z f)%Z.
  Proof.
    rewrite df_size_Z_spec, df_mexists_size, Nat2Z.inj_add, df_size_Z_spec; omega. 
  Qed.

  (* We only use it once so there is no need to automatize it *)

  Lemma df_mexists_spec n f ν : 
           df_pred (df_mexists n f) ν 
       <-> exists π, df_pred f (fun i => if le_lt_dec n i then ν (i-n) else π i).
  Proof.
    revert f ν; induction n as [ | n IHn ]; intros f v.
    + simpl; split; [ intros H; exists (fun _ => 0) | intros (? & H) ]; revert H; 
        apply df_pred_ext; intros; f_equal; omega.
    + simpl df_mexists; rewrite IHn; split; intros (pi & Hpi).
      * revert Hpi; rewrite df_pred_exst.
        intros (u & Hu).
        exists (fun i => match i with 0 => u | S i => pi i end).
        revert Hu; apply df_pred_ext.
        Opaque le_lt_dec.
        simpl; intros [ | i ].
        - replace (0-S n) with 0 by omega; auto.
        - replace (S i - S n) with (i-n) by omega. 
          simpl; destruct (le_lt_dec (S n) (S i)); 
            destruct (le_lt_dec n i); auto; omega.
      * exists (fun i => pi (S i)).
        rewrite df_pred_exst; exists (pi 0).
        revert Hpi; apply df_pred_ext.
        intros [ | i ].
        - replace (0-S n) with 0 by omega; simpl; auto.
        - replace (S i - S n) with (i-n) by omega.
          Opaque le_lt_dec.
          simpl; destruct (le_lt_dec (S n) (S i)); 
            destruct (le_lt_dec n i); auto; omega.
  Qed.

End multiple_exists.



