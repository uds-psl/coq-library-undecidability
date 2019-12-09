(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

(** ** Elementary diophantine constraints *)

Require Import List Arith Nat Omega.

From Undecidability.Shared.Libs.DLW.Utils 
  Require Import utils_list gcd prime.

From Undecidability.H10.Dio 
  Require Import dio_logic.

Set Implicit Arguments.

Local Notation "phi ↑ k" := (env_lift phi k) (at level 1, format "phi ↑ k", left associativity).
Local Notation "phi ↓"   := (fun n => phi (S n)) (at level 1, format "phi ↓", no associativity).

Section interval.

  (** A small interval & valuation library *)

  Definition interval := (nat * nat)%type. (* (a,b) <~~~> [a,b[ *)

  Implicit Types (i j : interval).

  Definition in_interval i x := let (a,b) := i in a <= x < b.
  Definition out_interval i x := let (a,b) := i in x < a \/ b <= x.
  Definition interval_disjoint i j := forall x, in_interval i x -> in_interval j x -> False.

  Definition interval_union (i j : interval) :=
    match i, j with (a1,b1),(a2,b2) => (min a1 a2, max b1 b2) end.

  Fact in_out_interval i x : in_interval i x -> out_interval i x -> False.
  Proof. destruct i; simpl; omega. Qed.

  Fact in_out_interval_dec i x : { in_interval i x } + { out_interval i x }.
  Proof. 
    destruct i as (a,b); simpl.
    destruct (le_lt_dec a x); destruct (le_lt_dec b x); try (left; omega);right; omega.
  Qed. 

  Fact interval_union_left i j x : in_interval i x -> in_interval (interval_union i j) x.
  Proof.
    revert i j; intros (a,b) (u,v); simpl.
    generalize (Nat.le_min_l a u) (Nat.le_max_l b v); omega.
  Qed.

  Fact interval_union_right i j x : in_interval j x -> in_interval (interval_union i j) x.
  Proof.
    revert i j; intros (a,b) (u,v); simpl.
    generalize (Nat.le_min_r a u) (Nat.le_max_r b v); omega.
  Qed.

  Definition valuation_union i1 (g1 : nat -> nat) i2 g2 : 
               interval_disjoint i1 i2 
            -> { g | (forall x, in_interval i1 x -> g x = g1 x)
                  /\ (forall x, in_interval i2 x -> g x = g2 x) }.
  Proof.
    intros H2.
    exists (fun x => if in_out_interval_dec i1 x then g1 x else g2 x).
    split; intros x Hx.
    + destruct (in_out_interval_dec i1 x) as [ | H3 ]; auto.
      exfalso; revert Hx H3; apply in_out_interval.
    + destruct (in_out_interval_dec i1 x) as [ H3 | ]; auto.
      exfalso; revert H3 Hx; apply H2.
  Qed.

  Definition valuation_one_union k v i1 (g1 : nat -> nat) i2 g2 : 
               ~ in_interval (interval_union i1 i2) k 
            -> interval_disjoint i1 i2 
            -> { g | g k = v /\ (forall x, in_interval i1 x -> g x = g1 x)
                             /\ (forall x, in_interval i2 x -> g x = g2 x) }.
  Proof.
    intros H1 H2.
    exists (fun x => if eq_nat_dec x k then v 
                     else if in_out_interval_dec i1 x then g1 x 
                     else g2 x).
    split; [ | split ].
    + destruct (eq_nat_dec k k) as [ | [] ]; auto.
    + intros x Hx.
      destruct (eq_nat_dec x k) as [ | ].
      * subst; destruct H1; apply interval_union_left; auto.
      * destruct (in_out_interval_dec i1 x) as [ | H3 ]; auto.
        exfalso; revert Hx H3; apply in_out_interval.
    + intros x Hx.
      destruct (eq_nat_dec x k) as [ | ].
      * subst; destruct H1; apply interval_union_right; auto.
      * destruct (in_out_interval_dec i1 x) as [ H3 | ]; auto.
        exfalso; revert H3 Hx; apply H2.
  Qed.

End interval.

Section diophantine_system.

  (* v : cst = nat      constant (natural number)
     p q : par = nat    parameter 
     x y z : var = nat  existentially quantified variable 
   
     equations are of 4 types 
       1) x = v 
       2) x = p 
       3) x = y + z 
       4) x = y * z 

     We represent a relation between parameters R by a list of equations l and one
     variable s : var such that
       a) for any value f : nat -> nat of the params, l[f] has a solution
       b) for any value f : nat -> nat of the params,

                R f <-> ((s=0)::l)[f] has a solution

     How do we simulate x = n ?

          x = n <-> s = 0 /\ exists p q u v w, s = p+q /\ u = p+v /\ u = q+w /\ v = x /\ w = n

     How do we simulate x = y + z 
        
          x = y+z <-> s = 0 /\ exists p q u v w r t, s = p+q /\ t = p+u /\ t=q+r
                                          /\ r = v+w /\ u = x /\ v = y /\ w = z 

     We implement conjunction (cap), disjunction (cup) and exists so that we get a linear encoding

      cap) R by (lR,xR) and S by (lS,xS) 
           we assume (lR,xR) and (lS,xS) do not share existential variables
           (always possible by renaming those of S)

           R cap S = (lR U lS U { z = x+y },z) where z is fresh
 
      cup) R cup S = (lR U lS U { z = x*y },z)

      exists) ∃n.R f{p<-n} = (lR[p<-0], ...)

   *)

  Inductive dio_elem_expr : Set :=
    | dee_nat  : nat -> dio_elem_expr   (* c : constant *)
    | dee_var  : nat -> dio_elem_expr   (* v : existentially quant. var *)
    | dee_par  : nat -> dio_elem_expr   (* p : parameter *)
    | dee_comp : dio_op -> nat -> nat -> dio_elem_expr. (* v1 op v2 *)

  Notation dee_add := (dee_comp do_add).
  Notation dee_mul := (dee_comp do_mul).

  Definition dee_eval φ ν e := 
    match e with
      | dee_nat n => n
      | dee_var v => φ v
      | dee_par i => ν i
      | dee_comp o v w => de_op_sem o (φ v) (φ w)
    end.

  Definition dee_vars e x  :=
    match e with
      | dee_nat _ => False
      | dee_var v => x = v
      | dee_par _ => False
      | dee_comp _ v w => x = v \/ x = w
    end.

  Fact dee_eval_ext e φ1 ν1 φ2 ν2  : 
        (forall x, dee_vars e x -> φ1 x = φ2 x) 
     -> (forall x, ν1 x = ν2 x)
     -> dee_eval φ1 ν1 e = dee_eval φ2 ν2 e.
  Proof. destruct e as [ | | | [] ]; simpl; auto. Qed.

  Definition dee_dec k e :=
    match e with
      | dee_nat n      => dee_nat n
      | dee_var v      => dee_var v
      | dee_par 0      => dee_var k 
      | dee_par (S i)  => dee_par i
      | dee_comp o v w => dee_comp o v w
    end.

  Fact dee_eval_dec φ ν k e : dee_eval φ ν (dee_dec k e) = dee_eval φ (fun x => match x with 0 => φ k | S x => ν x end) e.
  Proof. destruct e as [ | | [] | [] ]; simpl; auto. Qed.

  Fact dee_vars_dec k e x : dee_vars (dee_dec k e) x -> x = k \/ dee_vars e x.
  Proof. destruct e as [ | | [] | [] ]; simpl; firstorder. Qed.

  Definition dio_constraint := (nat * dio_elem_expr)%type.

  Implicit Type (c : dio_constraint).

  Definition dc_eval φ ν c := φ (fst c) = dee_eval φ ν (snd c).

  Arguments dc_eval φ ν c /.
  
  Definition dc_vars c x := x = fst c \/ dee_vars (snd c) x.

  Arguments dc_vars c x /.

  Fact dc_eval_ext c φ1 ν1 φ2 ν2  : 
        (forall x, dc_vars c x -> φ1 x = φ2 x) 
     -> (forall x, ν1 x = ν2 x)
     -> dc_eval φ1 ν1 c <-> dc_eval φ2 ν2 c.
  Proof.
    intros H1 H2.
    destruct c as (v,e); unfold dc_eval; simpl.
    rewrite H1; simpl; auto.
    rewrite dee_eval_ext with e φ1 ν1 φ2 ν2; try tauto.
    intros; apply H1; simpl; auto.
  Qed.

  Definition dc_dec k c := (fst c, dee_dec k (snd c)).

  Fact dc_eval_dec φ ν k c : dc_eval φ ν (dc_dec k c) <-> dc_eval φ  (fun x => match x with 0 => φ k | S x => ν x end) c.
  Proof. destruct c; simpl; rewrite dee_eval_dec; tauto. Qed.

  Fact dc_vars_dec k c x : dc_vars (dc_dec k c) x -> x = k \/ dc_vars c x.
  Proof. destruct c; simpl; intros [ | H ]; auto; apply dee_vars_dec in H; tauto. Qed.

  Implicit Type (R : (nat -> nat) -> Prop).

  (* A diophantine system for R is an interval i, a list l of constraints, a reference variable x
     such that
       1) the variables in l U {x} and belong to i
       2) for any valuation, the equations of l are satisfiable
       3) for any valuation ν, R ν holds iff the equations of { x=0 } U l are satisfiable
   *)

  Record dio_repr_at R a n l := {
    ds_eqns : list dio_constraint;
    ds_ref  : nat;
    ds_H0   : length ds_eqns = l;
    ds_H1   : forall x c, In c ds_eqns -> dc_vars c x -> a <= x < a+n;
    ds_H2   : a <= ds_ref < a+n;
    ds_H3   : forall ν, exists φ, Forall (dc_eval φ ν) ds_eqns;
    ds_H4   : forall ν, R ν <-> exists φ, Forall (dc_eval φ ν) ds_eqns /\ φ ds_ref = 0;
  }.

  Let g0 (n x0 x1 x2 x3 x4 x5 x6 x7 m : nat) := if le_lt_dec n m then 
                                 match m - n with
                                   | 0 => x0
                                   | 1 => x1
                                   | 2 => x2
                                   | 3 => x3
                                   | 4 => x4
                                   | 5 => x5
                                   | 6 => x6
                                   | _ => x7
                                end
                              else x0.

  Tactic Notation "g0" "auto" constr(n) constr(t) := 
    unfold g0; destruct (le_lt_dec n (n+t)); try omega;
    replace (n+t-n) with t by omega; auto.

  Let g0_0 (n x0 x1 x2 x3 x4 x5 x6 x7 : nat) : g0 n x0 x1 x2 x3 x4 x5 x6 x7 (n+0) = x0.
  Proof. g0 auto n 0. Qed. 

  Let g0_1 (n x0 x1 x2 x3 x4 x5 x6 x7 : nat) : g0 n x0 x1 x2 x3 x4 x5 x6 x7 (n+1) = x1.
  Proof. g0 auto n 1. Qed. 

  Let g0_2 (n x0 x1 x2 x3 x4 x5 x6 x7 : nat) : g0 n x0 x1 x2 x3 x4 x5 x6 x7 (n+2) = x2.
  Proof. g0 auto n 2. Qed. 
 
  Let g0_3 (n x0 x1 x2 x3 x4 x5 x6 x7 : nat) : g0 n x0 x1 x2 x3 x4 x5 x6 x7 (n+3) = x3.
  Proof. g0 auto n 3. Qed. 

  Let g0_4 (n x0 x1 x2 x3 x4 x5 x6 x7 : nat) : g0 n x0 x1 x2 x3 x4 x5 x6 x7 (n+4) = x4.
  Proof. g0 auto n 4. Qed. 

  Let g0_5 (n x0 x1 x2 x3 x4 x5 x6 x7 : nat) : g0 n x0 x1 x2 x3 x4 x5 x6 x7 (n+5) = x5.
  Proof. g0 auto n 5. Qed. 

  Let g0_6 (n x0 x1 x2 x3 x4 x5 x6 x7 : nat) : g0 n x0 x1 x2 x3 x4 x5 x6 x7 (n+6) = x6.
  Proof. g0 auto n 6. Qed. 

  Let g0_7 (n x0 x1 x2 x3 x4 x5 x6 x7 : nat) : g0 n x0 x1 x2 x3 x4 x5 x6 x7 (n+7) = x7.
  Proof. g0 auto n 7. Qed. 

  Tactic Notation "rew" "g0" := 
    try rewrite !g0_0;
    try rewrite !g0_1;
    try rewrite !g0_2;
    try rewrite !g0_3;
    try rewrite !g0_4;
    try rewrite !g0_5;
    try rewrite !g0_6;
    try rewrite !g0_7.
 
  Let complete_lemma x y : { u : nat & { v | u+x = v+y } }.
  Proof.
    destruct (le_lt_dec x y).
    + exists (y-x), 0; omega.
    + exists 0, (x-y); omega.
  Qed.

  (** x = i <~~> s = 0 /\ exists s p q u v w, s = p+q /\ u = p+v /\ u = q+w /\ v = x /\ w = i *)

  Lemma dio_repr_at_cst x i a : dio_repr_at (fun ν => ν x = i) a 6 5.
  Proof.
    exists ( (a+5,dee_add (a+0) (a+1))     (* s = p + q *)
           ::(a+2,dee_add (a+0) (a+3))     (* u = p + v *)
           ::(a+2,dee_add (a+1) (a+4))     (* u = q + w *)
           ::(a+3,dee_par x)               (* v = x     *)
           ::(a+4,dee_nat i)               (* w = i     *)
           ::nil)
           (a+5); simpl; auto; try omega.
    + intros j c.
      repeat (intros [ <- | H ]; [ simpl; try omega | revert H ]); try tauto.
    + intros v.
      destruct (complete_lemma (v x) i) as (p & q & H).
      exists (g0 a p q (p+v x) (v x) i (p+q) 0 0); 
        repeat constructor; simpl; rew g0; auto.
    + intros v; split.
      * intros H.
        exists (g0 a 0 0 (v x) (v x) i 0 0 0); 
          repeat constructor; simpl; rew g0; auto.
      * intros (phi & H); revert H.
        repeat rewrite Forall_cons_inv; simpl; omega.
  Defined.

  (** x = y o z <~~> s = 0 /\ exists p q u v w r t, s = p+q /\ t = p+u /\ t=q+r
                                          /\ r = v+w /\ u = x /\ v = y /\ w = z *)

  Lemma dio_repr_at_op o x y z a : dio_repr_at (fun ν => ν x = de_op_sem o (ν y) (ν z)) a 8 7.
  Proof.
    exists ( (a+7,dee_add (a+0) (a+1))     (* s = p + q *)
           ::(a+6,dee_add (a+0) (a+2))     (* t = p + u *)
           ::(a+6,dee_add (a+1) (a+5))     (* t = q + r *)
           ::(a+5,dee_comp o (a+3) (a+4))  (* r = v o w *)
           ::(a+2,dee_par x)               (* u = x     *)
           ::(a+3,dee_par y)               (* v = y     *)
           ::(a+4,dee_par z)               (* w = z     *)
           ::nil)
           (a+7); simpl; auto; try omega.
    + intros j c.
      repeat (intros [ <- | H ]; [ simpl; try omega | revert H ]); try tauto.
    + intros v.
      destruct (complete_lemma (v x) (de_op_sem o (v y) (v z))) as (p & q & H).
      exists (g0 a p q (v x) (v y) (v z) (de_op_sem o (v y) (v z)) (p+v x) (p+q)); 
        repeat constructor; simpl; rew g0; auto.
    + intros v; split.
      * intros H.
        exists (g0 a 0 0 (v x) (v y) (v z) (v x) (v x) 0); 
          repeat constructor; simpl; rew g0; auto.
      * intros (phi & H); revert H.
        repeat rewrite Forall_cons_inv; simpl. 
        intros ((E1 & E2 & E3 & E4 & E5 & E6 & E7 & _) & E0).
        rewrite <- E6, <- E7, <- E4; omega.
  Defined.

  Let not_interval_union a1 n1 a2 n2 : 
           a1+n1 <= a2
        -> ~ in_interval (interval_union (a1, a1 + n1) (a2, a2 + n2)) (a2 + n2).
  Proof.
    simpl; intros H1 (_ & H3).
    rewrite Nat.max_r in H3; omega.
  Qed.

  Let dio_op_swap o := match o with do_add => do_mul | do_mul => do_add end.

  Fact dio_repr_at_bin o R1 a1 n1 p1 R2 a2 n2 p2 n : 
          dio_repr_at R1 a1 n1 p1
       -> dio_repr_at R2 a2 n2 p2
       -> a1+n1 <= a2
       -> n = 1+a2+n2-a1
       -> dio_repr_at (fun ν => df_op_sem o (R1 ν) (R2 ν)) a1 n (1+p1+p2).
  Proof.
    intros [ l1 r1 F0 F1 F2 F3 F4 ] [ l2 r2 G0 G1 G2 G3 G4 ] H12 ?; subst n.
    exists ((a2+n2,dee_comp (dio_op_swap o) r1 r2)::l1++l2) (a2+n2).
    + simpl; rewrite app_length, F0, G0; omega.
    + replace (a1+(1+a2+n2-a1)) with (1+a2+n2) by omega.
      intros x c [ Hc | Hc ].
      * subst; simpl; omega.
      * intros H1; apply in_app_or in Hc; destruct Hc as [ Hc | Hc ].
        - specialize (F1 _ _ Hc H1); omega.
        - specialize (G1 _ _ Hc H1); omega.
    + omega.
    + intros f.
      destruct (F3 f) as (g1 & H1).
      destruct (G3 f) as (g2 & H2).
      destruct (@valuation_one_union (a2+n2) (de_op_sem (dio_op_swap o) (g1 r1) (g2 r2)) (a1,a1+n1) g1 (a2,a2+n2) g2) 
        as (g & Hg1 & Hg2 & Hg3); auto.
      { red; simpl; intros; omega. }
      exists g; constructor; [ | apply Forall_app; split ].
      * simpl; rewrite Hg1, (Hg2 r1), (Hg3 r2); auto.
      * apply Forall_impl with (2 := H1).
        intros c Hc; apply dc_eval_ext; auto.
        intros x Hx; apply Hg2, F1 with c; auto.
      * apply Forall_impl with (2 := H2).
        intros c Hc; apply dc_eval_ext; auto.
        intros x Hx; apply Hg3, G1 with c; auto.
    + intros f. 
      destruct o; simpl; rewrite F4, G4; split.
      * intros [ (g1 & H1 & H2) | (g2 & H1 & H2) ].
        - destruct (G3 f) as (g2 & H3).
          destruct (@valuation_one_union (a2+n2) 0 (a1,a1+n1) g1 (a2,a2+n2) g2) 
            as (g & Hg1 & Hg2 & Hg3); auto.
          { red; simpl; intros; omega. }
          exists g; split; auto.
          constructor; simpl; [ | apply Forall_app; split ].
          ++ rewrite Hg1, Hg2, H2; auto.
          ++ apply Forall_impl with (2 := H1).
             intros c Hc; apply dc_eval_ext; auto.
             intros x Hx; apply Hg2, F1 with c; auto.
          ++ apply Forall_impl with (2 := H3).
             intros c Hc; apply dc_eval_ext; auto.
             intros x Hx; apply Hg3, G1 with c; auto.
        - destruct (F3 f) as (g1 & H3).
          destruct (@valuation_one_union (a2+n2) 0 (a1,a1+n1) g1 (a2,a2+n2) g2) 
            as (g & Hg1 & Hg2 & Hg3); auto.
          { red; simpl; intros; omega. }
          exists g; split; auto.
          constructor; simpl; [ | apply Forall_app; split ].
          ++ rewrite Hg1, (Hg3 r2), H2, mult_comm; auto.
          ++ apply Forall_impl with (2 := H3).
             intros c Hc; apply dc_eval_ext; auto.
             intros x Hx; apply Hg2, F1 with c; auto.
          ++ apply Forall_impl with (2 := H1).
             intros c Hc; apply dc_eval_ext; auto.
             intros x Hx; apply Hg3, G1 with c; auto.
      * intros (g & Hg1 & Hg2).
        inversion Hg1 as [ | ? ? Hg3 Hg4 ].
        apply Forall_app in Hg4; destruct Hg4 as (Hg4 & Hg5).
        simpl in Hg3; rewrite Hg2 in Hg3.
        symmetry in Hg3; apply mult_is_O in Hg3.
        destruct Hg3 as [ Hg3 | Hg3 ]; [ left | right ]; exists g; auto.
      * intros ((g1 & H1 & H2) & (g2 & H3 & H4)).
        destruct (@valuation_one_union (a2+n2) 0 (a1,a1+n1) g1 (a2,a2+n2) g2) 
          as (g & Hg1 & Hg2 & Hg3); auto.
        { red; simpl; intros; omega. }
        exists g; split; auto; constructor; simpl.
        ++ rewrite Hg1, Hg2, Hg3; auto; omega.
        ++ apply Forall_app; split.
           ** apply Forall_impl with (2 := H1).
              intros c Hc; apply dc_eval_ext; auto.
              intros x Hx; apply Hg2, F1 with c; auto.
           ** apply Forall_impl with (2 := H3).
              intros c Hc; apply dc_eval_ext; auto.
              intros x Hx; apply Hg3, G1 with c; auto.
      * intros (g & Hg1 & Hg2).
        inversion Hg1 as [ | ? ? Hg3 Hg4 ].
        apply Forall_app in Hg4; destruct Hg4 as (Hg4 & Hg5).
        simpl in Hg3; split; exists g; split; auto; omega.
  Defined.

  Lemma dio_repr_at_exst R a n m p : 
          dio_repr_at R a n p
       -> m = n+1
       -> dio_repr_at (fun ν => exists n, R ν↑n) a m p. 
  Proof.
    intros [ l r F0 F1 F2 F3 F4 ] ?; subst m.
    exists (map (dc_dec (a+n)) l) r.
    + rewrite map_length; auto.
    + intros x c'; rewrite in_map_iff.
      intros (c & E & Hc) H; subst.
      apply dc_vars_dec in H.
      destruct H as [ | H ]; subst; simpl; try omega.
      apply F1 in H; simpl in *; auto; omega.
    + omega.
    + intros f.
      destruct (F3 (fun x => match x with 0 => 0 | S x => f x end)) as (g & Hg).
      exists (fun x => if eq_nat_dec x (a+n) then 0 else g x).
      rewrite Forall_map.
      apply Forall_impl with (2 := Hg). 
      intros c Hc; rewrite dc_eval_dec; apply dc_eval_ext; auto.
      * intros x Hx.
        destruct (eq_nat_dec x (a+n)); subst; auto.
        apply F1 in Hx; auto; omega.
      * intros [ | x ]; auto.
        destruct (eq_nat_dec (a+n) (a+n)); tauto.
    + intros f; split.
      * intros (u & Hu).
        apply F4 in Hu.
        destruct Hu as (g & H1 & H2).
        exists (fun x => if eq_nat_dec x (a+n) then u else g x); simpl; split.
        - rewrite Forall_map.
          apply Forall_impl with (2 := H1).
          intros c Hc; rewrite dc_eval_dec; apply dc_eval_ext; auto.
          ++ intros x Hx.
             destruct (eq_nat_dec x (a+n)); auto.
             subst x; apply F1 in Hx; auto; omega.
          ++ intros [ | x ]; auto.
             destruct (eq_nat_dec (a+n) (a+n)); tauto.
        - destruct (eq_nat_dec r (a+n)); auto.
          subst; omega.
      * intros (g & H1 & H2).
        exists (g (a+n)); rewrite F4.
        exists g; split; auto.
        revert H1; do 2 rewrite Forall_forall.
        intros H c Hc.
        apply in_map with (f := dc_dec _), H in Hc.
        revert Hc; rewrite dc_eval_dec; apply dc_eval_ext; auto.
        intros []; simpl; auto.
  Defined.

  Fixpoint df_weight_1 f :=
    match f with
      | df_cst _ _     => 6
      | df_op _ _ _ _  => 8
      | df_bin _ f g   => 1 + df_weight_1 f + df_weight_1 g  
      | df_exst f      => 1 + df_weight_1 f
    end.

  Fact df_weigth_1_size f : df_weight_1 f <= 8*df_size f.
  Proof. induction f; simpl; omega. Qed.

  Fixpoint df_weight_2 f :=
    match f with
      | df_cst _ _     => 5
      | df_op _ _ _ _  => 7
      | df_bin _ f g   => 1 + df_weight_2 f + df_weight_2 g  
      | df_exst f      => df_weight_2 f
    end.

  Fact df_weigth_2_size f : df_weight_2 f <= 7*df_size f.
  Proof. induction f; simpl in *; omega. Qed.

  Lemma dio_repr_at_form n f : dio_repr_at (df_pred f) n (df_weight_1 f) (df_weight_2 f).
  Proof.
    revert n;
    induction f as [ x i | o x y z | o f IHf g IHg | f IHf ]; intros n; simpl df_pred; simpl df_weight_1; simpl df_weight_2.
    + apply dio_repr_at_cst; auto.
    + apply dio_repr_at_op; auto.
    + apply dio_repr_at_bin with (n1 := df_weight_1 f) (a2 := n+df_weight_1 f) (n2 := df_weight_1 g); auto; omega.
    + apply dio_repr_at_exst with (n := df_weight_1 f); auto; omega.
  Defined.

End diophantine_system.

(** For any diophantine logic formula f of size s, one can compute a list l 
    of at most 1+8*s elementary diophantine constraints, containing at 
    most 7*s variables and such that df_pred f ν is equivalent to 
    the simultaneous satisfiability at ν of all the elementary constraints in l *)

Theorem dio_formula_elem f : { l | length l <= 1+7*df_size f
                               /\ (forall c x, In c l -> dc_vars c x -> x < 8*df_size f)  
                               /\  forall ν, df_pred f ν <-> exists φ, Forall (dc_eval φ ν) l }.
Proof.
  destruct (dio_repr_at_form 0 f) as [l r H0 H1 H2 H3 H4].
  exists ((r,dee_nat 0) :: l); split; [ | split ]; simpl length; try omega.
  + rewrite H0; apply le_n_S, df_weigth_2_size.
  + intros c x [ [] | H ].
    * simpl dc_vars; intros [ | [] ]; subst.
      generalize (df_weigth_1_size f); intros; simpl; omega.
    * intros G; apply H1 in G; auto.
      generalize (df_weigth_1_size f); intros; simpl; omega.
  + intros ν; rewrite H4.
    split; intros (φ & H); exists φ; revert H; rewrite Forall_cons_inv; simpl; tauto.
Defined.

Definition dio_fs f := proj1_sig (dio_formula_elem f).
 
(* Check dio_formula_elem.
Print Assumptions dio_formula_elem. *)

