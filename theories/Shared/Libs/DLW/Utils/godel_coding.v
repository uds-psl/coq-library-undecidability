(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From Stdlib Require Import List Arith Lia.

From Undecidability.Shared.Libs.DLW 
  Require Import utils gcd prime pos vec.

Set Implicit Arguments.
Set Default Goal Selector "!".

#[local] Notation "e #> x" := (vec_pos e x).
#[local] Notation "e [ v / x ]" := (vec_change e x v).

Record godel_coding n := {
  gc_pr : pos n -> nat;
  gc_enc : vec nat n -> nat;
  gc_pr_nz : forall p, 0 < gc_pr p;
  gc_not_div : forall p v, v#>p = 0 -> ~ divides (gc_pr p) (gc_enc v);
  gc_succ : forall p v, gc_pr p * gc_enc v = gc_enc (v[(S (v#>p))/p])
}.

Arguments godel_coding : clear implicits.

Section powers_of_2357_props.

  (* We use prime_bool_spec which is a crude Boolean primility test *)

  Local Fact prime_2 : prime 2.   Proof. apply prime_bool_spec; trivial. Qed.
  Local Fact prime_3 : prime 3.   Proof. apply prime_bool_spec; trivial. Qed.
  Local Fact prime_5 : prime 5.   Proof. apply prime_bool_spec; trivial. Qed.
  Local Fact prime_7 : prime 7.   Proof. apply prime_bool_spec; trivial. Qed.

  Hint Resolve prime_2 prime_3 prime_5 prime_7 : core.

  Ltac does_not_divide_1 := now intros H%divides_pow%prime_divides.

  Local Fact not_divides_2_3 x : ~ divides 2 (3^x).   Proof. does_not_divide_1. Qed.
  Local Fact not_divides_2_5 x : ~ divides 2 (5^x).   Proof. does_not_divide_1. Qed.
  Local Fact not_divides_2_7 x : ~ divides 2 (7^x).   Proof. does_not_divide_1. Qed.

  Local Fact not_divides_3_2 x : ~ divides 3 (2^x).   Proof. does_not_divide_1. Qed.
  Local Fact not_divides_3_5 x : ~ divides 3 (5^x).   Proof. does_not_divide_1. Qed.
  Local Fact not_divides_3_7 x : ~ divides 3 (7^x).   Proof. does_not_divide_1. Qed.

  Local Fact not_divides_5_2 x : ~ divides 5 (2^x).   Proof. does_not_divide_1. Qed.
  Local Fact not_divides_5_3 x : ~ divides 5 (3^x).   Proof. does_not_divide_1. Qed.
  Local Fact not_divides_5_7 x : ~ divides 5 (7^x).   Proof. does_not_divide_1. Qed.

  Local Fact not_divides_7_2 x : ~ divides 7 (2^x).   Proof. does_not_divide_1. Qed.
  Local Fact not_divides_7_3 x : ~ divides 7 (3^x).   Proof. does_not_divide_1. Qed.
  Local Fact not_divides_7_5 x : ~ divides 7 (5^x).   Proof. does_not_divide_1. Qed.

  Hint Resolve not_divides_2_3 not_divides_2_5 not_divides_2_7
               not_divides_3_2 not_divides_3_5 not_divides_3_7
               not_divides_5_2 not_divides_5_3 not_divides_5_7 
               not_divides_7_2 not_divides_7_3 not_divides_7_5 : core.

  Local Fact not_divides_5_1 : ~ divides 5 1.
  Proof. apply not_divides_5_3 with (x := 0). Qed.

  Ltac fold_not := match goal with |- ?t -> False => change (~ t) end.
  Ltac does_not_divide_2 :=
    let H := fresh 
    in intros [H|H]%prime_div_mult; auto; revert H; fold_not; auto.

  Local Fact not_divides_2_35 x y : ~ divides 2 (3^x*5^y).   Proof. does_not_divide_2. Qed.
  Local Fact not_divides_3_25 x y : ~ divides 3 (2^x*5^y).   Proof. does_not_divide_2. Qed.
  Local Fact not_divides_5_23 x y : ~ divides 5 (2^x*3^y).   Proof. does_not_divide_2. Qed.
  Local Fact not_divides_7_23 x y : ~ divides 7 (2^x*3^y).   Proof. does_not_divide_2. Qed.

  Hint Resolve not_divides_2_35 not_divides_3_5 not_divides_5_1 : core.

  Ltac does_not_divide_3 :=
    let H := fresh 
    in intros H; do 2 try apply prime_div_mult in H as [H|H]; auto; revert H; fold_not; auto.

  Local Fact not_divides_2_357 x y z : ~ divides 2 (3^x*5^y*7^z). Proof. does_not_divide_3. Qed.
  Local Fact not_divides_3_257 x y z : ~ divides 3 (2^x*5^y*7^z). Proof. does_not_divide_3. Qed.
  Local Fact not_divides_5_237 x y z : ~ divides 5 (2^x*3^y*7^z). Proof. does_not_divide_3. Qed.
  Local Fact not_divides_7_235 x y z : ~ divides 7 (2^x*3^y*5^z). Proof. does_not_divide_3. Qed.

End powers_of_2357_props.

Section godel_coding_235.

  Definition combi_235 a b c := 2^a*(3^b*5^c).

  Notation "⦉ x , y , z ⦊ " := (combi_235 x y z) (at level 1, format "⦉ x , y , z ⦊ ").

  Ltac combi_235_x_0 := unfold combi_235; rewrite Nat.pow_0_r; ring.

  Local Fact combi_235_2_0 b c : ⦉0,b,c⦊ = 3^b*5^c.   Proof. combi_235_x_0. Qed.
  Local Fact combi_235_3_0 a c : ⦉a,0,c⦊ = 2^a*5^c.   Proof. combi_235_x_0. Qed.
  Local Fact combi_235_5_0 a b : ⦉a,b,0⦊ = 2^a*3^b.   Proof. combi_235_x_0. Qed.

  Ltac combi_235_multx := unfold combi_235; rewrite Nat.pow_succ_r'; ring.

  Local Fact combi_235_mult2 a b c : 2*⦉a,b,c⦊ = ⦉S a,b,c⦊ .   Proof. combi_235_multx. Qed.
  Local Fact combi_235_mult3 a b c : 3*⦉a,b,c⦊ = ⦉a,S b,c⦊ .   Proof. combi_235_multx. Qed.
  Local Fact combi_235_mult5 a b c : 5*⦉a,b,c⦊ = ⦉a,b,S c⦊ .   Proof. combi_235_multx. Qed.

  Local Definition pos3_235 : pos 3 -> nat.
  Proof.
    intro p; repeat invert pos p.
    + exact 2.
    + exact 3.
    + exact 5.
  Defined.

  Local Fact pos3_235_gt_0 x : 0 < pos3_235 x.
  Proof. repeat invert pos x; cbn; lia. Qed.

  Theorem godel_coding_235 : godel_coding 3.
  Proof.
    exists pos3_235 (fun v => ⦉v#>pos0,v#>pos1,v#>pos2⦊).
    + apply pos3_235_gt_0.
    + intros p; repeat invert pos p; intros v ->.
      * rewrite combi_235_2_0; apply not_divides_2_35.
      * rewrite combi_235_3_0; apply not_divides_3_25.
      * rewrite combi_235_5_0; apply not_divides_5_23.
    + intros p; repeat invert pos p; intros v; rew vec.
      * apply combi_235_mult2.
      * apply combi_235_mult3.
      * apply combi_235_mult5.
  Qed.

End godel_coding_235.

Section godel_coding_2357.

  Definition combi_2357 a b c d := 2^a*(3^b*(5^c*7^d)).

  Notation "⦉ x , y , z , u ⦊" := (combi_2357 x y z u) (at level 1, format "⦉ x , y , z , u ⦊").

  Ltac combi_2357_x_0 := unfold combi_2357; rewrite Nat.pow_0_r; ring.

  Local Fact combi_2357_2_0 b c d : ⦉0,b,c,d⦊ = 3^b*5^c*7^d.   Proof. combi_2357_x_0. Qed.
  Local Fact combi_2357_3_0 a c d : ⦉a,0,c,d⦊ = 2^a*5^c*7^d.   Proof. combi_2357_x_0. Qed.
  Local Fact combi_2357_5_0 a b d : ⦉a,b,0,d⦊ = 2^a*3^b*7^d.   Proof. combi_2357_x_0. Qed.
  Local Fact combi_2357_7_0 a b c : ⦉a,b,c,0⦊ = 2^a*3^b*5^c.   Proof. combi_2357_x_0. Qed.

  Ltac combi_2357_multx := unfold combi_2357; rewrite Nat.pow_succ_r'; ring.

  Local Fact combi_2357_mult2 a b c d : 2*⦉a,b,c,d⦊ = ⦉S a,b,c,d⦊.   Proof. combi_2357_multx. Qed.
  Local Fact combi_2357_mult3 a b c d : 3*⦉a,b,c,d⦊ = ⦉a,S b,c,d⦊.   Proof. combi_2357_multx. Qed.
  Local Fact combi_2357_mult5 a b c d : 5*⦉a,b,c,d⦊ = ⦉a,b,S c,d⦊.   Proof. combi_2357_multx. Qed.
  Local Fact combi_2357_mult7 a b c d : 7*⦉a,b,c,d⦊ = ⦉a,b,c,S d⦊.   Proof. combi_2357_multx. Qed.

  Local Definition pos4_2357 : pos 4 -> nat.
  Proof.
    intro p; repeat invert pos p.
    + exact 2.
    + exact 3.
    + exact 5.
    + exact 7.
  Defined.

  Local Fact pos4_2357_gt_0 x : 0 < pos4_2357 x.
  Proof. repeat invert pos x; cbn; lia. Qed.

  Theorem godel_coding_2357 : godel_coding 4.
  Proof.
    exists pos4_2357 (fun v => ⦉v#>pos0,v#>pos1,v#>pos2,v#>pos3⦊).
    + apply pos4_2357_gt_0.
    + intros p; repeat invert pos p; intros v ->.
      * rewrite combi_2357_2_0; apply not_divides_2_357.
      * rewrite combi_2357_3_0; apply not_divides_3_257.
      * rewrite combi_2357_5_0; apply not_divides_5_237.
      * rewrite combi_2357_7_0; apply not_divides_7_235.
    + intros p; repeat invert pos p; intros v; rew vec.
      * apply combi_2357_mult2.
      * apply combi_2357_mult3.
      * apply combi_2357_mult5.
      * apply combi_2357_mult7.
  Qed.

End godel_coding_2357.
