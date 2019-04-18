(** * Definitions and Automation for PrettyBounds *)

From Undecidability Require Export TM.Prelim.
From Undecidability Require Export TM.ArithPrelim.
From Undecidability Require Export TM.Code.Code.

Arguments size {sig X cX}.


(** We use the following notion to bound up to some constant factor *)

Definition dominatedWith c x y := x <= c * y.

Notation "x '<=(' c ')' y" := (dominatedWith c x y) (at level 70, format "x  '<=(' c ')'  y").

(** Short example *)
Goal { c | forall x, 3*x*x + 4 <=(c) x*x + 1}.
  exists 4. intros. unfold dominatedWith. lia.
Qed.

(** * Automation *)
(* The idea is that we always have a goal of shape "x <=(?c) y", and the lemmas fill the evar ?c*)
(* See examples further down.*)
(* Sadly, this approach works only for non-recursive functions*)

Smpl Create domWith.
Ltac domWith_approx := repeat (smpl domWith).

Lemma dominatedWith_add c1 c2 y x1 x2:
  x1 <=(c1) y ->
  x2 <=(c2) y ->
  (x1+x2) <=(c1+c2) y.
Proof.
  unfold dominatedWith.
  lia.
Qed.

(*simple eapply to disallow unfolding of constants to find the "+" *)
Smpl Add 10 simple eapply dominatedWith_add: domWith.

Lemma dominatedWith_add_l c1 c2 x y:
  x <=(c2) y ->
  1 <= y ->
  (c1+x) <=(c1+c2) y.
Proof. intros. apply dominatedWith_add; auto. hnf. nia. Qed.

Lemma dominatedWith_add_r c1 c2 x y:
  x <=(c2) y ->
  1 <= y ->
  (x+c1) <=(c1+c2) y.
Proof. intros. setoid_rewrite Nat.add_comm at 1. apply dominatedWith_add; auto. hnf. nia. Qed.

Lemma dominatedWith_mult_l c c' x y:
  x <=(c) y ->
  (c'*x) <=(c'*c) y.
Proof.
  unfold dominatedWith. intros ?. rewrite <- mult_assoc. eapply Nat.mul_le_mono; eauto.
Qed.

Lemma dominatedWith_mult_r c c' x y:
  x <=(c) y ->
  (x*c') <=(c'*c) y.
Proof.
  intros. unfold dominatedWith in *. rewrite H. lia.
Qed.

Smpl Add 10 simple eapply dominatedWith_mult_r : domWith.
Smpl Add 10 simple eapply dominatedWith_mult_l : domWith.


Lemma dominatedWith_const x y:
  1 <= y ->
  x <=(x) y.
Proof.
  unfold dominatedWith. intros;destruct y. omega. ring_simplify. lia.
Qed.

Smpl Add 50 (simple eapply dominatedWith_const;nia) : domWith.

Lemma dominatedWith_solve x y:
  x <= y ->
  x <=(1) y.
Proof. unfold dominatedWith. intros;destruct y. omega. ring_simplify. lia. Qed.


Smpl Add 50 (simple eapply dominatedWith_solve;(nia)) : domWith.


Lemma dominatedWith_S c x y :
  x <=(c) y ->
  x <=(c) S y.
Proof.
  unfold dominatedWith. intros H. rewrite Nat.mul_succ_r. omega.
Qed.

Lemma dominatedWith_S' c x y :
  1 <= y ->
  x <=(c) y ->
  S x <=(S c) y.
Proof.
  unfold dominatedWith. intros H. rewrite Nat.mul_succ_l.
  transitivity (S (c * y)).
  - now rewrite H0.
  - omega.
Qed.

(* We can use this lemma if we know that the input is bound *)
Lemma dominatedWith_S'' c x y :
  c < y ->
  y > 0 ->
  x <=(c) S y ->
  x <=(S c) y.
Proof. unfold dominatedWith. intros H. rewrite Nat.mul_succ_l, Nat.mul_succ_r. intros. lia. Qed.



(** This Lemma is meant to be used *)
Lemma dominatedWith_trans c c' x y z:
  x <=(c) y ->
  y <=(c') z ->
  x <=(c'*c) z.
Proof.
  unfold dominatedWith. intros H H'.
  rewrite H' in H. lia.
Qed.

Instance dominatedWith_leq_Proper c:
  Proper (Basics.flip le ==> le ==> Basics.impl) (dominatedWith c).
Proof.
  unfold dominatedWith. intros x' x Hx y y' Hy H. rewrite <- Hy,<-H. exact Hx.
Qed.

Smpl Create domWith_match.
Ltac domWith_match := smpl domWith_match.

Smpl Add 12 domWith_match: domWith.

Lemma dominatedWith_match_list' X (l:list X) f g c1 c2:
  (l = [] -> f <=(c1) g )
  -> (forall x xs, l = x::xs -> f <=(c2) g )
  -> f <=(max c1 c2) (g) .
Proof with reflexivity + apply Nat.mul_le_mono; eauto using Nat.le_max_r,Nat.le_max_l.
  intros H1 H2. unfold dominatedWith in *.
  destruct l.
  -rewrite H1...
  -rewrite H2...
Qed.

Lemma dominatedWith_match_list X (l:list X) y z g c1 c2:
  (l = [] -> y <=(c1) z)
  -> (forall x xs, l = x::xs -> g x xs <=(c2) z)
  -> match l with
      [] => y
    | x::xs => g x xs
    end <=(max c1 c2) z .
Proof with reflexivity + apply Nat.mul_le_mono; eauto using Nat.le_max_r,Nat.le_max_l.
  intros H1 H2.
  eapply dominatedWith_match_list' with (l:=l);[intros H|intros ? ? H];rewrite !H.
  all: eauto.
Qed.

Smpl Add 12
     match goal with
       |- (match _ with [] => _ | _::_ => _ end) <=(_) _ =>
       let H := fresh in (eapply dominatedWith_match_list;[intros H|intros ? ? H]);try rewrite !H
     end: domWith_match.


Lemma dominatedWith_match_nat n y z g c1 c2:
  (n = 0 -> y <=(c1) z) ->
  (forall x, n = S x -> g x <=(c2) z) ->
  match n with
  | 0 => y
  | S x => g x
  end <=(max c1 c2) z .
Proof with reflexivity + apply Nat.mul_le_mono; eauto using Nat.le_max_r,Nat.le_max_l.
  intros H1 H2. unfold dominatedWith in *.
  destruct n.
  -rewrite H1...
  -rewrite H2...
Qed.

Smpl Add 12
     match goal with
     | [ |- (match _ with 0 => _ | S _ => _ end) <=(_) _ ] =>
       let H := fresh in (eapply dominatedWith_match_nat;[intros H|intros ? H]);try rewrite !H
     end: domWith_match.

Lemma dominatedWith_match_option (X : Type) (z : nat) (o : option X) (c1 c2 : nat) (g : X -> nat) (y : nat) :
  (forall x, o = Some x -> g x <=(c1) z) ->
  (o = None -> y <=(c2) z) ->
  match o with
  | Some x => g x
  | None => y
  end <=(max c1 c2) z .
Proof with reflexivity + apply Nat.mul_le_mono; eauto using Nat.le_max_r,Nat.le_max_l.
  intros H1 H2. unfold dominatedWith in *.
  destruct o.
  - rewrite H1...
  - rewrite H2...
Qed.


Smpl Add 12
     match goal with
     | [ |- (match _ with None => _ | Some _ => _ end) <=(_) _ ] =>
       let H := fresh in (eapply dominatedWith_match_option; [intros ? H |intros ?]); try rewrite !H
     end : domWith_match.

Lemma dominatedWith_match_sumbool (X Y : Prop) (z : nat) (s : {X} + {Y}) (c1 c2 : nat) (x : nat) (y : nat) :
  (forall (Px : X), s = Specif.left Px -> x <=(c1) z) ->
  (forall (Py : Y), s = Specif.right Py -> y <=(c2) z) ->
  match s with
  | Specif.left Px => x
  | Specif.right Py => y
  end <=(max c1 c2) z .
Proof with reflexivity + apply Nat.mul_le_mono; eauto using Nat.le_max_r,Nat.le_max_l.
  intros H1 H2. unfold dominatedWith in *.
  destruct s.
  - rewrite H1...
  - rewrite H2...
Qed.

Smpl Add 12
     match goal with
     | [ |- (match _ with Specif.left _ => _ | Specif.right _ => _ end) <=(_) _ ] =>
       let H := fresh in (eapply dominatedWith_match_sumbool; [intros ? H |intros ? H]); try rewrite !H
     end : domWith_match.


Lemma dominatedWith_match_bool (z : nat) (b : bool) (c1 c2 : nat) (x : nat) (y : nat) :
  (b = true  -> x <=(c1) z) ->
  (b = false -> y <=(c2) z) ->
  match b with
  | true => x
  | false => y
  end <=(max c1 c2) z .
Proof with reflexivity + apply Nat.mul_le_mono; eauto using Nat.le_max_r,Nat.le_max_l.
  intros H1 H2. unfold dominatedWith in *.
  destruct b.
  - rewrite H1...
  - rewrite H2...
Qed.

Smpl Add 12
     match goal with
     | [ |- (match _ with true => _ | false => _ end) <=(_) _ ] =>
       let H := fresh in (eapply dominatedWith_match_bool; [intros H |intros H]); try rewrite !H
     end : domWith_match.



Lemma dominatedWith_mono_c x y c c':
  x <=(c) y ->
  c <= c' ->
  x <=(c') y.
Proof.
  intros H1 H2. unfold dominatedWith in *. now rewrite <- H2.
Qed.


Lemma dominatedWith_refl (c x : nat) : c > 0 -> x <=(c) x.
Proof.
  intros H.
  induction c.
  - omega.
  - hnf. cbn. lia.
Qed.


Ltac pose_nice L H c:=
  pose proof (proj2_sig L) as H;
  unfold dominatedWith in H;
  pose (c := proj1_sig L);
  match type of H with
    context C [proj1_sig L] =>
    let H' := context C[c] in
    change H' in H
  end.
