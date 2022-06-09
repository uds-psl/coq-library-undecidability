(*
  Autor(s):
    Andrej Dudenhefner (1)
  Affiliation(s):
    (1) Saarland University, Saarbrücken, Germany
*)

(* 
  Reduction from:
    Uniform Diophantine Constraint Solvability (H10UC_SAT)
  via:
    Finite Multiset Term Constraint Solvability (FMsetTC_SAT)
  to:
    Finite Multiset Constraint Solvability (FMsetC_SAT)
*)

Require Import Arith Lia List Permutation.
Require Cantor.
Import ListNotations.

Require Import Undecidability.SetConstraints.FMsetC.
Require Import Undecidability.SetConstraints.Util.Facts.

Require Undecidability.DiophantineConstraints.H10C.
Import H10C (H10UC_SAT).
Require Import Undecidability.Synthetic.Definitions.
(*
Require Import Undecidability.Synthetic.ReducibilityFacts.
*)
Require Import ssreflect ssrbool ssrfun.

Set Default Goal Selector "!".

Local Notation "A ≡ B" := (mset_eq A B) (at level 65).
Local Notation "A ~p B" := (Permutation A B) (at level 65).

(* reduction from H10UC_SAT to FMsetTC_SAT *)
Module H10UC_FMsetTC. 

(* terms *)
Inductive mset_term : Set :=
  | mset_term_zero : mset_term
  | mset_term_var : nat -> mset_term
  | mset_term_plus : mset_term -> mset_term -> mset_term
  | mset_term_h : mset_term -> mset_term.

Definition constraint : Set := mset_term * mset_term.

(* evaluate an mset wrt. a valuation φ *)
Fixpoint mset_sem (φ : nat -> list nat) (A : mset_term) : list nat :=
  match A with
    | mset_term_zero => [0]
    | mset_term_var x => φ x
    | mset_term_plus A B => (mset_sem φ A) ++ (mset_sem φ B)
    | mset_term_h A => map S (mset_sem φ A)
  end.

(* does the valuation φ that satisfy all contraints *)
Definition mset_sat (φ : nat -> list nat) (l : list constraint) := 
  Forall (fun '(A, B) => Permutation (mset_sem φ A) (mset_sem φ B)) l.

(* is there a valuation φ that satisfies all contraints *)
Definition FMsetTC_SAT (l: list constraint) := 
  exists (φ : nat -> list nat), mset_sat φ l.

Module Argument.

Local Notation "t ⊍ u" := (mset_term_plus t u) (at level 40).
Local Notation "'h' t" := (mset_term_h t) (at level 38).
Local Notation "•0" := mset_term_zero.

Local Coercion mset_term_var : nat >-> mset_term.

(* interpret a multiset as a polynomial at p *)
Definition eval p A := list_sum (map (Nat.pow p) A).

Lemma eval_eq {p A B} : A ~p B -> eval p A = eval p B.
Proof.
  elim: A B. { by move=> ? /Permutation_nil ->. }
  move=> a A IH B /[dup] /(Permutation_in a) /(_ (in_eq _ _)).
  move=> /(@in_split nat) [B1 [B2 ->]].
  move=> /(@Permutation_cons_app_inv nat) /IH.
  rewrite /eval !map_app !list_sum_app /=. lia.
Qed.

Lemma eval_monotone {p q A} : p < q -> eval p A < eval q A \/ Forall (fun a => 0 = a) A.
Proof.
  move=> Hpq. elim: A; first by right.
  rewrite /eval. move=> [|n] A [IH|IH].
  - left => /=. lia.
  - right. by constructor.
  - left. have := Nat.pow_lt_mono_l p q (S n) (Nat.neq_succ_0 n) Hpq.
    move=> /=. lia.
  - left. have := Nat.pow_lt_mono_l p q (S n) (Nat.neq_succ_0 n) Hpq.
    move=> /= ?.
    have -> : list_sum (map (Nat.pow p) A) = list_sum (map (Nat.pow q) A).
    { elim: A IH; first done.
      by move=> m A IH /Forall_cons_iff [<- /IH] /= ->. }
    by lia.
Qed.

(* nat constraints are only satisfied by multisets containing only zeroes *)
Lemma nat_spec {n A B C} : 
  (map S B) ++ A ~p [n] ++ B ++ B ++ B ++ B ->
  (map S (map S C)) ++ A ~p [2*n] ++ C ++ C ++ C ++ C ->
  Forall (fun a => 0 = a) A.
Proof.
  have eval_map p' A' : eval p' (map S A') = p' * eval p' A'.
  { rewrite /eval. elim: A'; first done.
    move=> > /= ->. by nia. }
  move=> /(eval_eq (p := 4)) + /(eval_eq (p := 2)).
  rewrite /eval !map_app !list_sum_app -!/(eval _ _) !eval_map.
  have -> : eval 2 [2 * n] = eval 4 [n]. 
  { have := Nat.pow_mul_r 2 2 n. rewrite /eval /=. lia. }
  move=> ??.
  have : not (eval 2 A < eval 4 A) by lia.
  by have /(eval_monotone (A := A)) [] : 2 < 4 by lia.
Qed.

Fixpoint tower m n :=
  match n with 
  | 0 => []
  | S n => (tower m n) ++ (tower m n) ++ (tower m n) ++ (tower m n) ++ [m*n]
  end.

Lemma nat_sat {m n} :
  (map (fun i => m + i) (tower m n)) ++ (repeat 0 (4^n)) ~p [m*n] ++ (tower m n) ++ (tower m n) ++ (tower m n) ++ (tower m n).
Proof.
  elim: n; first by rewrite Nat.mul_0_r.
  move=> n IH /=. rewrite ?map_app ?repeat_app /= app_nil_r.
  pose L := (map (fun i => m + i) (tower m n)) ++ (repeat 0 (4^n)).
  pose R := [m*n] ++ (tower m n) ++ (tower m n) ++ (tower m n) ++ (tower m n).
  have -> : m + m * n = m * (S n) by nia.
  apply: (Permutation_trans (l' := (L ++ L ++ L ++ L) ++ [m * S n])).
  { rewrite /L. by Permutation_trivial. }
  apply /Permutation_sym /(Permutation_elt [] _ _ []).
  rewrite /L IH. by Permutation_trivial.
Qed.

(* forces instance to be a sequence *)
(* first constraint of encode bound *)
(* type 1 constraint *)
Lemma seq_spec2 {d A B} : A ++ B ~p [0] ++ (map (fun i => (S d) + i) A) ->
  exists n, A ~p map (fun i => (S d) * i) (seq 0 n) /\ B = [(S d) * n].
Proof.
  suff : forall k, A ++ B ~p [(1+d) * k] ++ (map (fun i => (1 + d) + i) A) ->
    A ~p map (fun i => (1+d) * i) (seq k (length A)) /\ B = [(1+d) * (k + length A)].
  { have ->: [0] = [(1+d) * 0] by (congr cons; lia).
    move=> /[apply] ?. by exists (length A). }
  move=> k. elim /(measure_rect (@length nat)) : A k => A IH k H.
  move: (H) => /Permutation_length. rewrite ?app_length map_length /= => HAB.
  have [b Hb] : exists b, B = [b].
  { move: (B) HAB => [|? [|? ?]] /=; [ by lia | by eexists | by lia ]. }
  subst B.
  move: (H) => /Permutation_sym /(Permutation_in ((1 + d) * k)) /(_ (in_eq _ _)) /in_app_iff [].
  - move /(@in_split nat) => [A1 [A2 ?]]. subst A.
    have := IH (A1 ++ A2). apply: unnest.
    { rewrite ?app_length /=. by lia. }
    move=> /(_ (1+k)). apply: unnest.
    { move: H. rewrite !map_app /= -!app_assoc /=.
      move=> /Permutation_sym /(@Permutation_cons_app_inv nat) <-.
      have -> : S (k + d * S k) = S (d + (k + d * k)) by lia.
      by apply /Permutation_sym /Permutation_middle. }
    move=> {IH} [IH ->]. constructor.
    + have ->: length (A1 ++ (1 + d) * k :: A2) = 1 + length (A1 ++ A2).
      { rewrite ?app_length /=. by lia. }
      rewrite /= -IH. by apply /Permutation_sym /Permutation_middle.
    + congr cons. rewrite !app_length /=. by lia.
  - case; last done. move=> ?. subst b.
    move: H => /Permutation_sym /(Permutation_cons_app_inv _ [] (A := nat)).
    rewrite app_nil_r.
    move=> /Permutation_map_lt_nil ->; first by lia.
    constructor=> /=; first done.
    congr cons. by lia.
Qed.

(* type 1 constraint satisfied by any sequence *)
Lemma seq_sat2 {d n} : 
  let A n := map (fun i => (S d) * i) (seq 0 n) in
  (A n) ++ [(S d) * n] ~p [0] ++ (map (fun i => (S d) + i) (A n)).
Proof.
  move=> A. elim: n. { apply: Permutation_refl'. congr cons. by lia. }
  move=> n IH.
  rewrite /A seq_last ?map_app -/(A n) /(map _ [n]) IH.
  have ->: S d * S n = S d + S d * n by lia.
  by Permutation_trivial.
Qed.

Lemma seq_sat1 {n} : 
  (seq 0 n) ++ [n] ~p [0] ++ (map S (seq 0 n)).
Proof.
  have -> : S = (fun i => (S 0) + i) by done.
  have -> : seq 0 n = map (fun i => (S 0) * i) (seq 0 n).
  { elim: (seq 0 n); first done.
    move=> ??? /=. rewrite Nat.add_0_r. by congr cons. }
  have -> : [n] = [1*n] by (congr cons; lia).
  by apply: seq_sat2.
Qed.

Definition unify_sat n :
  {A | A ++ (map (fun i => 2*i) (seq 0 n)) ~p (seq 0 n) ++ map S A}.
Proof.
  elim: n; first by exists [].
  set f := (fun i => 2*i). move=> n [A HA]. exists (A ++ seq n n).
  rewrite ?seq_last ?map_app /=.
  apply: (Permutation_trans (l' := (A ++ map f (seq 0 n)) ++ (seq n n ++ [f n]))).
  { by Permutation_trivial. }
  apply: (Permutation_trans _ (l' := (seq 0 n ++ map S A) ++ ([n] ++ map S (seq n n)))); first last.
  { by Permutation_trivial. }
  have ->: f n = n + n by (rewrite /f; lia).
  by rewrite HA /f seq_shift -seq_last.
Qed.

(* embed nat^3 into nat to provide fresh variables *)
Definition embed '(x, y, z) := Cantor.to_nat (Cantor.to_nat (x, y), z).
Definition unembed n := let (xy, z) := Cantor.of_nat n in
  (Cantor.of_nat xy, z).

Lemma embed_unembed {xyz} : unembed (embed xyz) = xyz.
Proof. 
  case: xyz. case. move=> >.
  by rewrite /embed /unembed ?Cantor.cancel_of_to.
Qed.

Opaque embed unembed.

Definition encode_bound (x: nat): list constraint :=
  let X n := embed (x, n, 0) in
    [
      ((X 1) ⊍ (X 2), •0 ⊍ (h (X 1))); (* X 1 = [0..n-1], X 2 = [n] *)
      ((X 3) ⊍ (X 4), •0 ⊍ (h (h (X 3)))); (* X 3 = [0,2,..2*(m-1)], X 4 = [2*m] *)
      ((X 5) ⊍ (X 3), (X 1) ⊍ (h (X 5))); (* n = m *)
      ((h (X 6)) ⊍ (X 0), (X 2) ⊍ ((X 6) ⊍ ((X 6) ⊍ ((X 6) ⊍ (X 6)))));
      ((h (h (X 7))) ⊍ (X 0), (X 4) ⊍ ((X 7) ⊍ ((X 7) ⊍ ((X 7) ⊍ (X 7))))) (* X 0 = [0..0] of length 2^n *)
    ].

Definition encode_bound_spec {φ x} : mset_sat φ (encode_bound x) -> 
  Forall (fun a => 0 = a) (φ (embed (x, 0, 0))).
Proof.
  rewrite /encode_bound /mset_sat !Forall_cons_iff Forall_nil_iff /mset_sem.
  have -> (A) : map S (map S A) = map (fun i => (S 1) + i) A by rewrite map_map.
  have -> : map S = map [eta Nat.add 1] by done.
  move=> [/seq_spec2 [n [-> ->]]].
  move=> [/seq_spec2 [m [-> ->]]].
  move=> [/Permutation_length]. rewrite !app_length !map_length !seq_length => ?.
  have <- : n = m by lia. clear.
  have -> : 1 * n = n by lia.
  move=> [H1 [H2 _]]. by apply: nat_spec; eassumption.
Qed.

(* [0] ++ [0,1] ++ [0,1,2] ++ ...*)
Definition pyramid n := flat_map (seq 0) (seq 0 n).

(* from a H10UC valuation φ construct a valuation for FMsetC *)
Definition construct_valuation (φ: nat -> nat) (n: nat): list nat :=
  match unembed n with
  | (x, 0, 0) => repeat 0 (4^(φ x))
  | (x, 1, 0) => seq 0 (φ x)
  | (x, 2, 0) => [(φ x)]
  | (x, 3, 0) => map (fun i => 2*i) (seq 0 (φ x))
  | (x, 4, 0) => [2*(φ x)]
  | (x, 5, 0) => proj1_sig (unify_sat (φ x))
  | (x, 6, 0) => tower 1 (φ x)
  | (x, 7, 0) => tower 2 (φ x)
  | (x, 0, 1) => repeat 0 (φ x)
  | (x, 1, 1) => repeat 0 (length (pyramid (φ x)))
  | (x, 2, 1) => repeat 0 (4^(φ x) - (φ x))
  | (x, 3, 1) => repeat 0 (4^(φ x) - (length (pyramid (φ x))))
  | (x, 4, 1) => seq 0 (φ x)
  | (x, 5, 1) => [(φ x)]
  | (x, 6, 1) => pyramid (φ x)
  | (x, 7, 1) => flat_map pyramid (seq 0 (φ x))
  | _ => []
  end.


Lemma encode_bound_sat {φ x} : 
  mset_sat (construct_valuation φ) (encode_bound x).
Proof.
  rewrite /encode_bound /mset_sat !Forall_cons_iff Forall_nil_iff /mset_sem.
  rewrite /construct_valuation ? embed_unembed.
  pose A d n := map (fun i => (S d) * i) (seq 0 n).
  constructor; first by apply: seq_sat1.
  constructor.
  { have -> (X) : map S (map S X) = map (fun i => 2+i) X by rewrite map_map.
    by apply: seq_sat2. }
  constructor; first by apply: proj2_sig (unify_sat _).
  constructor.
  { have -> (n): [n] = [1*n] by rewrite Nat.mul_1_l.
    by apply: nat_sat. }
  constructor; [|done].
  rewrite map_map. by apply: nat_sat.
Qed.

(* each n : nat is represented by a multiset containing n zeroes *)
Definition encode_nat (x: nat) : list constraint :=
  let X n := embed (x, n, 1) in
    [
      (X 0 ⊍ X 2, mset_term_var (embed (x, 0, 0))); (* X 0 = [0..0] *)
      (X 1 ⊍ X 3, mset_term_var (embed (x, 0, 0))); (* X 1 = [0..0] *)
      (X 4 ⊍ X 5, •0 ⊍ (h (X 4))); (* X 4 = [0..m-1], X 5 = [m]*)
      (X 4 ⊍ X 6, X 0 ⊍ (h (X 6))); (* m = length (X 0), length (X 6) ~ m * m *)
      (X 6 ⊍ X 7, X 1 ⊍ (h (X 7))) (* length X 1 ~ m * m *)
    ].

(* auxiliary lemma for square_spec *)
Lemma square_spec_aux {n m A C} : C ++ (n :: A) ~p (repeat 0 (S m)) ++ (map S A) -> 
  exists A', A ~p (seq 0 n) ++ A' /\ C ++ A' ~p (repeat 0 m) ++ (map S A').
Proof.
  elim: n A.
  { move=> A /= /Permutation_sym /(@Permutation_cons_app_inv nat) /Permutation_sym H.
    by exists A. }
  move=> n IH A /[dup] /(Permutation_in (S n)).
  apply: unnest. { apply /in_app_iff => /=. tauto. }
  case /in_app_iff. { by move=> /(@repeat_spec nat). }
  move=> /in_map_iff [?] [[->]] /(@in_split nat) [A1 [A2 ?]]. subst A.
  move=> /(Permutation_trans _ (l := S n :: (C ++ (n :: (A1 ++ A2))))).
  apply: unnest. { by Permutation_trivial. }
  move=> /Permutation_sym /(Permutation_trans _ (l := S n :: ((repeat 0 (S m)) ++ map S (A1 ++ A2)))).
  apply: unnest. { rewrite !map_app /=. by Permutation_trivial. }
  move=> /Permutation_sym /(@Permutation_cons_inv nat) /IH [A' [? ?]].
  exists A'. constructor; last done.
  rewrite seq_last -app_assoc. by apply: Permutation_elt.
Qed.

(* forces B to be a n zeroes and A to be of length in proportion to n squared *)
Lemma square_spec {n A} : (seq 0 n) ++ A ~p (repeat 0 n) ++ (map S A) -> 
  length A + length A + n = n * n.
Proof.
  elim: n A.
  { move=> A /Permutation_sym /Permutation_map_lt_nil ->; by [|lia]. }
  move=> n IH A. rewrite seq_last.
  rewrite -app_assoc.
  move=> /square_spec_aux [A' [/Permutation_length + /IH]].
  rewrite app_length seq_length. by lia. 
Qed.

(* if encode bound is satisfied, then there is a square relationship on length of solutions *)
Lemma encode_nat_spec {φ x} : mset_sat φ (encode_bound x) -> mset_sat φ (encode_nat x) -> 
  length (φ (embed (x, 1, 1))) + length (φ (embed (x, 1, 1))) + length (φ (embed (x, 0, 1))) = 
    length (φ (embed (x, 0, 1))) * length (φ (embed (x, 0, 1))).
Proof.
  move /encode_bound_spec. rewrite /mset_sat /encode_nat ?Forall_cons_iff Forall_nil_iff /mset_sem.
  pose X n := φ (embed (x, n, 1)). rewrite -?/(X _).
  move=> /(@Forall_eq_repeat nat) ->. move: (length (φ _)) => m.
  move=> [/(Permutation_repeat 0) H1] [/(Permutation_repeat 0) H2].
  have -> : map S (X 4) = map [eta Init.Nat.add 1] (X 4) by done.
  move=> [/seq_spec2 [n]]. rewrite (map_id' _ (seq 0 n)); [lia|].
  move=> [->] _ [].
  have -> : X 0 = repeat 0 (length (X 0)).
  { elim: (X 0) (m) H1; [done|].
    move=> ?? /= IH [|m'] /=; [done|].
    move=> [-> /IH] ->. by rewrite repeat_length. }
  move=> /[dup] H3. rewrite repeat_length.
  have -> : length (X 0) = n.
  { move: H3 => /Permutation_length. rewrite !app_length map_length seq_length repeat_length. by lia. }
  move=> /square_spec <- [/Permutation_length]. rewrite !app_length map_length. by lia.
Qed.

Lemma pyramid_shuffle {n} : seq 0 n ++ pyramid n ~p repeat 0 n ++ map S (pyramid n).
Proof.
  elim: n; first done.
  move=> n IH.
  rewrite /pyramid seq_last /plus flat_map_concat_map map_app concat_app.
  rewrite -flat_map_concat_map -/(pyramid _) ? map_app /= ? app_nil_r seq_shift.
  apply: (Permutation_trans (l' := (seq 0 n ++ [n]) ++ (seq 0 n ++ pyramid n))).
  { by Permutation_trivial. }
  rewrite IH -seq_last /=.
  by Permutation_trivial.
Qed.

Lemma pyramid_length n : n + length (pyramid n) <= 4 ^ n.
Proof.
  elim: n; first by (move=> /=; lia).
  move=> n IH. 
  rewrite /pyramid seq_last /plus -/plus flat_map_concat_map map_app concat_app app_length.
  rewrite -flat_map_concat_map -/(pyramid _).
  rewrite /map /concat app_length seq_length /=.
  have := Nat.pow_gt_lin_r 4 n.
  by lia.
Qed.

Lemma encode_nat_sat_aux {n} : 
  pyramid n ++ flat_map pyramid (seq 0 n) ~p repeat 0 (length (pyramid n)) ++ (map S (flat_map pyramid (seq 0 n))).
Proof.
  elim: n; first done.
  move=> n IH.
  rewrite /pyramid ? seq_last /plus ? (flat_map_concat_map, map_app, concat_app, app_length).
  rewrite -?flat_map_concat_map -/pyramid -/(pyramid _) ?repeat_app seq_length /= ?app_nil_r.
  apply: (Permutation_trans (l' := (pyramid n ++ flat_map pyramid (seq 0 n)) ++ (seq 0 n ++ pyramid n))).
  { by Permutation_trivial. }
  rewrite pyramid_shuffle IH.
  by Permutation_trivial.
Qed.

Lemma encode_nat_sat {φ x} : 
  mset_sat (construct_valuation φ) (encode_nat x).
Proof.
  rewrite /encode_nat /mset_sat !Forall_cons_iff Forall_nil_iff /mset_sem /construct_valuation ?embed_unembed.
  rewrite -?repeat_app.
  constructor.
  { apply: Permutation_refl'. congr repeat. have := pyramid_length (φ x). by lia. }
  constructor.
  { apply: Permutation_refl'. congr repeat. have := pyramid_length (φ x). by lia. }
  constructor; first by apply: seq_sat1.
  constructor; first by apply: pyramid_shuffle.
  constructor; last done.
  by apply: encode_nat_sat_aux.
Qed.

(* represent constraints of shape 1 + x + y * y = z *)
Definition encode_constraint x y z := 
  encode_bound x ++ encode_bound y ++ encode_bound z ++ 
  encode_nat x ++ encode_nat y ++ encode_nat z ++ 
  let x := embed (x, 0, 1) in
  let yy := embed (y, 1, 1) in
  let y := embed (y, 0, 1) in
  let z := embed (z, 0, 1) in
  [ (•0 ⊍ x ⊍ yy ⊍ yy ⊍ y, mset_term_var z) ].

(* if mset constraint has a solution, then uniform diophantine constraint is satisfied *)
Lemma encode_constraint_spec {φ x y z} :  
  mset_sat φ (encode_constraint x y z) -> 
  1 + length (φ (embed (x, 0, 1))) + length(φ (embed (y, 0, 1))) * length(φ (embed (y, 0, 1))) = length(φ (embed (z, 0, 1))).
Proof.
  rewrite /encode_constraint /mset_sat ?Forall_app -?/(mset_sat _ _).
  move=> [Hx [Hy [Hz]]].
  move=> [/(encode_nat_spec Hx) ? [/(encode_nat_spec Hy) ? [/(encode_nat_spec Hz) ?]]].
  rewrite /mset_sat Forall_cons_iff Forall_nil_iff /mset_sem.
  move=> [/Permutation_length]. rewrite ? app_length /=. by lia.
Qed.

(* if uniform diophantine constraint is satisfied, then mset constraint has a solution *)
Lemma encode_constraint_sat {φ x y z} : 
  1 + (φ x) + (φ y) * (φ y) = (φ z) -> mset_sat (construct_valuation φ) (encode_constraint x y z).
Proof.
  move=> Hxyz.
  rewrite /encode_constraint /mset_sat ?Forall_app -?/(mset_sat _ _).
  do 3 (constructor; first by apply: encode_bound_sat).
  do 3 (constructor; first by apply: encode_nat_sat).
  constructor; last done.
  rewrite /mset_sem /construct_valuation ? embed_unembed.
  have ->: [0] = repeat 0 1 by done.
  rewrite -?repeat_app. apply: Permutation_refl'. congr repeat.
  move: Hxyz=> <-. clear. 
  elim: (φ y); clear; first by (move=> /=; lia).
  move=> φy IH. 
  rewrite /pyramid seq_last /(plus 0 _) flat_map_concat_map map_app concat_app.
  rewrite -flat_map_concat_map -/(pyramid _) /= ?app_length seq_length /=. by lia.
Qed.

(* encode a single H10UC constraint as a list of FMsetC constraints *)
Definition encode_h10uc '(x, y, z) := encode_constraint x y z.

End Argument.

(* many-one reduction from H10UC to FMsetC *)
Theorem reduction : H10UC_SAT ⪯ FMsetTC_SAT.
Proof.
  exists (fun h10ucs => flat_map Argument.encode_h10uc h10ucs).
  move=> h10ucs. constructor.
  - move=> [φ Hφ]. 
    exists (Argument.construct_valuation φ).
    elim: h10ucs Hφ; first by constructor.
    move=> [[x y] z] h10cs IH.
    move /Forall_forall. rewrite Forall_cons_iff. move=> [Hxyz /Forall_forall /IH].
    move=> {}IH. apply /Forall_app. constructor; last done.
    by apply: Argument.encode_constraint_sat.
  - move=> [φ] Hφ.
    pose ψ := (fun x => length (φ (Argument.embed (x, 0, 1)))).
    exists ψ. rewrite -Forall_forall.
    elim: h10ucs Hφ; first done.
    move=> [[x y] z] h10ucs IH. 
    rewrite /flat_map -/(flat_map _) /mset_sat Forall_app /(Argument.encode_h10uc _).
    move=> [/Argument.encode_constraint_spec Hxyz /IH ?].
    by constructor.
Qed.

End H10UC_FMsetTC.

(* reduction from FMsetTC_SAT to FMsetC_SAT *)
Module FMsetTC_FMsetC.

Import H10UC_FMsetTC.

Module Argument.

Opaque Cantor.to_nat Cantor.of_nat.
Fixpoint term_to_nat (t: mset_term) : nat :=
  match t with
  | mset_term_zero => 1 + Cantor.to_nat (0, 0)
  | mset_term_var x => 1 + Cantor.to_nat (0, 1+x)
  | mset_term_plus t u => 1 + Cantor.to_nat (1 + term_to_nat t, 1 + term_to_nat u)
  | mset_term_h t => 1 + Cantor.to_nat (1 + term_to_nat t, 0)
  end.

Fixpoint nat_to_term' (k: nat) (n: nat) : mset_term :=
  match k with
  | 0 => mset_term_zero
  | S k =>
    match n with
    | 0 => mset_term_zero
    | S n => 
      match Cantor.of_nat n with
      | (0, 0) => mset_term_zero
      | (0, S x) => mset_term_var x
      | (S nt, 0) => mset_term_h (nat_to_term' k nt)
      | (S nt, S nu) => mset_term_plus (nat_to_term' k nt) (nat_to_term' k nu)
      end
    end
  end.

Definition nat_to_term (n: nat) : mset_term := nat_to_term' (1+n) n.

Lemma nat_term_cancel {t} : nat_to_term (term_to_nat t) = t.
Proof.
  rewrite /nat_to_term.
  move Hk: (k in nat_to_term' (1 + k) _) => k.
  have : term_to_nat t <= k by lia.
  elim: t k {Hk}.
  - done.
  - move=> x k /=. by rewrite Cantor.cancel_of_to.
  - move=> nt IHt nu IHu k /=.
    rewrite Cantor.cancel_of_to => ?.
    have ? := Cantor.to_nat_non_decreasing (S (term_to_nat nt)) (S (term_to_nat nu)).
    have -> : k = S (k - 1) by lia.
    rewrite IHt; first by lia. by rewrite IHu; first by lia.
  - move=> nt IH k /=. rewrite Cantor.cancel_of_to => ?.
    have ? := Cantor.to_nat_non_decreasing (S (term_to_nat nt)) 0.
    have -> : k = S (k - 1) by lia.
    by rewrite IH; first by lia.
Qed.

Lemma term_to_nat_pos t : term_to_nat t = S (Nat.pred (term_to_nat t)).
Proof. by case: t. Qed.

Opaque nat_to_term term_to_nat.

(* decompose mset_term into elementary constraints *)
Fixpoint term_to_msetcs (t: mset_term) : list msetc :=
  match t with
  | mset_term_zero => [msetc_zero (term_to_nat t)]
  | mset_term_var x => []
  | mset_term_plus u v => 
      [msetc_sum (term_to_nat t) (term_to_nat u) (term_to_nat v)] ++ 
      (term_to_msetcs u) ++ (term_to_msetcs v)
  | mset_term_h u => 
      [msetc_h (term_to_nat t) (term_to_nat u)] ++ (term_to_msetcs u)
  end.

Definition encode_eq (t u: mset_term) :=
  [(msetc_sum 0 0 0); 
  (msetc_sum (term_to_nat t) 0 (term_to_nat u))].

(* encode FMsetC_PROBLEM as LPolyNC_PROBLEM *)
Definition encode_problem (msetcs : list constraint) : list msetc :=
  flat_map (fun '(t, u) => (encode_eq t u) ++ term_to_msetcs t ++ term_to_msetcs u) msetcs.

Lemma completeness {l} : FMsetTC_SAT l -> FMsetC_SAT (encode_problem l).
Proof.
  move=> [φ] Hφ.
  pose ψ x := if x is 0 then [] else mset_sem φ (nat_to_term x).
  have H'ψ (A) : ψ (term_to_nat A) = mset_sem φ A.
  { by rewrite /ψ nat_term_cancel term_to_nat_pos. }
  have Hψ (A) : Forall (msetc_sem ψ) (term_to_msetcs A).
  { elim: A.
    - by constructor.
    - by rewrite /term_to_msetcs.
    - move=> A IHA B IHB /=. constructor; last by apply /Forall_app.
      by rewrite /msetc_sem !H'ψ.
    - move=> A IH /=. constructor; last done.
      by rewrite /msetc_sem !H'ψ. }
  exists ψ.
  rewrite -Forall_forall /encode_problem Forall_flat_map.
  apply: Forall_impl; last eassumption. 
  move=> [A B] HφAB. apply /Forall_app.
  split; last by apply /Forall_app.
  constructor; [done|constructor;[|done]].
  rewrite /msetc_sem !H'ψ. by apply /Permutation_count_occ.
Qed.

Lemma soundness {l} : FMsetC_SAT (encode_problem l) -> FMsetTC_SAT l.
Proof.
  move=> [ψ]. rewrite -Forall_forall Forall_flat_map => Hψ.
  pose φ x := ψ (term_to_nat (mset_term_var x)).
  exists φ.
  apply: Forall_impl; last by eassumption.
  move=> [t u] /Forall_app [/Forall_cons_iff [+] /Forall_cons_iff [+ _]] /Forall_app [] => /=.
  move=> /Permutation_count_occ /(Permutation_app_inv_r _ []) /Permutation_nil -> /=.
  move=> /Permutation_count_occ Hψtu.
  have Hφ (s) : Forall (msetc_sem ψ) (term_to_msetcs s) -> Permutation (mset_sem φ s) (ψ (term_to_nat s)).
  { clear. elim: s.
    - by move=> /Forall_cons_iff /= [] /Permutation_count_occ ->.
    - done.
    - move=> t IHt u IHu /= /Forall_cons_iff /= [/Permutation_count_occ ->].
      by move=> /Forall_app [/IHt -> /IHu ->].
    - move=> t IH /= /Forall_cons_iff /= [/Permutation_count_occ ->].
      by move=> /IH /Permutation_map. }
  by move=> /Hφ -> /Hφ ->.
Qed.

End Argument.

(* many-one reduction from FMsetTC to FMsetC *)
Theorem reduction : FMsetTC_SAT ⪯ FMsetC_SAT.
Proof.
  exists Argument.encode_problem.
  move=> cs. constructor.
  - exact Argument.completeness.
  - exact Argument.soundness.
Qed.

End FMsetTC_FMsetC.

Theorem reduction : H10UC_SAT ⪯ FMsetC_SAT.
Proof.
  have [f Hf] := H10UC_FMsetTC.reduction.
  have [g Hg] := FMsetTC_FMsetC.reduction.
  exists (fun x => g (f x)) => ?. by rewrite Hf Hg.
Qed.
