(* 
  Autor(s):
    Andrej Dudenhefner (1) 
  Affiliation(s):
    (1) Saarland Informatics Campus, Saarland University, Saarbrücken, Germany
*)

(* 
  Reduction from:
    Uniform H10 constraint solvability (H10UC)
  to:
    Finite multiset constraint solvability (FMsetC)
  
  References:
    [1] Paliath Narendran: Solving Linear Equations over Polynomial Semirings.
      LICS 1996: 466-472, doi: 10.1109/LICS.1996.561463
*)

Require Import ssreflect ssrbool ssrfun.
Require Import Arith Psatz.
Require Import List.
Import ListNotations.

From Undecidability Require Import Problems.FMsetC Problems.H10UC Problems.Reduction.
From Undecidability Require Import 
  FMset.mset_utils FMset.mset_eq_utils FMset.mset_poly_utils FMset.mset_term_utils.

(* 
  auxiliary soundness and completeness lemmas 
  for the reduction from H10UC to FMsetC
*)

(* nat constraints are only satisfied by multisets containing only zeroes *)
Lemma nat_spec {n A B C} : 
  (map S B) ++ A ≡ [n] ++ B ++ B ++ B ++ B ->
  (map S (map S C)) ++ A ≡ [2*n] ++ C ++ C ++ C ++ C ->
  Forall (fun a => 0 = a) A.
Proof.
  move=> /(eval_eq (p := 4)) + /(eval_eq (p := 2)).
  rewrite ? eval_norm ? eval_map Nat.pow_mul_r.
  move=> /= ? ?.
  have : eval 2 A = eval 4 A by lia.
  apply /eval_nat_spec.
  by lia.
Qed.

Fixpoint tower m n :=
  match n with 
  | 0 => []
  | S n => (tower m n) ++ (tower m n) ++ (tower m n) ++ (tower m n) ++ [m*n]
  end.

Lemma nat_sat {m n} :
  (map (fun i => m + i) (tower m n)) ++ (repeat 0 (4^n)) ≡ [m*n] ++ (tower m n) ++ (tower m n) ++ (tower m n) ++ (tower m n).
Proof.
  elim: n.
    by (have -> : m * 0 = 0 by nia).
  move=> n IH /=. rewrite ? map_app ? repeat_add. cbn.
  pose L := (map (fun i => m + i) (tower m n)) ++ (repeat 0 (4^n)).
  pose R := [m*n] ++ (tower m n) ++ (tower m n) ++ (tower m n) ++ (tower m n).
  have -> : m + m * n = m * (S n) by nia.
  under (eq_lr (A' := (m * S n) :: (L ++ L ++ L ++ L)) (B' := (m * S n) :: (R ++ R ++ R ++ R))).
    by eq_trivial.
    by eq_trivial.
  rewrite -/(mset_eq _ _).
  apply /eq_cons_iff.
  do 3 (apply /eq_appI; first done).
  done.
Qed.

(* forces instance to be a sequence *)
(* first constraint of encode bound *)
(* type 1 constraint *)
Lemma seq_spec2 {d A B} : A ++ B ≡ [0] ++ (map (fun i => (S d) + i) A) ->
  exists n, A ≡ map (fun i => (S d) * i) (seq 0 n) /\ B = [(S d) * n].
Proof.
  move /copy => [/eq_length + +].
  rewrite ? app_length map_length => /= H.
  have : length B = 1 by lia. clear H.
  move /singleton_length => [n ? Heq]. subst B. 
  exists (n / (S d)).
  move: n Heq.
  elim /(measure_ind (@length nat)) : A => A.
  case: (nil_or_ex_max A).
    move=> -> _ n /= /eq_singletonE. case=> <-. constructor.
      done.
    cbn. f_equal. by nia.
  move=> [m [+ Hm]].
  move /(in_split _ _) => [A1 [A2 ?]]. subst A.
  move=> IH n.
  move /copy => [H +].
  have: n = (S d)+m.
    move : H.
    move /eq_in_iff /(_ ((S d)+m)) /iffRL.
    apply: unnest. 
      rewrite ? (in_app_iff, in_cons_iff, map_app, map_cons). by lia.
    rewrite in_app_iff. case.
      move: Hm => /Forall_forall. move=> + H. move /(_ _ H). by lia.
    rewrite /In /plus. by case.
  move=> ?. subst n.
  under (eq_lr (A' := ((S d) + m) :: (A1 ++ A2) ++ [m]) (B' := ((S d) + m) :: 0 :: map (fun i : nat => S (d + i)) (A1 ++ A2))).
  all: rewrite -/(mset_eq _ _).
    by eq_trivial.
    rewrite ? map_app map_cons /plus. by eq_trivial.
  move /eq_cons_iff /IH.
  apply: unnest.
    rewrite ? app_length => /=. by lia.
  move=> [IHA1A2].
  case. rewrite  -/(Nat.div m (S d)) - ? /(mult (S d) _).
  have -> : S d + m = 1 * S d + m by lia.
  rewrite Nat.div_add_l.
    by lia.
  rewrite seq_last map_app map_cons.
  have -> : S d * (1 + m / S d) = S d + S d * (m / S d) by lia.
  move=> IHm. rewrite  -/(Nat.div m (S d)) - ? /(mult (S d) _).
  rewrite /plus -/plus.  
  rewrite - ? IHm.
  constructor; first last.
    f_equal. by lia.
  under (eq_lr (A' := m :: (A1 ++ A2)) (B' := m :: map (fun i : nat => i + d * i) (seq 0 (m / S d)))).
  all: rewrite -/(mset_eq _ _).
    by eq_trivial.
    by eq_trivial.
  by apply /eq_cons_iff.
Qed.

(* type 1 constraint satisfied by any sequence *)
Lemma seq_sat2 {d n} : 
  let A n := map (fun i => (S d) * i) (seq 0 n) in
  (A n) ++ [(S d) * n] ≡ [0] ++ (map (fun i => (S d) + i) (A n)).
Proof.
  move=> A. elim: n.
    apply /eq_eq. cbn. f_equal. by nia.
  move=> n IH.
  rewrite /A seq_last ? map_app -/(A n) /plus -/plus.
  rewrite /(map _ [n]) /(map _ [S d * n]).
  have -> : S (d + S d * n) = S d * S n by lia.
  under map_ext => i. rewrite -/(plus (S d) i). over.
  rewrite -/(mset_eq _ _).
  under (eq_lr 
    (A' := S d * S n :: (A n ++ [S d * n])) 
    (B' := S d * S n :: ([0] ++ map [eta Init.Nat.add (S d)] (A n)))).
    by eq_trivial.
    by eq_trivial.
  rewrite -/(mset_eq _ _).
  by apply /eq_cons_iff.
Qed.

Lemma seq_sat1 {n} : 
  (seq 0 n) ++ [n] ≡ [0] ++ (map S (seq 0 n)).
Proof.
  have -> : S = (fun i => (S 0) + i) by done.
  have -> : seq 0 n = map (fun i => (S 0) * i) (seq 0 n).
    elim: n.
      done.
    move=> n IH. rewrite seq_last map_app - IH => /=.
    by rewrite Nat.add_0_r.
  have -> : [n] = [1*n] by f_equal; lia.
  by apply: seq_sat2.
Qed.

Lemma unify_spec {A m n} : A ++ (map (fun i => 2 * i) (seq 0 m)) ≡ (seq 0 n) ++ map S A ->
  n = m.
Proof.
  move /eq_length.
  rewrite ? app_length ? map_length ? seq_length.
  by lia.
Qed.

Lemma unify_sat_aux {B n} : 
  Forall2 (fun i j => i >= j) B (seq 0 n) -> {A | A ++ B ≡ (seq 0 n) ++ map S A}.
Proof.
  elim /(induction_ltof1 _ (fold_right (fun x y => S (x + y)) 0)) : B n.
  rewrite /ltof.
  move=> B.
  case (list_eq_dec Nat.eq_dec B []).
    move=> -> ? ? /Forall2_nil_lE ->. by exists [].
  move /exists_last=> [C [a HC]]. subst B. move => IH. case.
    move=> /Forall2_nil_rE /app_eq_nil. by case.
  move=> n. rewrite seq_last /plus. move /Forall2_lastP => [HC Ha].
  have := gt_eq_gt_dec n a. case; first case; first last.
    move=> ?. exfalso. by lia.
    move=> ?. subst a. move: (IH C).
    apply: unnest_t.
      clear. elim: C=> /= *; by lia. 
    move /(_ _ ltac:(eassumption)) => [A HA]. exists A.
    under (eq_lr (A' := n :: (A ++ C)) (B' := n :: (seq 0 n ++ map S A))).
      by eq_trivial.
      by eq_trivial.
    rewrite -/(mset_eq _ _). by apply /eq_cons_iff.
  move=> ?.
  have HaSPa : a = S (Nat.pred a) by lia.
  move: (IH (C ++ [Nat.pred a])).
  apply: unnest_t.
    move: HaSPa. clear. elim: C => /= [|? ? IH /IH] ?; by lia.
  move /(_ (S n)). apply: unnest_t.
    rewrite seq_last /plus. apply /Forall2_lastP. constructor; by [|lia].
  move=> [A HA]. exists ((Nat.pred a) :: A).
  rewrite -seq_last /(map) -/(map _ _) - HaSPa.
  under (eq_lr (A' := a :: (A ++ C ++ [Nat.pred a])) (B' := a :: (seq 0 (S n) ++ map S A))).
    by eq_trivial.
    by eq_trivial.
  rewrite -/(mset_eq _ _). by apply /eq_cons_iff.
Qed.

Definition unify_sat n :
  {A | A ++ (map (fun i => 2*i) (seq 0 n)) ≡ (seq 0 n) ++ map S A}.
Proof.
  apply: unify_sat_aux. elim: n.
    by constructor.
  move=> n IH. rewrite ? seq_last map_app. apply: Forall2_app.
    done.
  constructor.
    by lia.
  done.
Qed.

(* embed nat^3 into nat to provide fresh variables *)
Definition embed '(x, y, z) := NatNat.nat2_to_nat (NatNat.nat2_to_nat (x, y), z).
Definition unembed n := let (xy, z) := NatNat.nat_to_nat2 n in
  (NatNat.nat_to_nat2 xy, z).


Lemma embed_unembed {xyz} : unembed (embed xyz) = xyz.
Proof. 
  case: xyz. case. move=> >.
  by rewrite /embed /unembed ? NatNat.nat_nat2_cancel.
Qed.

Opaque embed unembed.

Definition encode_bound (x: nat): FMsetC_PROBLEM :=
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
  rewrite /encode_bound /mset_sat ? Forall_norm /mset_sem.
  have -> (A) : map S (map S A) = map (fun i => (S 1) + i) A.
    by rewrite map_map.
  have -> : map S = map [eta Nat.add 1] by done.

  move=> [/seq_spec2 [n [/eq_length Hn ->]]].
  move=> [/seq_spec2 [m [/eq_length Hm ->]]].
  move=> [/eq_length]. rewrite ? app_length Hn Hm ? map_length ? seq_length => ?.
  have ? : n = m by lia. subst m. clear.
  have -> : [eta Nat.add 1] = S by done.
  have -> : 1 * n = n by lia.
  move=> [H1 H2]. by apply: nat_spec.
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
  rewrite /encode_bound /mset_sat ? Forall_norm /mset_sem.
  rewrite /construct_valuation ? embed_unembed.
  pose A d n := map (fun i => (S d) * i) (seq 0 n).
  constructor.
    by apply: seq_sat1.
  constructor.
    have -> (X) : map S (map S X) = map (fun i => 2+i) X by rewrite map_map.
    by apply: seq_sat2.
  constructor.
    apply: proj2_sig (unify_sat _).
  constructor.
    have -> (n): [n] = [1*n] by f_equal; lia.
    by apply: nat_sat.
  rewrite map_map.
  by apply: nat_sat.
Qed.

(* each n : nat is represented by a multiset containing n zeroes *)
Definition encode_nat (x: nat) : FMsetC_PROBLEM :=
  let X n := embed (x, n, 1) in
    [
      (X 0 ⊍ X 2, mset_term_var (embed (x, 0, 0))); (* X 0 = [0..0] *)
      (X 1 ⊍ X 3, mset_term_var (embed (x, 0, 0))); (* X 1 = [0..0] *)
      (X 4 ⊍ X 5, •0 ⊍ (h (X 4))); (* X 4 = [0..m-1], X 5 = [m]*)
      (X 4 ⊍ X 6, X 0 ⊍ (h (X 6))); (* m = length (X 0), length (X 6) ~ m * m *)
      (X 6 ⊍ X 7, X 1 ⊍ (h (X 7))) (* length X 1 ~ m * m *)
    ].

(* auxiliary lemma for square_spec *)
Lemma square_spec_aux {n m A C} : C ++ (n :: A) ≡ (repeat 0 (S m)) ++ (map S A) -> 
exists A', A ≡ (seq 0 n) ++ A' /\ C ++ A' ≡ (repeat 0 m) ++ (map S A').
Proof.
elim: n A.
  move=> A. rewrite /repeat -/(repeat _).
  under (eq_lr (A' := 0 :: (C ++ A)) (B' := 0 :: ((repeat 0 m) ++ map S A))).
    by eq_trivial.
    by eq_trivial.
  move /eq_cons_iff=> ?. exists A. by constructor.
move=> n IH A /copy [/eq_in_iff /(_ (S n)) /iffLR].
apply: unnest. 
  apply /in_app_iff. right. by left.
move /in_app_iff. case.
  by move /(@repeat_spec _ _ _ _).
move /in_map_iff=> [n' [+ +]]. case=> ?. subst n'.
move /(@in_split _ _) => [A1 [A2 ?]]. subst A.

under (eq_lr (A' := S n :: (C ++ (n :: (A1 ++ A2)))) (B' := S n :: ((repeat 0 (S m)) ++ map S (A1 ++ A2)))).
  by eq_trivial.
  move=> c. rewrite ? map_app map_cons. move: c. by eq_trivial.
move /eq_cons_iff => /IH [A' [? ?]].
exists A'. constructor.
  rewrite seq_last.
  under (eq_lr (A' := n :: (A1 ++ A2)) (B' := n :: (seq 0 n ++ A'))).
    by eq_trivial.
    rewrite /plus. by eq_trivial.
  rewrite -/(mset_eq _ _). by apply /eq_cons_iff.
done.
Qed.

(* forces B to be a n zeroes and A to be of length in proportion to n squared *)
Lemma square_spec {n A} : (seq 0 n) ++ A ≡ (repeat 0 n) ++ (map S A) -> 
length A + length A + n = n * n.
Proof.
elim: n A.
  move=> A /=. by move=> /eq_symm /eq_mapE ->.
move=> n IH A. rewrite seq_last /plus -/plus.
under (eq_lr _ eq_refl (A' := seq 0 n ++ (n :: A))).
  by eq_trivial.
move /square_spec_aux => [A' [/eq_length + /IH]].
rewrite app_length seq_length. by lia. 
Qed.

(* if encode bound is satisfied, then there is a square relationship on length of solutions *)
Lemma encode_nat_spec {φ x} : mset_sat φ (encode_bound x) -> mset_sat φ (encode_nat x) -> 
  length (φ (embed (x, 1, 1))) + length (φ (embed (x, 1, 1))) + length (φ (embed (x, 0, 1))) = 
    length (φ (embed (x, 0, 1))) * length (φ (embed (x, 0, 1))).
Proof.
  move /encode_bound_spec.
  rewrite /mset_sat /encode_nat.
  rewrite ? Forall_norm /mset_sem.
  pose X n := φ (embed (x, n, 1)). rewrite - ? /(X _).
  move=> H.
  move=> [/eq_Forall_iff /(_ [eta eq 0]) /iffRL /(_ H)].
  rewrite Forall_norm=> [[HX0 _]].
  move=> [/eq_Forall_iff /(_ [eta eq 0]) /iffRL /(_ H)].
  rewrite Forall_norm=> [[? _]].
  have -> : map S (X 4) = map [eta Init.Nat.add 1] (X 4) by done.
  move=> [/seq_spec2 [n]].
  have -> : map [eta Init.Nat.mul 1] (seq 0 n) = map id (seq 0 n).
    under map_ext => i. have -> : 1*i = i by lia. over. done.
  rewrite map_id => [[Hn _]].
  move=> [/eq_symm /eq_trans] => /(_ ((seq 0 n) ++ X 6)). apply: unnest.
    by apply: eq_appI.
  move => HX6. have HlX0 : length (X 0) = n.
    move: HX6 => /eq_length. rewrite ? app_length map_length seq_length. by lia.
  move: HX6 => /eq_symm. have -> := Forall_repeat HX0. rewrite HlX0. 
  move /square_spec => ?.
  move /eq_length. rewrite ? app_length map_length repeat_length.
  by lia.
Qed.

Lemma pyramid_shuffle {n} : seq 0 n ++ pyramid n ≡ repeat 0 n ++ map S (pyramid n).
Proof.
  elim: n.
    done.
  move=> n IH.
  rewrite /pyramid seq_last /plus flat_map_concat_map map_app concat_app.
  rewrite -flat_map_concat_map -/(pyramid _).
  rewrite ? map_app. cbn. rewrite ? app_nil_r.
  rewrite seq_shift.
  under (eq_lr 
    (A' := (seq 0 n ++ [n]) ++ (seq 0 n ++ pyramid n)) 
    (B' := (0 :: seq 1 n) ++ (repeat 0 n ++ map S (pyramid n)))).
    by eq_trivial.
    by eq_trivial.
  rewrite -/(mset_eq _ _).
  rewrite -seq_last -/(seq _ (S n)).
  by apply /eq_app_iff.
Qed.

Lemma encode_nat_sat_aux {n} : 
  pyramid n ++ flat_map pyramid (seq 0 n) ≡ repeat 0 (length (pyramid n)) ++ (map S (flat_map pyramid (seq 0 n))).
Proof.
  elim: n.
    by done.
  move=> n IH.
  rewrite /pyramid ? seq_last /plus ? (flat_map_concat_map, map_app, concat_app, app_length).
  rewrite - ? flat_map_concat_map -/pyramid -/(pyramid _).
  rewrite ? repeat_add seq_length.
  cbn. rewrite ? app_nil_r.
  under (eq_lr 
    (A' := (pyramid n ++ flat_map pyramid (seq 0 n)) ++ (seq 0 n ++ pyramid n))
    (B' := (repeat 0 (length (pyramid n)) ++ map S (flat_map pyramid (seq 0 n))) ++ (repeat 0 n ++ map S (pyramid n)))).
    by eq_trivial.
    by eq_trivial.
  rewrite -/(mset_eq _ _).
  apply: eq_appI.
    done.
  by apply: pyramid_shuffle.
Qed.

Lemma pyramid_length n : n + length (pyramid n) <= 4 ^ n.
Proof.
  elim: n.
    cbn. by lia.
  move=> n IH. 
  rewrite /pyramid seq_last /plus -/plus flat_map_concat_map map_app concat_app app_length.
  rewrite -flat_map_concat_map -/(pyramid _).
  rewrite /map /concat app_length seq_length. move=> /=.
  case: n IH.
    rewrite /Nat.pow. by lia.
  move=> n. have := Nat.pow_gt_1 4 (S n) ltac:(lia) ltac:(lia).
    by lia.
Qed.

Lemma encode_nat_sat {φ x} : 
  mset_sat (construct_valuation φ) (encode_nat x).
Proof.
  rewrite /encode_nat /mset_sat ? Forall_norm /mset_sem.
  rewrite /construct_valuation ? embed_unembed.
  constructor.
    rewrite - repeat_add. apply: eq_eq. f_equal.
    have := pyramid_length (φ x).
    by lia.
  constructor.
    rewrite - repeat_add. apply: eq_eq. f_equal.
    have := pyramid_length (φ x).
    by lia.
  constructor.
    by apply: seq_sat1.
  constructor.
    by apply: pyramid_shuffle.
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
  rewrite /encode_constraint /mset_sat. rewrite ? (Forall_app_iff). rewrite - ? /(mset_sat _ _).
  move=> [Hx [Hy [Hz]]].
  move=> [/(encode_nat_spec Hx) ? [/(encode_nat_spec Hy) ? [/(encode_nat_spec Hz) ?]]].
  rewrite /mset_sat Forall_norm /mset_sem.
  move /eq_length. rewrite ? app_length.
  have -> : (length [0] = 1) by done.
  by lia.
Qed.

(* if uniform diophantine constraint is satisfied, then mset constraint has a solution *)
Lemma encode_constraint_sat {φ x y z} : 
  1 + (φ x) + (φ y) * (φ y) = (φ z) -> mset_sat (construct_valuation φ) (encode_constraint x y z).
Proof.
  move=> Hxyz.
  rewrite /encode_constraint /mset_sat ? Forall_app_iff Forall_singleton_iff.
  rewrite - ? /(mset_sat _ _).
  do 3 (constructor; first by apply: encode_bound_sat).
  do 3 (constructor; first by apply: encode_nat_sat).
  rewrite /mset_sem /construct_valuation ? embed_unembed.
  have ->: [0] = repeat 0 1 by done.
  rewrite - ? repeat_add. apply: eq_eq.
  f_equal. move: Hxyz=> <-. clear. elim: (φ y); clear.
    cbn. by lia.
  move=> φy IH. rewrite /pyramid seq_last /(plus 0 _) flat_map_concat_map map_app concat_app.
  rewrite -flat_map_concat_map -/(pyramid _).
  cbn. rewrite ? app_length seq_length. cbn. by lia.
Qed.


(* encode a single H10UC constraint as a list of FMsetC constraints *)
Definition encode_h10uc '(x, y, z) := encode_constraint x y z.

(* many-one reduction from H10UC to FMsetC *)
Theorem H10UC_to_FMsetC : H10UC_SAT ⪯ FMsetC_SAT.
Proof.
  exists (fun h10ucs => flat_map encode_h10uc h10ucs).
  move=> h10ucs. constructor.
  - move=> [φ Hφ]. 
    exists (construct_valuation φ).
    elim: h10ucs Hφ.
      done.
    move=> [[x y] z] h10cs IH.
    move /Forall_forall. rewrite Forall_cons_iff. move=> [Hxyz /Forall_forall /IH].
    move=> {}IH A B.
    rewrite /flat_map -/(flat_map _) in_app_iff. case; first last.
      by apply /IH.
    rewrite /encode_h10uc.
    have := @encode_constraint_sat φ x y z ltac:(done).
    rewrite /mset_sat Forall_forall. by apply.
  - move=> [φ]. rewrite - mset_satP /mset_sat. move=> Hφ.
    pose ψ := (fun x => length (φ (embed (x, 0, 1)))).
    exists ψ.
    rewrite - Forall_forall.
    elim: h10ucs Hφ.
      done.
    move=> [[x y] z] h10ucs IH. rewrite /flat_map -/(flat_map _) Forall_app_iff.
    rewrite /(encode_h10uc _).
    move=> [/encode_constraint_spec Hxyz /IH ?].
    by constructor.
Qed.

Check H10UC_to_FMsetC.
(* Print Assumptions H10UC_to_FMsetC. *)

From Undecidability Require Import Problems.TM.
From Undecidability Require Import Reductions.H10C_to_H10UC.

(* undecidability of FMsetC *)
Theorem FMsetC_undec : Halt ⪯ FMsetC_SAT.
Proof.
  apply (reduces_transitive H10UC_undec).
  apply H10UC_to_FMsetC.
Qed.

Check FMsetC_undec.
(* Print Assumptions FMsetC_undec. *)
