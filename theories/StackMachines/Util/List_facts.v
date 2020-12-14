Require Import List Lia.
Import ListNotations.

Require Import Undecidability.StackMachines.Util.Nat_facts.

Require Import ssreflect ssrbool ssrfun.

Set Default Goal Selector "!".

Lemma seq_last {m n} : seq m (1+n) = seq m n ++ [m + n].
Proof. have -> : 1+n = n+1 by lia. by rewrite seq_app. Qed.

(* nth_error facts *)

Lemma nth_error_map {X Y: Type} {f: X -> Y} {l: list X} {n: nat} :
  nth_error (map f l) n = omap f (nth_error l n).
Proof.
  elim: n l; first by case.
  move=> n IH. case; first done.
  move=> x l /=. by rewrite /nth_error -?/(nth_error _ _).
Qed.

Lemma nth_error_seq {m l n: nat} :
  n < l -> nth_error (seq m l) n = Some (m+n).
Proof.
  elim: n m l.
  - move=> m [|l]; first by lia.
    move=> /= _. congr Some. by lia.
  - move=> n IH m [|l /= ?]; first by lia.
    rewrite /nth_error -/(nth_error _ _) IH; [|congr Some]; by lia.
Qed.

Lemma repeat_appP {X: Type} {x: X} {n m: nat} : 
  repeat x n ++ repeat x m = repeat x (n+m).
Proof. by elim: n; [| move=> ? /= ->]. Qed.

Lemma repeat_app_appP {X: Type} {x: X} {xs: list X} {n m: nat} : 
  repeat x n ++ (repeat x m ++ xs) = repeat x (n+m) ++ xs.
Proof. by rewrite -repeat_appP app_assoc. Qed.

Lemma repeat_singP {X: Type} {x: X} : 
  [x] = repeat x 1.
Proof. done. Qed.

Lemma app_assoc' {X: Type} {xs ys zs: list X} :
  (xs ++ ys) ++ zs = xs ++ ys ++ zs.
Proof. by rewrite app_assoc. Qed.

Lemma cons_repeat_app {X: Type} {x: X} {xs: list X} {m: nat} : 
  x :: (repeat x m ++ xs) = (repeat x (m+1) ++ xs).
Proof. by have ->: m + 1 = S m by lia. Qed.

Lemma app_singP {X: Type} {x: X} {l: list X} : [x] ++ l = x :: l.
Proof. done. Qed.

Lemma app_repeat_cons {X: Type} {n: nat} {x: X} {l: list X} : repeat x (1+n) ++ l = x :: (repeat x n ++ l).
Proof. done. Qed.

Lemma nth_error_Some_In_combineP {X: Type} {i} {x: X} {L: list X} : 
  nth_error L i = Some x <-> In (i, x) (combine (seq 0 (length L)) L).
Proof.
  suff: forall j, nth_error L i = Some x <-> In (j+i, x) (combine (seq j (length L)) L) by move /(_ 0).
  elim: L i.
  { by move=> [|i] j. }
  move=> y L IH [|i] j /=.
  - constructor.
    + move=> [->]. left. f_equal. by lia.
    + case; first by move=> [_ ->].
      move /(@in_combine_l nat X). rewrite in_seq. by lia.
  - rewrite (IH i (S j)). 
    have ->: S j + i = j + S i by lia. constructor.
    + move=> ?. by right.
    + by case; [move=> []; lia |].
Qed.

Lemma nth_error_combine_SomeP {X: Type} {i} {x: X} {L: list X} : 
  nth_error L i = Some x <-> nth_error (combine (seq 0 (length L)) L) i = Some (i, x).
Proof.
  suff: forall j, nth_error L i = Some x <-> nth_error (combine (seq j (length L)) L) i = Some (j+i, x) by move /(_ 0).
  elim: L i; first by case.
  move=> y L IH [|i] j /=.
  - have ->: j + 0 = j by lia.
    by constructor; move=> [->].
  - have ->: j + S i = S j + i by lia.
    by apply: IH.
Qed.

Lemma nth_error_appP {X: Type} {l1 l2: list X} {i: nat} {x: X} : 
  nth_error (l1 ++ l2) i = Some x <-> 
    ((i < length l1 /\ nth_error l1 i = Some x) \/ (length l1 <= i /\ nth_error l2 (i - length l1) = Some x)).
Proof.
  constructor.
  - have [Hi | Hi]: i < length l1 \/ length l1 <= i by lia.
    + by rewrite nth_error_app1; firstorder done.
    + by rewrite nth_error_app2; firstorder done.
  - move=> [[? ?]|[? ?]]; by [rewrite nth_error_app1 | rewrite nth_error_app2].
Qed.

Lemma NoDup_map {X Y: Type} {f : X -> Y} {l : list X} :
  (forall x1 x2, f x1 = f x2 -> x1 = x2) -> NoDup l -> NoDup (map f l).
Proof.
  move=> Hf. elim: l.
  { move=> ?. by apply: NoDup_nil. }
  move=> x l IH /NoDup_cons_iff [Hx /IH Hfl] /=.
  apply /NoDup_cons_iff. constructor; last done.
  rewrite in_map_iff. by move=> [x'] [/Hf ->].
Qed.

Lemma legnth_flat_map {X Y: Type} {f: X -> list Y} {l: list X} {n: nat}: 
  (forall x, length (f x) <= n) -> 
  length (flat_map f l) <= n * length l.
Proof.
  move=> Hf. elim: l.
  - move=> * /=. by lia.
  - move=> x l IH /=. rewrite app_length. have := Hf x. by lia.
Qed.

Lemma in_split_informative {X: Type} {x: X} {l: list X} : (forall (x y: X), {x = y} + {x <> y}) ->
  In x l -> { '(l1, l2) | l = l1 ++ x :: l2 }.
Proof.
  move=> H_dec. elim: l; first done.
  move=> y l IH /=. case: (H_dec y x).
  - move=> <- _. by exists ([], l).
  - move=> ? Hxl. have : In x l by case: Hxl.
    move /IH => [[l1 l2] ->]. by exists (y :: l1, l2).
Qed.

Lemma in_split_rest {X: Type} {x y: X} {L1 L2: list X} : 
  In y (L1 ++ x :: L2) -> x <> y -> In y (L1 ++ L2).
Proof. rewrite ?in_app_iff /=. by firstorder done. Qed. 

Lemma in_app_l {X: Type} {x: X} {l1 l2: list X} : In x l1 -> In x (l1 ++ l2).
Proof. move=> ?. apply /in_app_iff. by left. Qed.

Lemma in_app_r {X: Type} {x: X} {l1 l2: list X} : In x l2 -> In x (l1 ++ l2).
Proof. move=> ?. apply /in_app_iff. by right. Qed.
