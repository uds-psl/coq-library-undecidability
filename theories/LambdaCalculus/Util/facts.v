Require Import Relations List Lia PeanoNat.
Import ListNotations.
Require Import ssreflect.

#[local] Arguments in_combine_l {A B l l' x y}.
#[local] Arguments app_inj_tail {A x y a b}.

Lemma Forall2_repeat {X Y : Type} (P : X -> Y -> Prop) x y n : P x y -> Forall2 P (repeat x n) (repeat y n).
Proof.
  move=> ?. elim: n; by constructor.
Qed.

Lemma Forall_Forall_impl {X : Type} (P Q : X -> Prop) l : (Forall (fun x => P x -> Q x) l) -> Forall P l -> Forall Q l.
Proof.
  elim; first done.
  move=> > H ? IH /Forall_cons_iff [/H] ??.
  by constructor; auto.
Qed.

Lemma Forall2_repeat_r {X Y : Type} {P : X -> Y -> Prop} {l y n} : Forall2 P l (repeat y n) -> Forall (fun x => P x y) l.
Proof.
  move E: (repeat y n)=> l' H.
  elim: H n E; first done.
  move=> > ?? IH [|n]; first done.
  move=> [? /IH] ?. subst.
  by constructor; auto.
Qed.

Lemma Forall2_repeat_r' {X Y : Type} (P : X -> Y -> Prop) l y n : Forall (fun x => P x y) l -> length l = n -> Forall2 P l (repeat y n).
Proof.
  move=> + <-. elim; first done.
  move=> > ?? IH. by constructor.
Qed.

Lemma nth_error_seq i k : i < k -> nth_error (seq 0 k) i = Some i.
Proof.
  elim: k i; first lia.
  move=> k IH [|i]; first done.
  move=> ? /=.
  rewrite -seq_shift nth_error_map IH; by [|lia].
Qed.

Lemma nth_error_Some' {X : Type} {l : list X} {i : nat} {x : X} : nth_error l i = Some x -> i < length l.
Proof.
  move=> E. apply /nth_error_Some. by rewrite E.
Qed.

Lemma Forall2_change {X Y : Type} (P Q : X -> Y -> Prop) l l1 l2 :
  length l1 = length l2 ->
  (forall i, match (nth_error l i, nth_error l1 i, nth_error l2 i) with (Some x, Some y1, Some y2) => P x y1 -> Q x y2 | _ => True end) ->
  Forall2 P l l1 -> Forall2 Q l l2.
Proof.
  move=> ++ H. elim: H l2; first by case.
  move=> x y1 {}l {}l1 ?? IH [|y2 l2]; first done.
  move=> /= [] /IH {}IH H. constructor; first by apply: (H 0).
  apply: IH=> i. by apply: (H (S i)).
Qed.

Lemma Forall2_change2 {Y : Type} (P Q : nat -> Y -> Prop) m l1 l2 x1 x2 x'1 x'2 :
  (P (length l1) x1 -> Q (length l1) x'1) ->
  (P (S (length l1)) x2 -> Q (S (length l1)) x'2) ->
  (forall i x, i < S (S m) -> i <> length l1 -> i <> S (length l1) -> P i x -> Q i x) ->
  Forall2 P (seq 0 (S (S m))) (l1 ++ x1 :: x2 :: l2) ->
  Forall2 Q (seq 0 (S (S m))) (l1 ++ x'1 :: x'2 :: l2).
Proof.
  move=> Hx1 Hx2 H'. apply: Forall2_change; first by rewrite !length_app.
  move=> i.
  case Ex: (nth_error (seq _ _) i) => [x|]; last done.
  case Ey1: (nth_error (l1 ++ x1 :: x2 :: l2) i) => [y1|]; last done.
  case Ey2: (nth_error (l1 ++ x'1 :: x'2 :: l2) i) => [y2|]; last done.
  move: (Ex) => /nth_error_Some'. rewrite length_seq=> Hx.
  move: Ex. rewrite nth_error_seq; first done.
  move=> [?]. subst i.
  have [?|[?|[??]]] : x = length l1 \/ x = S (length l1) \/ (x <> length l1 /\ x <> S (length l1)) by lia.
  - subst x. move: Ey1. rewrite nth_error_app2; first done.
    rewrite Nat.sub_diag=> - [<-].
    move: Ey2. rewrite nth_error_app2; first done.
    rewrite Nat.sub_diag=> - [<-]. by apply: Hx1.
  - subst x. move: Ey1. rewrite nth_error_app2; first lia.
    have ->: S (length l1) - length l1 = 1 by lia.
    move=> [<-]. move: Ey2. rewrite nth_error_app2; first lia.
    have ->: S (length l1) - length l1 = 1 by lia.
    move=> [<-]. by apply: Hx2.
  - suff ->: y1 = y2 by apply: H'.
    have [?|?] : x < length l1 \/ x > S (length l1) by lia.
    + move: Ey1. rewrite nth_error_app1; first done.
      move: Ey2. rewrite nth_error_app1; first done.
      by move=> -> [<-].
    + move: Ey1 Ey2.
      change (l1 ++ x1 :: x2 :: l2) with (l1 ++ [x1; x2] ++ l2).
      change (l1 ++ x'1 :: x'2 :: l2) with (l1 ++ [x'1; x'2] ++ l2).
      rewrite !app_assoc. rewrite !nth_error_app2 ?length_app /=; [lia..|].
      by move=> -> [<-].
Qed.

Lemma Forall2_map_r {X Y Z : Type} (f : Y -> Z) (P : X -> Z -> Prop) l1 l2 : Forall2 P l1 (map f l2) <-> Forall2 (fun x y => P x (f y)) l1 l2.
Proof.
  split.
  - move E: (map f l2) => l3 H.
    elim: H l2 E; first by case.
    move=> > ??? [|??]; first done.
    move=> /= [??]. subst.
    by auto using Forall2.
  - elim; by constructor.
Qed.

Lemma Forall2_map_l {X Y Z : Type} (f : X -> Z) (P : Z -> Y -> Prop) l1 l2 : Forall2 P (map f l1) l2 <-> Forall2 (fun x y => P (f x) y) l1 l2.
Proof.
  split.
  - move E: (map f l1) => l3 H.
    elim: H l1 E; first by case.
    move=> > ??? [|??]; first done.
    move=> /= [??]. subst.
    by auto using Forall2.
  - elim; by constructor.
Qed.

Lemma Forall2_trans {X Y Z : Type} (P : X -> Y -> Prop) (Q : Y -> Z -> Prop) (R : X -> Z -> Prop) l1 l2 l3 :
  (forall x y z, P x y -> Q y z -> R x z) -> Forall2 P l1 l2 -> Forall2 Q l2 l3 -> Forall2 R l1 l3.
Proof.
  move=> H H'. elim: H' l3.
  - by move=> [|??] /Forall2_length.
  - move=> > ?? IH [|??] /[dup] /Forall2_length; first done.
    move=> _ /Forall2_cons_iff [? /IH ?]. constructor; last done.
    apply: H; by eassumption.
Qed.
