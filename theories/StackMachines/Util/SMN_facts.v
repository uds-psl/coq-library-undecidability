Require Import Arith Lia Relation_Operators Operators_Properties List.
Import ListNotations.

From Undecidability.StackMachines.Util Require Import Nat_facts List_facts.
Require Import Undecidability.StackMachines.SMN.

Require Import ssreflect ssrbool ssrfun.

Set Default Goal Selector "!".

Local Definition rt_rt1n := @clos_rt_rt1n_iff Config.

Definition terminal (M: SMN) (X: Config) : Prop :=
  forall (Y: Config), not (step M X Y).

Lemma stepI {M: SMN} {X Y: Config} v w l r l' r' x y : X = (l ++ v, r ++ w, x) -> Y = (l' ++ v, r' ++ w, y) -> 
  In ((l, r, x), (l', r', y)) M -> step M X Y.
Proof. move=> -> -> /transition. by apply. Qed.

(* step is monotone wrt machine inclusion *)
Lemma step_incl {M1 M2 X Y} : incl M1 M2 -> step M1 X Y -> step M2 X Y.
Proof. move=> HM1M2. case=> > /HM1M2. by apply: transition. Qed.

Lemma deterministic_confluent {M} : deterministic M -> confluent M.
Proof.
  move=> HM ? ? + /rt_rt1n Hxy1. elim: Hxy1.
  { move=> *. eexists. by constructor; last by apply: rt_refl. }
  move=> ? ? ? Hxy1 /rt_rt1n Hy1z1 IH ? /rt_rt1n Hxy2. case: Hxy2 Hxy1.
  - move=> ?. eexists. constructor; first by apply: rt_refl.
    apply: rt_trans; last by eassumption. apply: rt_step. by eassumption.
  - move=> > Hxy2 /rt_rt1n Hy2z2 Hxy1. have ? := HM _ _ _ Hxy1 Hxy2. subst.
    by apply: IH.
Qed.

(* reachability in at most n steps *)
Inductive reachable_n (M: SMN) : nat -> Config -> Config -> Prop :=
  | rn_refl n X : reachable_n M n X X
  | rn_step n X Y Z: step M X Y -> reachable_n M n Y Z -> reachable_n M (1+n) X Z.

Lemma reachable_0E {M X Y} : reachable_n M 0 X Y -> X = Y.
Proof.
  move Hn: (0) => n HXY. case: HXY Hn; first done. by lia.
Qed.
  
Lemma reachable_SnE {M n X Z} : reachable_n M (1+n) X Z -> 
  X = Z \/ (exists Y, step M X Y /\ reachable_n M n Y Z).
Proof.
  move Hn': (1+n) => n' HXY. case: HXY Hn'; first by (move=> *; left).
  move=> {}n' *. right. have ->: n = n' by lia. by firstorder done.
Qed.

Lemma reachable_n_incl {M1 M2 n X Y} : incl M1 M2 -> reachable_n M1 n X Y -> reachable_n M2 n X Y.
Proof.
  move=> H. elim: n X Y.
  { move=> > /reachable_0E ->. by apply: rn_refl. }
  move=> n IH > /reachable_SnE. case.
  - move=> ->. by apply: rn_refl.
  - move=> [?] [? ?]. apply: rn_step.
    + apply: step_incl; by eassumption.
    + by apply: IH.
Qed.

Lemma reachable_to_reachable_n {M X Y} : reachable M X Y -> exists n, reachable_n M n X Y.
Proof.
  move /rt_rt1n. elim; first by (move=> ?; exists 0; apply: rn_refl).
  move=> > ? _ [n ?]. exists (1+n). apply: rn_step; by eassumption.
Qed.

Lemma reachable_n_to_reachable {M n X Y} : reachable_n M n X Y -> reachable M X Y.
Proof.
  elim; first by (move=> *; apply: rt_refl).
  move=> *. apply: rt_trans; last by eassumption.
  by apply: rt_step.
Qed.

Lemma reachable_incl {M1 M2 X Y} : incl M1 M2 -> reachable M1 X Y -> reachable M2 X Y.
Proof.
  move=> /reachable_n_incl H /reachable_to_reachable_n [?] ?.
  apply: reachable_n_to_reachable. apply: H. by eassumption.
Qed.

(* confluence is preserved under rule reordering / duplication *)
Lemma confluent_incl {M1 M2} : incl M1 M2 -> incl M2 M1 -> confluent M1 -> confluent M2.
Proof.
  move=> /reachable_incl H12 /reachable_incl H21 HM1 ? ? ? /H21 /HM1 {}HM1 /H21 /HM1 [? [? ?]]. 
  eexists. constructor; apply: H12; by eassumption.
Qed.

(* reachable_n is monotone *)
Lemma reachable_n_monotone {M X Y m n} : m <= n -> reachable_n M m X Y -> reachable_n M n X Y.
Proof.
  elim: n m X Y.
  { move=> m > ?. have ->: m = 0 by lia. move /reachable_0E => ->. by apply: rn_refl. }
  move=> n IH [|m] > ?.
  { move /reachable_0E => ->. by apply: rn_refl. }
  move /reachable_SnE => [-> | [Z [? ?]]]; first by apply: rn_refl.
  apply: rn_step; first by eassumption.
  apply: IH; last by eassumption. by lia.
Qed.

Lemma step_app {M1 M2 x y} : step (M1 ++ M2) x y -> step M1 x y \/ step M2 x y.
Proof. case=> >. rewrite in_app_iff. case=> /transition ?; [by left | by right]. Qed.

Lemma reachable_n_stack_app {M n l r x l' r' y v w} : 
  reachable_n M n (l, r, x) (l', r', y) -> reachable_n M n (l ++ v, r ++ w, x) (l' ++ v, r' ++ w, y).
Proof.
  elim: n l r x l' r' y.
  { move=> > /reachable_0E [] <- <- <-. apply: rn_refl. }
  move=> n IH l r x l' r' y /reachable_SnE [[] <- <- <- | [z] [+]]; first by apply: rn_refl.
  move Hx': (l, r, x) => x' Hx'z. case: Hx'z Hx'.
  move=> > H [] -> -> -> /IH {}IH. apply: rn_step; last by eassumption.
  rewrite -?app_assoc. by apply: transition.
Qed.

Lemma reachable_stack_app {M l r x l' r' y v w} : 
  reachable M (l, r, x) (l', r', y) -> reachable M (l ++ v, r ++ w, x) (l' ++ v, r' ++ w, y).
Proof.
  move /reachable_to_reachable_n => [?] /reachable_n_stack_app ?. by apply: reachable_n_to_reachable.
Qed.

Lemma length_preserving_incl {M1 M2} : incl M1 M2 -> length_preserving M2 -> length_preserving M1.
Proof. by move=> H12 H2 > /H12 /H2. Qed.

Lemma length_preservingP {M l r x l' r' y} : 
  length_preserving M -> reachable M (l, r, x) (l', r', y) -> 
  (l, r, x) = (l', r', y) \/ (length (l ++ r) = length (l' ++ r') /\ 1 <= length (l ++ r)).
Proof.
  move=> HM /reachable_to_reachable_n [n]. elim: n l r x l' r' y.
  { move=> > /reachable_0E => ?. by left. }
  move=> n IH l r x l' r' y /reachable_SnE [? | [Z] []]; first by left.
  move HX: (l, r, x) => X HXZ. case: HXZ HX.
  move=> > /HM []. rewrite ?app_length. move=> ? ? [] ? ? ?. subst.
  move /IH. case.
  - move=> [] *. subst. rewrite ?app_length. right. by lia.
  - rewrite ?app_length. move=> [] ? ?. right. by lia.
Qed.

Lemma next_configs M (X: Config) : exists L, (forall Y, step M X Y -> In Y L) /\ length L <= length M.
Proof.
  elim: M.
  { exists []. constructor=> > /=; [by case | by lia]. }
  move: X => [[lx rx] x] [[[l r] y] [[l' r'] z]] M [L [HL ?]].
  have [[] * | Hy] : (firstn (length l) lx, firstn (length r) rx, x) = (l, r, y) \/ 
    (firstn (length l) lx, firstn (length r) rx, x) <> (l, r, y) by do 4 decide equality.
  - exists ((l' ++ skipn (length l) lx, r' ++ skipn (length r) rx, z) :: L).
    constructor; last by (move=> /=; lia).
    move HX: (lx, rx, x) => X Z HXZ. case: HXZ HX => v w > /=. case.
    + move=> + [] => [[]] *. subst. left.
      by rewrite ?skipn_app ?skipn_all ?Nat.sub_diag /=.
    + move /transition => /(_ v w) ? ?. right. apply: HL. by congruence.
  - exists L. constructor; last by (move=> /=; lia).
    move HX: (lx, rx, x) => X Z HXZ. case: HXZ HX => v w > /=. case.
    + move=> + [] => [[]] *. subst. exfalso. apply: Hy.
      by rewrite ?firstn_app ?firstn_all ?Nat.sub_diag ?app_nil_r.
    + move /transition => /(_ v w) ? ?. apply: HL. by congruence.
Qed.

Lemma next_n_configs M (n: nat) (Xs: list Config) : 
  exists L, (forall X Y, In X Xs -> reachable_n M n X Y -> In Y L) /\ (length L <= (Nat.pow (1 + length M) n) * length Xs * (1+n)).
Proof.
  elim: n Xs.
  - move=> Xs. exists Xs. constructor; last by (move=> /=; lia).
    by move=> X Y ? => /reachable_0E => <-.
  - move=> n IH Xs.
    have [Ys [HYs ?]]: exists L, (forall X Y, In X Xs -> step M X Y -> In Y L) /\ length L <= (1 + length M) * length Xs.
    { (* there is a list of next configurations from Xs *)
      clear. elim: Xs.
      { exists []. constructor; [done | by move=> /=; lia]. }
      move=> X Xs [L [HL ?]]. have [LX [HLX ?]] := next_configs M X.
      exists (LX ++ L). constructor; first last.
      - rewrite app_length /length -?/(length _). by lia.
      - move=> > /=. rewrite in_app_iff. move=> [<- /HLX ? | * ]; first by left.
        right. apply: HL; by eassumption. }
    have [L [HL ?]] := IH Ys. exists (Xs ++ L). constructor.
    { move=> X Y HX /reachable_SnE. case.
      - move=> <-. apply /in_app_iff. by left.
      - move=> [Z] [/HYs] /(_ HX) /HL => H /H ?. apply /in_app_iff. by right. }
    rewrite app_length. 
    suff: length L <= (1 + length M) ^ S n * length Xs * (1 + n).
    { have := Nat.pow_nonzero (1 + length M) (S n) ltac:(lia). by nia. }
    rewrite /Nat.pow -/Nat.pow.
    have ? := Nat.pow_nonzero (1 + length M) n ltac:(lia). 
    suff: (1 + length M) ^ n * length Ys <= (1 + length M) * (1 + length M) ^ n * length Xs by nia.
    by nia.
Qed.

Lemma concat_reachable {M} {NM: nat} (xs : list Config) : bounded M NM ->
  exists L, (forall x y, In x xs -> reachable M x y -> In y L) /\ length L <= NM * length xs.
Proof.
  move=> bounded_M. elim: xs.
  { exists []. constructor; [done | by (move=> /=; lia) ]. }
  move=> x xs [Lxs [HLxs ?]]. have [Lx [HLx ?]] := bounded_M x.
  exists (Lx ++ Lxs). constructor; last by (rewrite app_length /=; lia).
  move=> ? ? /=. rewrite in_app_iff. case.
  - move=> <- /HLx *. by left.
  - move=> *. right. apply: HLxs; by eassumption.
Qed.
