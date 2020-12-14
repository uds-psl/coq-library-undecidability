Require Import List Lia Relation_Operators.
Import ListNotations.

From Undecidability.StackMachines.Util Require Import Nat_facts List_facts.
Require Import Undecidability.StackMachines.Reductions.CM1_HALT_to_SMNdl_UB.SMX.

Require Import ssreflect ssrbool ssrfun.

Set Default Proof Using "Type".
Set Default Goal Selector "!".

Section SMX_facts.
Context {State Symbol : Set}.

Local Definition Config := @Config State Symbol.

(* reachable in at most n steps *)
Inductive reachable_n (M: SMX) : nat -> Config -> Config -> Prop :=
  | reach_refl (n: nat) (X: Config) : reachable_n M n X X
  | reach_step (n: nat) (X Y Z: Config) : step M X Y -> reachable_n M n Y Z -> reachable_n M (1+n) X Z.

Definition terminal (M: SMX) (X: Config) : Prop :=
  forall (Y: Config), not (step M X Y).

(* terminating or reachable in at most n steps *)
Definition maybe_reachable (M: SMX) (n: nat) (X Y: Config) : Prop :=
  reachable_n M n X Y \/ (exists Z, reachable_n M n X Z /\ terminal M Z).

Lemma reachable_n_maybe_reachable {M n X Y} : reachable_n M n X Y-> maybe_reachable M n X Y.
Proof. move=> ?. by left. Qed.

Lemma terminal_maybe_reachable {M n X Y} : terminal M X -> maybe_reachable M n X Y.
Proof. move=> ?. right. exists X. constructor; [by apply: reach_refl | done]. Qed.

Lemma reachable_n_step {M X Y} : step M X Y -> reachable_n M 1 X Y.
Proof. move=> ?. apply: reach_step; [by eassumption | by apply: reach_refl]. Qed.

Lemma reachable_n_mon {M n m X Y} :
  n <= m -> reachable_n M n X Y -> reachable_n M m X Y.
Proof.
  elim: n m X Y.
  { move=> m X Y ?. move Hn: (0) => n HXY. 
    case: HXY Hn => *; [by apply: reach_refl | by lia]. }
  move=> n IH m X Y Hnm. move Hn': (S n) => n' HXY. 
  case: HXY Hn' => [|{}n'] *; first by apply: reach_refl.
  have ->: m = S (m - 1) by lia. 
  apply: reach_step; first by eassumption. apply: IH; first by lia.
  by (have ->: n = n' by lia).
Qed.
    
Lemma reachable_n_trans {M} n m X Y Z : 
  reachable_n M n X Y -> reachable_n M m Y Z -> reachable_n M (n+m) X Z.
Proof.
  elim: n X Y.
  { move=> X Y /=. move Hn: (0) => n HXY. case: HXY Hn; [done | by lia]. }
  move=> n IH X Y /=. move Hn': (S n) => n' HXY. case: HXY Hn' => [| {}n' {}X Y1 Y2] *.
  { apply: reachable_n_mon; last by eassumption. by lia. }
  have ?: n' = n by lia. subst n'.
  apply: reach_step; first by eassumption. by apply: IH; eassumption.
Qed.

Lemma reachable_n_refl' {M n X X'} : 
  X = X' -> reachable_n M n X X'.
Proof. move=> ->. by apply: reach_refl. Qed.

Lemma reachable_n_mon' {M n n' X X' Y Y'} :
  n <= n' -> (X, Y) = (X', Y') -> reachable_n M n X Y -> reachable_n M n' X' Y'.
Proof. move=> ? [? ?] ?. subst. by apply: reachable_n_mon; eassumption. Qed.

Lemma reachable_n_trans' {M} n {m k X X' Y Z} : 
  m+n <= k -> X = X' -> reachable_n M n Y Z -> reachable_n M m X Y -> reachable_n M k X' Z.
Proof. move /reachable_n_mon => H *. subst. apply: H. by apply: reachable_n_trans; eassumption. Qed.

Lemma reachable_n_reachable {M T x y} : 
  reachable_n M T x y -> reachable M x y.
Proof.
  elim: T x y.
  { move HT: (0) => T x y Hxy. case: Hxy HT => *; [by apply: rt_refl | by lia]. }
  move=> T IH x y. move HT': (S T) => T' Hxy. 
  case: Hxy HT'; first by (move=> *; apply: rt_refl).
  move=> {}T' {}x z {}y /(@rt_step Config) Hxz + ?.
  have ->: T' = T by lia. move /IH. by apply: rt_trans.
Qed.

Lemma maybe_reachable_refl' {M n X Y} : X = Y -> maybe_reachable M n X Y.
Proof. move=> ->. left. by apply: reach_refl. Qed.

Lemma maybe_reachable_mon' {M n n' X X' Y Y'} :
  n <= n' -> (X, Y) = (X', Y') -> maybe_reachable M n X Y -> maybe_reachable M n' X' Y'.
Proof.
  move /reachable_n_mon => H [-> ->] [?|]; first by (left; apply: H).
  move=> [Z [HZ ?]]. right. exists Z. by constructor; [apply: H | ].
Qed.

Lemma maybe_reachable_trans' {M} n {m k X X' Y Z} : 
  m + n <= k -> X = X' -> maybe_reachable M n Y Z -> maybe_reachable M m X Y -> maybe_reachable M k X' Z.
Proof.
  move /reachable_n_mon => H <- HYZ [?|]; first last.
  { move=> [Z' [HZ' ?]]. right. exists Z'. constructor; last done.
    apply: H. apply: reachable_n_mon; last by eassumption. by lia. }
  move: HYZ => [? | [Z' [HZ' ?]]].
  { left. apply: H. by apply: reachable_n_trans; eassumption. }
  right. exists Z'. constructor; last done.
  apply: H. by apply: reachable_n_trans; eassumption.
Qed.

Lemma first_step {M} (op : Instruction) (v w: list Symbol) {n X Z} : 
  1 <= n -> In op M -> 
  let '((r, s, x), (r', s', y), b) := op in
    X = (r ++ v, s ++ w, x) ->
    reachable_n M (n-1) (if b is true then (s' ++ w, r' ++ v, y) else (r' ++ v, s' ++ w, y)) Z ->
    reachable_n M n X Z.
Proof.
  move=> Hn. move: op=> [[[[r s] x] [[r' s'] y]] b].
  move /(transition M v w) /reachable_n_step => + ? ?. subst X.
  by (apply: (reachable_n_trans' (n-1)); first by lia).
Qed.

Lemma maybe_first_step {M} (op : Instruction) (v w: list Symbol) {n X Z} : 
  1 <= n -> In op M -> 
  let '((r, s, x), (r', s', y), b) := op in
    X = (r ++ v, s ++ w, x) ->
    maybe_reachable M (n-1) (if b is true then (s' ++ w, r' ++ v, y) else (r' ++ v, s' ++ w, y)) Z ->
    maybe_reachable M n X Z.
Proof.
  move=> Hn. move: op=> [[[[r s] x] [[r' s'] y]] b].
  move /(transition M v w) /reachable_n_step => HXY ? HYZ. subst X.
  move: HYZ => [? | [Z' [HZ' ?]]].
  - left. move: HXY. by (apply: (reachable_n_trans' (n-1)); first by lia).
  - right. exists Z'. constructor; last done.
    move: HXY. by (apply: (reachable_n_trans' (n-1)); first by lia).
Qed.

End SMX_facts.
