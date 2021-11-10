Require Import List.

Require Import ssreflect.

Set Default Goal Selector "!".

Lemma Forall_repeatI {X : Type} {P : X -> Prop} {x n} : 
  P x -> Forall P (repeat x n).
Proof.
  elim: n; first by constructor.
  move=> ? IH ?. constructor; [done | by apply: IH].
Qed.

Lemma In_appl {X : Type} {x: X} {l1 l2: list X} : In x l1 -> In x (l1 ++ l2).
Proof. move=> ?. apply: in_or_app. by left. Qed.

Lemma In_appr {X : Type} {x: X} {l1 l2: list X} : In x l2 -> In x (l1 ++ l2).
Proof. move=> ?. apply: in_or_app. by right. Qed.
