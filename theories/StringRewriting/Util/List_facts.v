Require Import List.

Require Import ssreflect.

Set Default Goal Selector "!".

Lemma ForallE {X : Type} {P : X -> Prop} {l} : 
  Forall P l -> if l is x :: l then P x /\ Forall P l else True.
Proof. by case. Qed.

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

Lemma map_firstn {X Y: Type} {f: X -> Y} {n} {l} : map f (firstn n l) = firstn n (map f l).
Proof.
  elim: n l; first done.
  move=> n IH [|? ?]; first done.
  move=> /=. congr cons. by apply: IH.
Qed.

Lemma map_skipn {X Y: Type} {f: X -> Y} {n} {l} : map f (skipn n l) = skipn n (map f l).
Proof.
  elim: n l; first done.
  move=> n IH [|? ?]; [done | by apply: IH].
Qed.
