(* 
  Autor(s):
    Andrej Dudenhefner (1) 
  Affiliation(s):
    (1) Saarland University, Saarbrücken, Germany
*)

Require Import List.

Require Import ssreflect ssrbool ssrfun.

Set Default Goal Selector "!".

Lemma ForallE {X: Type} {P: X -> Prop} {l} : 
  Forall P l -> if l is x :: l then P x /\ Forall P l else True.
Proof. by case. Qed.

Lemma map_0P {X: Type} {A: list X} : (map (fun=> 0) A) = repeat 0 (length A).
Proof. 
  elim: A; [done | by move=> > /= ->].
Qed.
