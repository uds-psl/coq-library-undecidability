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

Lemma Forall_mapP {X Y : Type} {P : Y -> Prop} {f : X -> Y} {l : list X} : 
  Forall P (map f l) <-> Forall (fun x => P (f x)) l.
Proof.
  elim: l; [ constructor; by constructor | ].
  move=> ? ? IH /=. constructor => /ForallE [? /IH ?]; by constructor.
Qed.

Lemma map_0P {X: Type} {A: list X} : (map (fun=> 0) A) = repeat 0 (length A).
Proof. 
  elim: A; [done | by move=> > /= ->].
Qed.

Lemma count_occ_app {X : Type} {D : forall x y : X, {x = y} + {x <> y}} {A B c} :
  count_occ D (A ++ B) c = count_occ D A c + count_occ D B c.
Proof.
  elim: A B; first done.
  move=> a A IH B /=. rewrite IH. by case: (D a c).
Qed.
