(* 
  Autor(s):
    Andrej Dudenhefner (1) 
  Affiliation(s):
    (1) Saarland University, Saarbrücken, Germany
*)

Require Import List.
Require Import ssreflect ssrbool ssrfun. 

Lemma ForallE {T : Type} {P : T -> Prop} {l} : 
  Forall P l -> if l is x :: l then P x /\ Forall P l else True.
Proof. by case. Qed.

Lemma incl_consP {X: Type} {a: X} {A B} : incl (a :: A) B <-> (In a B /\ incl A B).
Proof. constructor.
  - by move=> /Forall_forall /ForallE [? /Forall_forall].
  - move=> [? H] ? [<-| ?]; [done | by apply: H].
Qed.
