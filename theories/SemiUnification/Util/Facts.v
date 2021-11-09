(* 
  Autor(s):
    Andrej Dudenhefner (1) 
  Affiliation(s):
    (1) Saarland University, Saarbrücken, Germany
*)

Require Import List.
Import ListNotations.
Require Import ssreflect ssrbool ssrfun.

Set Default Goal Selector "!".

(* duplicates argument *)
Lemma copy {A: Prop} : A -> A * A.
Proof. done. Qed.

Lemma itebP {X: Type} {P: bool -> X} {b: bool} : (if b then P true else P false) = P b.
Proof. by case: b. Qed.

(* Forall facts *)
Lemma Forall_singleton_iff {X: Type} {P: X -> Prop} {x} : Forall P [x] <-> P x.
Proof.
  rewrite Forall_cons_iff. by constructor; [case |].
Qed.

(* usage: rewrite ? Forall_norm *)
Definition Forall_norm := (@Forall_app, @Forall_singleton_iff, @Forall_cons_iff, @Forall_nil_iff).
