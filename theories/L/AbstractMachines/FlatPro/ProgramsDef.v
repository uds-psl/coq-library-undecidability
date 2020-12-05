From Undecidability.L Require Import Prelim.MoreBase L.
Require Import Lia.

(* ** Encoding Terms as Programs *)

Inductive Tok := varT (n :nat) | appT | lamT | retT.
Notation Pro := (list Tok) (only parsing).

Instance Tok_eq_dec : eq_dec Tok.
Proof.
repeat intro. hnf. repeat decide equality.
Qed.

Fixpoint compile (s: L.term) : Pro :=
  match s with
    var x => [varT x]
  | app s t => compile s ++ compile t ++ [appT]
  | lam s => lamT :: compile s ++ [retT]
  end.

Inductive reprP : Pro -> term -> Prop :=
  reprPC s : reprP (compile s) (lam s).

Lemma reprP_elim P s': reprP P s' -> exists s, P = compile s /\ s' = lam s.
Proof. inversion 1. eauto. Qed. 