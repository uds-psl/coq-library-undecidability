From Undecidability.Synthetic Require Import Definitions EnumerabilityFacts.

Require Import Undecidability.L.L.
Require Import Undecidability.L.Enumerators.term_enum.
Require Import Undecidability.L.Computability.Seval.

(* semi-decider for HaltL *)
Lemma HaltL_semi_decision : { f : term -> nat -> bool | semi_decider f HaltL }.
Proof.
  exists (fun t n => match eva n t with Some _ => true | None => false end).
    intros s. split.
    + intros [t [n Hn]%eval_iff%eval_seval].
      exists n. now rewrite (seval_eva Hn).
    + intros [n Hn]. destruct (eva n s) as [t|] eqn:E.
      * exists t. now apply eval_iff, (@seval_eval n), eva_seval.
      * easy.
Qed.

(* enumerator for HaltL *)
Lemma HaltL_enumeration : { e : nat -> option term | enumerator e HaltL }.
Proof.
  apply (semi_decider_enumerator enumerator__T_term (proj2_sig HaltL_semi_decision)).
Qed.

Definition HaltL_enumerator := proj1_sig HaltL_enumeration.

Lemma HaltL_enumerator_spec : enumerator HaltL_enumerator HaltL.
Proof. exact (proj2_sig HaltL_enumeration). Qed.
