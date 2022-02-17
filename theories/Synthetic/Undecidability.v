Require Export Undecidability.Synthetic.Definitions.
Require Import Undecidability.Synthetic.ReducibilityFacts.
Require Import Undecidability.Synthetic.DecidabilityFacts.
Require Import Undecidability.TM.SBTM.

(*
  p is undecidable if decidability of p implies co-enumerability of L halting.
  Since L halting is enumerable, its co-enumerability would imply its decidability.
  Instead of L halting, any other enumerable, many-one equivalent problem to L halting suffices. 
  For example (cf. [2]):
    Post correspondence problem (cf. [1, Lemma 2.26]),
    binary stack machine halting,
    two-counter machine halting,
    Diophantine constraint solvability, ...

  References:
  [1] Yannick Forster, Dominik Kirst, and Gert Smolka.
      "On synthetic undecidability in Coq, with an application to the Entscheidungsproblem."
      Proceedings of the 8th ACM SIGPLAN International Conference on Certified Programs and Proofs. 2019.
  [2] Yannick Forster.
      "Computability in Constructive Type Theory."
      PhD Thesis. Faculty of Mathematics and Computer Science of Saarland University. 2021.
      https://www.ps.uni-saarland.de/~forster/thesis.php
*)
Definition undecidable {X} (p : X -> Prop) :=
  decidable p -> enumerable (complement SBTM_HALT).

Lemma undecidability_from_reducibility {X} {p : X -> Prop} {Y} {q : Y -> Prop} :
  undecidable p -> p ⪯ q -> undecidable q.
Proof.
  unfold undecidable, decidable, decider, reduces, reduction, reflects.
  intros H [f Hf] [d Hd]. eapply H. exists (fun x => d (f x)). intros x. rewrite Hf. eapply Hd.
Qed.

Lemma undecidability_from_complement {X} {p : X -> Prop} :
  undecidable (complement p) -> undecidable p.
Proof.
  intros H Hp. now apply H, dec_compl.
Qed.

Lemma undecidability_to_complement {X} {p : X -> Prop} :
  undecidable (complement p) -> undecidable (complement (complement p)).
Proof.
  intros H Hp. now apply H, dec_compl'.
Qed.

Module UndecidabilityNotations.

Tactic Notation "undec" "from" constr(H) :=
  apply (undecidability_from_reducibility H).

Tactic Notation "reduce" "with" "chain" constr(H) := 
  repeat (apply (reduces_reflexive _) || (eapply reduces_transitive; [ apply H | ])).

Tactic Notation "undec" "from" constr(U) "using" "chain" constr(C) :=
  undec from U; reduce with chain C.

End UndecidabilityNotations.
