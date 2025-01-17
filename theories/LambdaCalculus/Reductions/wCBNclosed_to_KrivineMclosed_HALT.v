(*
  Author(s):
    Andrej Dudenhefner (1)
  Affiliation(s):
    (1) TU Dortmund University, Dortmund, Germany
*)

(*
  Reduction from:
    Weak call-by-name leftmost outermost normalization of closed terms (wCBNclosed)
  to:
    Krivine machine halting for closed terms (KrivineMclosed_HALT)
*)

From Undecidability.LambdaCalculus Require Import
  Lambda Krivine Util.term_facts Util.wCBN_facts Util.Krivine_facts.
From Stdlib Require Import List Relations.
Import Undecidability.L.L (term, var, app, lam).
Import Undecidability.L.Util.L_facts.
Import Lambda (subst, wCBN_step).

From Stdlib Require Import ssreflect.

Set Default Goal Selector "!".

#[local] Notation step := wCBN_step.

Module Argument.

#[local] Arguments clos_refl_trans {A}.

Lemma simulation s t ts ctx : clos_refl_trans step s t -> closed s ->
  halt_cbn ts ctx t -> halt_cbn ts ctx s.
Proof.
  move=> /(clos_rt_rt1n term). elim; [done|].
  move=> > /[dup] /step_closed ? /step_halt_cbn.
  by auto with nocore.
Qed.

Definition many_app s ts := fold_left app ts s.
#[local] Arguments many_app /.

Lemma step_many_app s t ts : step s t -> step (many_app s ts) (many_app t ts).
Proof.
  elim /rev_ind: ts. { done. }
  move=> ?? IH /= ?. rewrite !fold_left_app /=.
  by auto using step with nocore.
Qed.

Lemma inverse_simulation ts ctx s : halt_cbn ts ctx s ->
  exists t', clos_refl_trans step (many_app (flatten (closure ctx s)) (map flatten ts)) (lam t').
Proof.
  elim.
  - move=> > ? [t'] /= Ht'. exists t'.
    move: Ht'. congr clos_refl_trans.
    congr fold_left. rewrite !simpl_term.
    apply: ext_subst_term => n. by rewrite /= !simpl_term.
  - done.
  - done.
  - move=> [? ?] > ? [t'] /= Ht'. exists t'.
    apply: rt_trans; last by eassumption.
    apply: rt_step. apply: step_many_app.
    apply: stepLam'. rewrite !simpl_term /=.
    apply: ext_subst_term. move=> [|n] /=.
    + rewrite !simpl_term. apply: ext_subst_term => n.
      by rewrite /= !simpl_term.
    + by rewrite !simpl_term ren_as_subst_term.
  - move=> >. eexists. by apply: rt_refl.
Qed.

End Argument.

Require Import Undecidability.Synthetic.Definitions.

(* reduction from weak call-by-name leftmost outermost normalization to Krivine machine halting *)
Theorem reduction : wCBNclosed ⪯ KrivineMclosed_HALT.
Proof.
  exists id.
  move=> [s Hs].
  have H's : closed s. { apply: closed_I => k. by rewrite L_subst_Lambda_subst. }
  split.
  - move=> [t]. move: H's => /Argument.simulation /[apply].
    apply. by constructor.
  - move=> /Argument.inverse_simulation [t'] /=. rewrite Hs.
    move=> ?. by exists t'.
Qed.
