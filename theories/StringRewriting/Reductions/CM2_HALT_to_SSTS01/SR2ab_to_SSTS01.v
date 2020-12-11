Require Import List Relation_Operators Operators_Properties Lia.
Import ListNotations.

Require Import Undecidability.StringRewriting.Reductions.CM2_HALT_to_SSTS01.SR2ab.
Require Import Undecidability.StringRewriting.SSTS.

Require Undecidability.StringRewriting.Reductions.CM2_HALT_to_SSTS01.SR2ab_facts.
Require Import Undecidability.StringRewriting.Util.List_facts.

Require Import ssreflect ssrbool ssrfun.

Set Default Proof Using "Type".

Local Arguments rt_trans {A R x y z}.

(* injective pairing *)
Definition enc_pair '(x, y) : nat := (x + y) * (x + y) + y.

Lemma enc_pair_inj {xy x'y'} : enc_pair xy = enc_pair x'y' -> xy = x'y'.
Proof.
  move: xy x'y' => [x y] [x' y'] /=. rewrite pair_equal_spec.
  have : x + y <> x' + y' \/ x + y = x' + y' by lia.
  case; by nia.
Qed.

Opaque enc_pair.

Module Argument.
Section Reduction.
(* given simple rewriting system *)
Context (srs : Srs) (a0: Symbol) (b0: Symbol) (Ha0b0: b0 <> a0).

Import SR2ab_facts (sym_eq_dec).

Definition enc (x: Symbol) : nat :=
  if sym_eq_dec x a0 then 0
  else if sym_eq_dec x b0 then 1
  else 2 + (
    match x with
    | (n, None) => enc_pair (n, 0)
    | (n, Some m) => enc_pair (n, 1 + m)
    end).
    
(* construct a simple semi-Thue system *)
Definition ssts : Ssts := map (fun '((a, b), (c, d)) => ((enc a, enc b), (enc c, enc d))) srs.

Lemma sim_step {s t} : SR2ab.step srs s t -> SSTS.step ssts (map enc s) (map enc t).
Proof.
  case => > ?. rewrite ?map_app /=.
  apply: step_intro. rewrite /ssts in_map_iff.
  eexists. by constructor; last by eassumption.
Qed.

Lemma enc_inj {a b} : enc a = enc b -> a = b.
Proof.
  rewrite /enc. move: (sym_eq_dec a a0) (sym_eq_dec a b0) (sym_eq_dec b a0) (sym_eq_dec b b0).
  move=> [] ? [] ? [] ? [] ? /=; try congruence.
  move: (a) (b) => [? [?|]] [? [?|]] /= [] /enc_pair_inj []; by congruence.
Qed.

Lemma map_enc_inj {s t} : map enc s = map enc t -> s = t.
Proof.
  elim: s t; first by case.
  move=> ? ? IH [|? ?]; first done.
  by move=> /= [/enc_inj -> /IH ->].
Qed.

Lemma inv_sim_step {s t'} : SSTS.step ssts (map enc s) t' -> exists t, t' = map enc t /\ SR2ab.step srs s t.
Proof.
  move Hs': (map enc s) => s' Hs't'.
  case: Hs't' Hs' => u' v' a' b' c' d' H Hs.
  move: H. rewrite /ssts in_map_iff. move=> [[[a b]]] [c d] [[]] ? ? ? ?. subst.
  move=> H. exists (firstn (length u') s ++ c :: d :: skipn (length u' + 2) s). constructor.
  - rewrite map_app /= map_firstn map_skipn Hs.
    rewrite firstn_app (ltac:(lia) : length u' - length u' = 0) firstn_all.
    rewrite skipn_app (ltac:(lia) : length u' + 2 - length u' = 2) skipn_all2 /=; first by lia.
    by rewrite app_nil_r.
  - move: H => /SR2ab_facts.stepI. apply; last done.
    apply: map_enc_inj. rewrite Hs map_app /= map_firstn map_skipn Hs.
    rewrite firstn_app (ltac:(lia) : length u' - length u' = 0) firstn_all.
    rewrite skipn_app (ltac:(lia) : length u' + 2 - length u' = 2) skipn_all2 /=; first by lia.
    by rewrite app_nil_r.
Qed.

Lemma repeat_a0 {n} : repeat 0 n = map enc (repeat a0 n).
Proof.
  elim: n; first done.
  move=> n /= ->. congr cons.
  rewrite /enc. by case: (sym_eq_dec a0 a0).
Qed.

Lemma repeat_b0 {n} : repeat 1 n = map enc (repeat b0 n).
Proof using Ha0b0.
  elim: n; first done.
  move=> n /= ->. congr cons.
  rewrite /enc. case: (sym_eq_dec b0 a0); [done | by case: (sym_eq_dec b0 b0)].
Qed.
  
Lemma transport : SR2ab (srs, a0, b0) -> SSTS01 ssts.
Proof using Ha0b0.
  move=> [n Hn]. exists n. move: Hn. rewrite repeat_a0 repeat_b0. 
  move: (repeat a0 _) (repeat b0 _) => s t. elim.
  - move=> > ?. apply: rt_step. by apply: sim_step.
  - move=> *. by apply rt_refl.
  - move=> *. apply: rt_trans; by eassumption.
Qed.

Lemma inverse_transport : SSTS01 ssts -> SR2ab (srs, a0, b0).
Proof using Ha0b0.
  move=> [n Hn]. exists n. move: Hn. rewrite repeat_a0 repeat_b0.
  move: (repeat a0 _) (repeat b0 _) => s t.
  move Hs': (map enc s) => s'. move Ht': (map enc t) => t' /(@clos_rt_rt1n_iff _ _) Hs't'.
  elim: Hs't' s t Hs' Ht'.
  - move=> ? s t *. subst. have -> : s = t by apply: map_enc_inj. 
    by apply rt_refl.
  - move=> > IH1 _ IH2 *. subst. move: IH1 => /inv_sim_step [t] [? ?]. subst.
    apply /rt_trans; [apply: rt_step; by eassumption | by apply: IH2].
Qed.

End Reduction.
End Argument.

Require Import Undecidability.Synthetic.Definitions.

Theorem reduction : SR2ab ⪯ SSTS01.
Proof.
  exists (fun '(srs, a0, b0) => 
    if SR2ab_facts.sym_eq_dec b0 a0 then [((0, 0), (1, 1))] else Argument.ssts srs a0 b0).
  move=> [[srs a0] b0]. constructor.
  - case: (SR2ab_facts.sym_eq_dec b0 a0).
    + move=> *. exists 1. rewrite /=. apply: rt_step.
      apply: (step_intro _ (u := [])). by left.
    + move=> H /=. by apply: Argument.transport.
  - case: (SR2ab_facts.sym_eq_dec b0 a0).
    + move=> /= -> _. exists 0. by apply: rt_refl.
    + move=> /= H. by apply: Argument.inverse_transport.
Qed.
