(*
  Intersection Type Typability of a term M (type_assignment Gamma M t)
  implies Strong Normalization of M (Acc (fun x y => step y x) M)
*)

Require Import
  Undecidability.IntersectionTypes.CD
  Undecidability.IntersectionTypes.Util.CD_facts
  Undecidability.IntersectionTypes.Util.CD_fundamental.

Require Import Undecidability.LambdaCalculus.Util.term_facts.
Require Import Relations List Wellfounded.Transitive_Closure.

Import L (term, var, app, lam).
Import Lambda.

Import ListNotations TermNotations.

Require Import ssreflect.

Set Default Goal Selector "!".

#[local] Unset Implicit Arguments.

Lemma Acc_clos_trans' {X : Type} (R : X -> X -> Prop) x :
  Acc (clos_trans _ R) x -> Acc R x.
Proof. by elim; eauto using Acc, clos_trans. Qed.

#[local] Arguments Acc_clos_trans {A R x}.

Module Admissible_sn.

Lemma neutral_step M N : neutral sn M -> step M N -> neutral sn N.
Proof.
  move=> + H. elim: H.
  - by move=> > /neutralE [/neutralE].
  - move=> > ? H /neutralE [/H] *. by constructor.
  - move=> > H _ /neutralE [? H']. constructor; [done|].
    by apply: Acc_inv; eassumption.
  - by move=> > _ _ /neutralE.
Qed.

Lemma neutral_sn_app N : sn N -> forall M, neutral sn M -> sn M -> sn (app M N).
Proof.
  elim=> {}N IH1N IH2N M + H. elim: H=> {}M IH1M IH2M HM.
  constructor=> N' /stepE [|[|]] [?] [??]; subst.
  - by move: HM => /neutralE.
  - apply: IH2M; [done|]. by apply: neutral_step; eassumption.
  - by apply: IH2N; [| |constructor].
Qed.

Lemma neutal_sn_sn M : neutral sn M -> sn M.
Proof.
  elim.
  - move=> ?. by constructor=> ? /stepE.
  - move=> *. by apply: neutral_sn_app.
Qed.

(* remember substituted term *)
Inductive head_exp' (P : term -> Prop) : term -> term -> term -> Prop :=
  | head_exp'_lam M N : P N -> head_exp' P (subst (scons N var) M) (app (lam M) N) N
  | head_exp'_app M M' N N' : head_exp' P M M' N' -> P N -> head_exp' P (app M N) (app M' N) N'.

Lemma head_exp'E (P : term -> Prop) M N L : head_exp' P M N L ->
  match N with
  | var _ => False
  | app N1 N2 =>
      (exists N1', N1 = lam N1' /\ N2 = L /\ M = (subst (scons N2 var) N1') /\ P N2) \/
      (exists M1, M = app M1 N2 /\ head_exp' P M1 N1 L /\ P N2) 
  | lam _ => False
  end.
Proof.
  case=> *; [left|right]; by do ? econstructor.
Qed.

Lemma head_exp'_step M N N' L : head_exp' sn M N L -> step N N' ->
  M = N' \/
  (exists M', clos_trans _ step M M' /\ head_exp' sn M' N' L) \/
  (exists L', step L L' /\ (exists M', clos_refl_trans _ step M M' /\ head_exp' sn M' N' L')).
Proof.
  move=> + H. elim: H M L.
  - move=> > /head_exp'E [].
    + move=> [?] [[->]] [->] [->] ?. by left.
    + by move=> [?] [?] [/head_exp'E].
  - move=> > H IH ? ? /head_exp'E [].
    + move=> [?] [?] [?] [??]. subst. right. left.
      move: H => /stepE [?] [??]. subst. eexists.
      split; [|by constructor].
      apply: t_step. by apply: subst_step.
    + move=> [?] [?] [+?].
      move=> /IH [|[|]].
      * move=> ?. subst. by left.
      * move=> [?] [??]. subst. right. left.
        eexists. split; [|constructor; eassumption].
        by apply: t_stepsAppL.
      * move=> [?] [?] [?] [??]. subst. right. right.
        eexists. split; [eassumption|].
        eexists. split; [|constructor; eassumption].
        by apply: rt_stepsAppL.
  - move=> > ? _ ?? /head_exp'E [|].
    + move=> [?] [?] [?] [??]. subst. right. right.
      eexists. split; [eassumption|].
      eexists. split; [|constructor; apply: Acc_inv; eassumption].
      apply: subst_steps=> - [|?] /=; by eauto using clos_refl_trans.
    + move=> [?] [?] [??]. subst. right. left.
      eexists. split; [|constructor; [|apply: Acc_inv]; eassumption].
      apply: t_step. by apply: stepAppR.
  - by move=> > ? _ ?? /head_exp'E.
Qed.

Lemma head_exp'I M N : head_exp sn M N -> exists L, head_exp' sn M N L.
Proof. elim; by firstorder (eauto using head_exp'). Qed.

Lemma head_exp_sn M N : head_exp sn M N -> sn M -> sn N.
Proof.
  move=> /head_exp'I [L] H1 /Acc_clos_trans H2.
  elim: H2 N L H1=> {}M IH1M IH2M N L H'.
  have H : sn L by elim H'.
  elim: H M IH1M IH2M N H' => {}L IH1L IH2L M IH1M IH2M N.
  move=> /head_exp'_step HMN.
  constructor=> N' /HMN [|[|]].
  - move=> <-. apply: Acc_clos_trans'. by constructor.
  - by move=> [M'] [] /clos_trans_flip /IH2M /[apply].
  - move=> [L'] [/IH2L] {}IH2L [M'] [/clos_refl_trans_flip ? /IH2L]. apply.
    + move=> ??. apply: IH1M. apply: clos_rt_t'; eassumption.
    + move=> ????. apply: IH2M. apply: clos_rt_t'; eassumption.
Qed.

Lemma sn_app_var M x : sn (app M (var x)) -> sn M.
Proof. by move=> /snE []. Qed.

Lemma Admissible_sn : Admissible sn.
Proof.
  constructor.
  - by apply: head_exp_sn.
  - by apply: neutal_sn_sn.
  - by apply: sn_app_var.
Qed.

End Admissible_sn.

(* consequence of fundamental theorem *)
Lemma strong_normalization {Gamma M t} : type_assignment Gamma M t -> sn M.
Proof.
  apply: fundamental. by apply: Admissible_sn.Admissible_sn.
Qed.
