(*
  Author(s):
    Andrej Dudenhefner (1)
  Affiliation(s):
    (1) TU Dortmund University, Dortmund, Germany
*)

(*
  Reduction from:
    Strong normalization for closed lambda-terms (SNclosed)
  to:
    Intersection Type Typability (CD_TYP)
*)

(*
  Literature:
  [1] van Raamsdonk, Femke, et al. "Perpetual Reductions in λ-Calculus." Information and Computation 149.2 (1999): 173-225.
*)

Require Import Undecidability.IntersectionTypes.CD.
Require Import Undecidability.IntersectionTypes.Util.CD_facts.
Require Undecidability.IntersectionTypes.Util.CD_sn.
Require Import Undecidability.LambdaCalculus.Util.term_facts.

Require Import PeanoNat Relations List Lia.
Import ListNotations TermNotations.

Import L (term, var, app, lam).
Import Lambda.

Require Import ssreflect.

Set Default Goal Selector "!".

Unset Implicit Arguments.

Lemma Forall_exists_Forall2 {X Y : Type} (P : X -> Y -> Prop) l : Forall (fun x => exists (y : Y), P x y) l ->
  exists l', Forall2 P l l'.
Proof.
  elim.
  - by exists nil.
  - move=> ?? [y ?] _ [l' ?]. exists (y :: l'). by constructor.
Qed.

Inductive typable (M : term): Prop :=
  typable_intro Gamma t : type_assignment Gamma M t -> typable M.

#[local] Notation is_nonzero := (fun n : nat => match n with 0 => False | S _ => True end).

(* has_var_zero M means that ((lam M) N) is a lambda-I redex *)
Definition has_var_zero M := not (allfv is_nonzero M).

(* traditional lambda-I reduction *)
Inductive stepI : term -> term -> Prop :=
  | stepIRed s t     : has_var_zero s -> stepI (app (lam s) t) (subst (scons t var) s)
  | stepILam s s'    : stepI s s' -> stepI (lam s) (lam s')
  | stepIAppL s s' t : stepI s s' -> stepI (app s t) (app s' t)
  | stepIAppR s t t' : stepI t t' -> stepI (app s t) (app s t').

(* specific lambda-K reduction *)
Inductive stepK : term -> term -> Prop :=
  (* lambda-K redex contraction *)
  | stepKRed s t          : normal_form t -> stepK (app (lam (ren S s)) t) s
  | stepKLam s s'         : stepK s s' -> stepK (lam s) (lam s')
  | stepKNAppR s t t'     : neutral (fun _ => True) s -> stepK t t' -> stepK (app s t) (app s t')
  | stepKLAppR s t t'     : stepK t t' -> stepK (app (lam (ren S s)) t) (app (lam (ren S s)) t')
  | stepKAAppL s1 s2 s' t : stepK (app s1 s2) s' -> stepK (app (app s1 s2) t) (app s' t).

(* union of stepI and stepK, which is a class of perpetual reduction strategies [1] *)
#[local] Notation step' M N := (stepI M N \/ stepK M N).
(* reflexive, transitive closure of step' *)
#[local] Notation steps' M N := (clos_refl_trans term (fun M N => step' M N) M N).

Fixpoint merge (Gamma1 Gamma2 : list ty) :=
  match Gamma1 with
  | nil => Gamma2
  | (s1, phi1) :: Gamma1 =>
    match Gamma2 with
    | nil => (s1, phi1) :: Gamma1
    | (s2, phi2) :: Gamma2 => (s1, phi1 ++ (s2 :: phi2)) :: merge Gamma1 Gamma2
    end
  end.

Lemma type_assignment_mergeL Delta Gamma M t :
  type_assignment Gamma M t -> type_assignment (merge Delta Gamma) M t.
Proof.
  apply: type_assignment_weaken.
  elim: Delta Gamma.
  - move=> /= > -> ?. by do 3 econstructor.
  - move=> [??] > IH [|[??] ?] /=.
    + by case.
    + move=> [|?] /=.
      * move=> > [] *. subst. do 3 econstructor; [done|].
        right. apply /in_app_iff. by right.
      * by apply: IH.
Qed.

Lemma type_assignment_mergeR Delta Gamma M t :
  type_assignment Gamma M t -> type_assignment (merge Gamma Delta) M t.
Proof.
  apply: type_assignment_weaken.
  elim: Gamma Delta.
  - by move=> ? [|].
  - move=> [??] > IH [|[??] ?] /=.
    + move=> [|?] /=.
      * move=> > [] *. subst. by do 3 econstructor.
      * move=> *. by do 3 econstructor; eassumption.
    + move=> [|?] /=.
      * move=> > [] *. subst. do 3 econstructor; [done|].
        rewrite in_app_iff. tauto.
      * by apply: IH.
Qed.

Lemma neutral_typableE M : neutral typable M -> forall t, exists Gamma, type_assignment Gamma M t.
Proof.
  elim.
  - move=> x t. exists (repeat (t, nil) (S x)). econstructor.
    + apply: nth_error_repeat. lia.
    + by left.
  - move=> > _ IH [] Gamma s ? t.
    move: (IH (arr s nil t)) => - [Gamma'] ?.
    exists (merge Gamma Gamma'). econstructor.
    + apply: type_assignment_mergeL. by eassumption.
    + by apply: type_assignment_mergeR.
    + done.
Qed.

Lemma neutral_typableI P M : neutral P M -> typable M -> neutral typable M.
Proof.
  elim.
  - by constructor.
  - move=> > _ IH _ [] > /type_assignmentE [] *.
    constructor; [apply: IH|]; apply: typable_intro; eassumption.
Qed.

Lemma typable_lam M : typable M -> typable (lam M).
Proof.
  move=> [] [|[??] ?] ?.
  + move=> /(type_assignment_mergeL [(atom 0, nil)]) ?.
    do 2 econstructor. by eassumption.
  + move=> *. do 2 econstructor. by eassumption.
Qed.

Lemma nf_typable M : normal_form M -> typable M.
Proof.
  elim.
  - move=> x. apply: (typable_intro _ (repeat ((atom 0), nil) (S x)) (atom 0)).
    econstructor; [|by left]. apply: nth_error_repeat. lia.
  - move=> > ?. by apply: typable_lam.
  - move=> x N ??.
    have /neutral_typableE : neutral typable (app (var x) N) by do ? constructor.
    move=> /(_ (atom 0)) [?] ?. econstructor. by eassumption.
  - move=> > /normal_form_app_neutral /neutral_typableI /[apply].
    move=> /neutral_typableE H _ [] Gamma t ?.
    move: (H (arr t nil (atom 0))) => [Gamma'] ?.
    apply: typable_intro. econstructor.
    + apply: (type_assignment_mergeL Gamma Gamma'). by eassumption.
    + by apply: type_assignment_mergeR.
    + done.
Qed.

Lemma arg_K_typable M N Gamma s phi t :
  type_assignment Gamma (lam (ren S M)) (arr s phi t) ->
  typable N ->
  exists Gamma', type_assignment Gamma' (app (lam (ren S M)) N) t.
Proof.
  move=> /type_assignmentE ? [] Gamma' s' ?.
  exists (merge Gamma Gamma').
  econstructor; [|by apply: type_assignment_mergeL; eassumption|by apply: Forall_nil].
  apply: type_assignment_mergeR. constructor.
  apply: type_assignment_fv; [eassumption|].
  apply: allfv_ren. apply: allfv_trivial.
  move=> >. by apply.
Qed.

(* subject expansion for specialized K-reduction *)
Lemma stepK_expansion M N Gamma t : stepK M N -> type_assignment Gamma N t ->
  match M with
  | var _ => exists Gamma', type_assignment Gamma' M t
  | app _ _ => exists Gamma', type_assignment Gamma' M t
  | lam _ => typable M
  end.
Proof.
  have Hty : forall M t,
    match M with
    | var _ => exists Gamma', type_assignment Gamma' M t
    | app _ _ => exists Gamma', type_assignment Gamma' M t
    | lam _ => typable M
    end -> typable M.
  { by move=> [] > => [[? /typable_intro]|[? /typable_intro]|]. }
  move=> H. elim: H Gamma t.
  - move=> > /nf_typable /arg_K_typable H.
    move=> Gamma t /(type_assignment_ren _ ((atom 0, nil):: Gamma) S) H'.
    apply: H. constructor. apply: H'. by case.
  - move=> > ? IH Gamma [] > /type_assignmentE; [done|].
    move=> /IH /Hty. by apply: typable_lam.
  - move=> > ?? IH Gamma t /type_assignmentE [] >.
    move=> ? /IH /Hty {}IH ?.
    apply: neutral_typableE. constructor; [|done].
    apply: neutral_typableI; [|econstructor]; eassumption.
  - move=> > ? IH Gamma t /type_assignmentE [] >.
    move=> ? /IH /Hty {}IH ?. by apply: arg_K_typable; eassumption.
  - move=> > ? IH Gamma t /type_assignmentE [] >.
    move=> /IH [?] ?? H. eexists (merge Gamma _). econstructor.
    + apply: type_assignment_mergeL. by eassumption.
    + by apply: type_assignment_mergeR.
    + apply: Forall_impl H => *. by apply: type_assignment_mergeR.
Qed.

Lemma type_assignment_allfv_substE Gamma1 Gamma2 M N s phi t : 
  allfv (Nat.iter (length Gamma1) (scons True) is_nonzero) M ->
  type_assignment (Gamma1 ++ Gamma2)
    (subst
        (Nat.iter (length Gamma1)
          (fun sigma => scons (var 0) (fun x => ren S (sigma x))) (scons N var)) M) t ->
  type_assignment (Gamma1 ++ (s, phi) :: Gamma2) M t.
Proof.
  move=> HM /(type_assignment_ren_fv _ (Gamma1 ++ (s, phi) :: Gamma2)
    (fun n => match (length Gamma1) - n with 0 => S n | _ => n end)).
  rewrite !simpl_term.
  have : forall (A B C : Prop), A -> (B -> C) -> (A -> B) -> C by auto.
  apply.
  { apply: allfv_subst. apply: allfv_impl HM.
    elim: (Gamma1).
    - by move=> [|x] /=.
    - move=> ?? IH [|x] /=; [done|].
      move=> /IH H'. apply: allfv_ren.
      apply: allfv_impl H'.
      move=> x' /= {}IH > /IH <-.
      by case: (_ - _). }
  congr type_assignment. rewrite -[RHS]subst_var_term.
  apply: ext_allfv_subst_term.
  apply: allfv_impl HM.
  elim: (length Gamma1). { by case. }
  move=> x IH [|?] /=; [done|].
  move=> /IH. rewrite !simpl_term /=.
  move: (Nat.iter _ _ _ _) => [? []|??|?] /=; [|done..].
  move=> <-. congr var. by case: (_ - _).
Qed.

Lemma stepISubst_expansion M N Gamma t : has_var_zero M ->
  type_assignment Gamma (subst (scons N var) M) t -> type_assignment Gamma (app (lam M) N) t.
Proof.
  suff H : forall Gamma1 Gamma2,
    not (allfv (Nat.iter (length Gamma1) (scons True) is_nonzero) M) ->
    type_assignment (Gamma1 ++ Gamma2) (subst (Nat.iter (length Gamma1) (fun sigma => scons (var 0) (funcomp (ren S) sigma)) (scons N var)) M) t ->
    exists s_phi,
    type_assignment (Gamma1 ++ s_phi :: Gamma2) M t /\
    type_assignment Gamma2 N (fst s_phi) /\
    Forall (type_assignment Gamma2 N) (snd s_phi).
  { move=> HM /(H nil) [|[? ?]].
    - move=> H'. apply: HM. apply: allfv_impl H'. by case.
    - move=> [?] [??]. econstructor; [|eassumption..].
      by constructor. }
  (* proof of the generalized statement *)
  move=> Gamma1 Gamma2. elim: M Gamma1 t.
  - move=> y Gamma1 t /= H.
    have <- : length Gamma1 = y.
    { elim: Gamma1 y H=> /=; [by case|].
      move=> ?? IH [|y] /=; [done|].
      by move=> /IH ->. }
    move=> HN. exists (t, nil). clear H.
    split; [|split; [|done]].
    + econstructor; [|by left].
      by rewrite nth_error_app2 ?Nat.sub_diag; [lia|].
    + elim: Gamma1 HN; [done|].
      move=> ? Gamma1 IH /= H. apply: IH.
      move: H=> /(type_assignment_ren_fv _ (Gamma1 ++ Gamma2) Nat.pred).
      rewrite !simpl_term. apply. apply: allfv_ren.
      by apply: allfv_trivial=> - [|?] /=.
  - move=> M1 + M2 + Gamma1 t.
    move=> /(_ Gamma1) + /(_ Gamma1).
    set P := (Nat.iter (length Gamma1) (scons True) is_nonzero).
    move=> IH1 IH2 H /=.
    have HP : forall n, Decidable.decidable (P n).
    { rewrite /P /Decidable.decidable /=.
      elim: (Gamma1) => /=.
      - case; by auto.
      - move=> ?? IH [|?] /=; by auto. }
    move=> /type_assignmentE [] s' phi'.
    have := allfv_dec _ M2 HP.
    have := allfv_dec _ M1 HP.
    move=> [|] HM1 [|] HM2.
    + move: H=> /=. tauto.
    + move: HM1 => /type_assignment_allfv_substE /[apply] H'M1.
      move=> /(IH2 _ HM2) [[s2 phi2]] [?] [??].
      move=> /(@Forall_impl _ _ _ (fun t => IH2 t HM2)).
      move=> /Forall_exists_Forall2 [tys] Hphi'.
      exists (s2, (phi2 ++ concat (map (fun '(s', phi') => s' :: phi') tys))).
      split; [|split].
      * econstructor.
        ** by apply: H'M1.
        ** apply: type_assignment_weaken_assumption; [|by eassumption].
            move=> ?. do ? rewrite  /= in_app_iff; tauto. 
        ** move: Hphi'. elim; [done|].
            move=> ? [??] > /= [?] [??] _ H'. constructor.
            *** apply: type_assignment_weaken_assumption; [|by eassumption].
                move=> ?. do ? rewrite  /= in_app_iff; tauto. 
            *** apply: Forall_impl H' => ?. apply: type_assignment_weaken_assumption.
                move=> ?. do ? rewrite  /= in_app_iff; tauto.
      * by eassumption.
      * apply /Forall_app. split; [by eassumption|].
        apply /Forall_concat /Forall_map. elim: Hphi'; [done|].
        move=> ? [??] > [_] /= [??] *. by do ? constructor.
    + move=> /(IH1 _ HM1) [[s phi]] [?] [??] H1M2 H2M2.
      exists (s, phi). split; [|by split].
      econstructor.
      * by eassumption.
      * by apply: type_assignment_allfv_substE; eassumption.
      * apply: Forall_impl H2M2 => ?. by apply: type_assignment_allfv_substE.
    + move=> /(IH1 _ HM1) [[s1 phi1]] [?] [??].
      move=> /(IH2 _ HM2) [[s2 phi2]] [?] [??].
      move=> /(@Forall_impl _ _ _ (fun t => IH2 t HM2)).
      move=> /Forall_exists_Forall2 [tys] Hphi'.
      exists (s1, (phi1 ++ s2 :: phi2 ++ concat (map (fun '(s', phi') => s' :: phi') tys))).
      split; [|split].
      * econstructor.
        ** apply: type_assignment_weaken_assumption; [|by eassumption].
            move=> ?. do ? rewrite  /= in_app_iff; tauto. 
        ** apply: type_assignment_weaken_assumption; [|by eassumption].
            move=> ?. do ? rewrite  /= in_app_iff; tauto.
        ** move: Hphi'. elim; [done|].
            move=> ? [??] > [?] [??] _ H'. constructor.
            *** apply: type_assignment_weaken_assumption; [|by eassumption].
                move=> ?. do ? rewrite  /= in_app_iff; tauto.
            *** apply: Forall_impl H' => ?.
                apply: type_assignment_weaken_assumption.
                move=> ?. do ? rewrite  /= in_app_iff; tauto.
      * eassumption.
      * apply /Forall_app. split; [done|].
        apply: Forall_cons; [done|].
        apply /Forall_app. split; [done|].
        elim: Hphi'; [done|].
        move=> ? [??] > /= [?] [??] _ ?.
        by constructor; [|apply /Forall_app].
  - move=> M IH Gamma1 [?|s' phi' t] /= HM /type_assignmentE; [done|].
    move=> /(IH ((s', phi') :: Gamma1)) {}IH.
    move: IH => [|[s phi]].
    { move=> H. apply: HM. apply: allfv_impl H. by case. }
    move=> [?] [??]. exists (s, phi). by do 2 constructor.
Qed.

Lemma stepI_expansion M N Gamma t : stepI M N -> type_assignment Gamma N t ->
  type_assignment Gamma M t.
Proof.
  move=> H. elim: H Gamma t.
  - move=> *. by apply: stepISubst_expansion.
  - move=> > _ IH ? [|??] > /type_assignmentE ?; [done|].
    constructor. by apply: IH.
  - move=> > _ IH > /type_assignmentE [] *.
    econstructor; [|eassumption..].
    apply: IH. by eassumption.
  - move=> > _ IH > /type_assignmentE [] > ?? H'. econstructor.
    + by eassumption.
    + by apply: IH.
    + apply: Forall_impl H' => ?. by apply: IH.
Qed.

Lemma step'_step M N : step' M N -> step M N.
Proof.
  case.
  - elim; by auto using step.
  - elim; [|by auto using step..].
    move=> > _. apply: stepSubst'. by rewrite !simpl_term.
Qed.

Lemma has_var_zero_dec M : has_var_zero M \/ exists M', M = ren S M'.
Proof.
  case: (@allfv_dec (fun n => match n with 0 => False | _ => True end) M).
  - move=> [|?]; tauto.
  - move=> H. right. exists (ren Nat.pred M). rewrite simpl_term.
    rewrite -[LHS]ren_id_term. apply: ext_allfv_ren_term.
    by apply: allfv_impl H => - [|?].
  - move=> ?. by left.
Qed.

Lemma step_step' M N : step M N -> exists N', step' M N'.
Proof.
  elim: M N.
  - by move=> > /stepE.
  - move=> [?|M1 M2|M] IHM N IHN ?.
    + move=> /stepE [|[|]] [?] [] => [|/stepE|]; [done..|].
      move=> /IHN [?] [] ? _.
      * eexists. left. apply: stepIAppR. by eassumption.
      * eexists. right. by apply: stepKNAppR; [constructor|eassumption].
    + have [[?]|H] := step_dec (app M1 M2).
      * move=> /IHM [?] []; by eauto using stepK, stepI.
      * move=> /stepE [|[|]] [?] [] => [|/H|]; [done..|].
        move=> /IHN [?] []; [by eauto using stepK, stepI|].
        move=> ? _. eexists. right. apply: stepKNAppR; [|by eassumption].
        move: H => /not_step_normal_form /normal_form_app_neutral.
        by apply: neutral_impl.
    + have [?|[? ->]] := has_var_zero_dec M.
      { by eauto using stepK, stepI. }
      have [[?]|/not_step_normal_form ?] := step_dec N.
      * move=> /IHN [?] []; by eauto using stepK, stepI.
      * by eauto using stepK, stepI.
  - move=> ? IH ? /stepE [?] [/IH [? [?|?]]].
    + by eauto using stepK, stepI.
    + by eauto using stepK, stepI.
Qed.

Lemma step'_or_nf M : (exists N, step' M N) \/ (normal_form M).
Proof.
  by move: (step_dec M) => [[? /step_step']|/not_step_normal_form]; auto.
Qed.

Lemma sn_step'_nf M : sn M -> exists N, steps' M N /\ normal_form N.
Proof.
  elim=> {}M _ IH. case: (step'_or_nf M).
  - move=> [?] /[dup] /step'_step /IH [?] [??] ?.
    eexists. split; [|by eassumption].
    apply: rt_trans; [apply: rt_step|]; by eassumption.
  - move=> ?. eexists. by split; [apply: rt_refl|].
Qed.

Lemma subject_expansion M N : step' M N -> typable N -> typable M.
Proof.
  case.
  + by move=> /stepI_expansion H [] > /H /typable_intro.
  + move=> /stepK_expansion H [] > /H{H}.
    by case: M => > => [[? /typable_intro]|[? /typable_intro]|].
Qed.

Lemma sn_type_assignment M : sn M -> exists Gamma t, type_assignment Gamma M t.
Proof.
  move=> /sn_step'_nf [N] [/clos_rt_rt1n_iff]. elim.
  - move=> ? /nf_typable [] *. do 2 eexists. by eassumption.
  - move=> > /subject_expansion H _ /[apply].
    move=> [?] [?] /typable_intro /H [] *. do 2 eexists. by eassumption.
Qed.

(* weak normalization for step' implies strong normalization for step *)
Theorem wn_step'_sn_step (M N : term) : steps' M N -> normal_form N -> sn M.
Proof.
  move=> /clos_rt_rt1n_iff HMN HN.
  suff: typable M.
  { move=> [] >. by apply: CD_sn.strong_normalization. }
  elim: HMN HN.
  - by apply: nf_typable.
  - move=> > /subject_expansion. by auto.
Qed.

Require Import Undecidability.Synthetic.Definitions.

(* reduction from strong normalization to intersection type typability *)
Theorem reduction : SNclosed ⪯ CD_TYP.
Proof.
  exists (fun '(exist _ M _) => M).
  move=> [t Ht] /=. split.
  - move=> ?. by apply: sn_type_assignment.
  - move=> [?] [?]. by apply: CD_sn.strong_normalization.
Qed.
