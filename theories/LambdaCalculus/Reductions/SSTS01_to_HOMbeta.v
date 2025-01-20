(*
  Author(s):
    Andrej Dudenhefner (TU Dortmund University, Germany)

  Reduction from:
    Simple semi-Thue system 01 rewriting (SSTS01)
  to:
    Higher-Order Matching wrt. beta-equivalence (HOMbeta)
*)

From Stdlib Require Import List PeanoNat Relations Lia.
Import ListNotations.

Require Undecidability.L.L.
Import L (term, var, app, lam).
From Undecidability.LambdaCalculus Require Import Lambda HOMatching Util.facts Util.stlc_facts Util.term_facts.
Require Undecidability.StringRewriting.SSTS.

From Stdlib Require Import ssreflect.

Set Default Proof Using "Type".

(* Set Default Goal Selector "!". *)

#[local] Unset Implicit Arguments.

(* used only for debugging 
Create HintDb shelf.
Hint Extern 99 => shelve : shelf. *)

(* solve allfv constraints *)
Create HintDb allfv.
Hint Resolve allfv_apps allfv_app allfv_subst allfv_ren allfv_var Nat.neq_0_succ allfv_ren_lt : allfv.

(* solve stlc constraints *)
Create HintDb stlc.
Hint Resolve stlc_app Forall2_repeat_r' : stlc.

(* transforms a goal (A -> B) -> C into goals A and B -> C *)
Lemma unnest : forall (A B C : Type), A -> (B -> C) -> (A -> B) -> C.
Proof. auto. Qed.

#[local] Notation lams k M := (Nat.iter k lam M).
#[local] Notation apps M Ns := (fold_left app Ns M).
#[local] Notation arrs ss t := (fold_right arr t ss).
#[local] Notation closed M := (forall (P : nat -> Prop), allfv P M).
#[local] Notation steps := (clos_refl_trans _ step).

#[local] Arguments nth_error_In {A l n x}.

Section Argument.

(* symbols is the number of additional symbols besides 0, 1 *)
Context {rules : list ((nat*nat)*(nat*nat))}.

(* upper bound on rule symbols *)
Definition symbols := 2 + list_sum (map (fun '((a, b), (c, d)) => a+b+c+d) rules).

(* upper bound on all symbols *)
Notation n := (symbols + 6). (* bot, top, bullet, $, 0, 1 *)

Definition sym a := 4 + a.

(* each symbol in rule respects upper bound n *)
Inductive wf_rule (rule : ((nat*nat)*(nat*nat))) : Prop :=
  | wf_rule_intro : 
      sym (fst (fst rule)) < n -> sym (fst (snd rule)) < n ->
      sym (snd (fst rule)) < n -> sym (snd (snd rule)) < n -> wf_rule rule.

(* each rule respects the symbol bound *)
Lemma wf_rules : Forall wf_rule rules.
Proof.
  suff: (Forall (fun rule => sym (fst (fst rule)) < n /\ sym (fst (snd rule)) < n /\
    sym (snd (fst rule)) < n /\ sym (snd (snd rule)) < n) rules).
  { apply: Forall_impl=> *. constructor; lia. }
  rewrite /sym /symbols. elim: (rules); first done.
  move=> [[a b]] [c d] ? IH /=. constructor.
  - move=> /=. lia.
  - apply: Forall_impl IH=> - [[a' b']] [c' d'] /=. lia.
Qed.

Opaque symbols sym.

(* special symbols *)
Definition bot := 0.
Definition top := 1.
Definition bullet := 2.
Definition dollar := 3.
Definition zero := 4.
Definition one := 5.

Definition A := fold_right arr atom (repeat atom n).

(* N .. N M N .. N where M is at position y *)
Definition single (y : nat) (M : term) (N : term) := repeat N (n - 1 - y) ++ M :: (repeat N y).

Definition delta (i : nat) := lam (lams n (apps (var n) (single top (var i) (var 0)))).
Definition pi (i : nat) := lams n (var i).

(* case M of bullet |-> N1, zero |-> N2, one |-> N3, else N *)
Definition case_of (M N1 N2 N3 N : term) := apps M (single bullet N1 (apps M (single zero N2 (apps M (single one N3 N))))).

Lemma nth_error_wf_rule x rule : nth_error rules x = Some rule -> wf_rule rule.
Proof.
  move=> /nth_error_In. by move: (wf_rules)=> /Forall_forall /[apply].
Qed.

Lemma dollar_lt_n : dollar < n.
Proof. rewrite /dollar. lia. Qed.

Lemma dollar_lt_Sn : dollar < S n.
Proof. rewrite /dollar. lia. Qed.

Lemma zero_lt_n : zero < n.
Proof. rewrite /zero. lia. Qed.

Lemma zero_lt_Sn : zero < S n.
Proof. rewrite /zero. lia. Qed.

Lemma one_lt_n : one < n.
Proof. rewrite /one. lia. Qed.

Lemma one_lt_Sn : one < S n.
Proof. rewrite /one. lia. Qed.

Lemma bullet_lt_n : bullet < n.
Proof. rewrite /bullet. lia. Qed.

Lemma bot_lt_n : bot < n.
Proof. rewrite /bot. lia. Qed.

Lemma bot_lt_Sn : bot < S n.
Proof. rewrite /bot. lia. Qed.

Lemma top_lt_n : top < n.
Proof. rewrite /top. lia. Qed.

Lemma zero_neq_dollar : zero <> dollar.
Proof. done. Qed.

Lemma one_neq_dollar : one <> dollar.
Proof. done. Qed.

Lemma bot_neq_dollar : bot <> dollar.
Proof. done. Qed.

#[local] Hint Resolve dollar_lt_n dollar_lt_Sn bullet_lt_n top_lt_n bot_lt_n bot_lt_Sn
  zero_lt_n zero_lt_Sn one_lt_n one_lt_Sn zero_neq_dollar one_neq_dollar bot_neq_dollar : core.

Lemma map_single (f : term -> term) M N x : map f (single x M N) = single x (f M) (f N).
Proof. by rewrite /single !map_app /= !map_repeat. Qed.

Lemma length_single M N i : i < n -> length (single i M N) = n.
Proof. rewrite /single length_app /= !repeat_length. lia. Qed.

Lemma nth_single_eq i N1 N2 M : nth i (rev (single i N1 N2)) M = N1.
Proof.
  rewrite /single rev_app_distr /= -app_assoc.
  by rewrite app_nth2 !length_rev !repeat_length ?Nat.sub_diag.
Qed.

Lemma nth_single_neq i j N1 N2 M : i < n -> j < n -> i <> j -> nth j (rev (single i N1 N2)) M = N2.
Proof.
  move=> ???. rewrite /single rev_app_distr /= -app_assoc.
  have [?|?] : j < i \/ j > i by lia.
  - rewrite app_nth1; first by rewrite length_rev repeat_length.
    rewrite rev_repeat (nth_indep _ _ N2); first by rewrite repeat_length.
    by apply: nth_repeat.
  - rewrite app_nth2 !length_rev !repeat_length; first lia.
    have ->: j - i = S (j - i - 1) by lia.
    rewrite /= rev_repeat (nth_indep _ _ N2); first by (rewrite repeat_length; lia).
    by apply: nth_repeat.
Qed.

Lemma Forall_single P M N i : P M -> P N -> Forall P (single i M N).
Proof.
  move=> ??. rewrite /single. apply /Forall_app. split.
  - by apply /Forall_forall=> ? /(@repeat_spec term) ->.
  - by constructor; [|apply /Forall_forall=> ? /(@repeat_spec term) ->].
Qed.

Lemma Forall2_single P i N1 N2 N'2 N'1 : P N1 N'1 -> P N2 N'2 -> Forall2 P (single i N1 N2) (single i N'1 N'2).
Proof.
  move=> ??. rewrite /single. apply: Forall2_app.
  - by apply: Forall2_repeat.
  - constructor; first done.
    by apply: Forall2_repeat.
Qed.

Lemma stlc_var_atom i Gamma : i < n -> stlc (repeat atom n ++ Gamma) (var i) atom.
Proof.
  move=> ?. apply: stlc_var. rewrite nth_error_app1; first by rewrite repeat_length.
  by rewrite nth_error_repeat.
Qed.

Lemma stlc_pi Gamma i : i < n -> stlc Gamma (pi i) A.
Proof.
  rewrite /pi /A=> ?. apply: stlc_lams.
  - by apply: repeat_length.
  - rewrite rev_repeat. by apply: stlc_var_atom.
Qed.

Lemma pi_closed i : i < n -> closed (pi i).
Proof. move=> /(stlc_pi []). by apply: stlc_closed. Qed.

Hint Resolve allfv_closed pi_closed : allfv.

Lemma ren_pi xi i : i < n -> ren xi (pi i) = pi i.
Proof. move=> ?. by rewrite ren_closed; auto with allfv. Qed.

Lemma subst_pi i sigma : i < n -> subst sigma (pi i) = pi i.
Proof. move=> ?. by rewrite subst_closed; auto with allfv. Qed.

Lemma stlc_apps_single Gamma M i N1 N2 : i < n ->
  stlc Gamma M A -> stlc Gamma N1 atom -> stlc Gamma N2 atom -> stlc Gamma (apps M (single i N1 N2)) atom.
Proof.
  move=> ????. apply: stlc_apps; first by eassumption.
  apply: Forall2_repeat_r'; last by apply: length_single.
  by apply: Forall_single.
Qed.

Lemma stlc_repeat_var_lt Gamma i : i < n -> stlc (repeat atom n ++ Gamma) (var i) atom.
Proof.
  move=> ?. constructor.
  rewrite nth_error_app1; first by rewrite repeat_length.
  by apply nth_error_repeat.
Qed.

Lemma stlc_repeat_var_eq Gamma x t : stlc (repeat atom x ++ t :: Gamma) (var x) t.
Proof.
  apply: stlc_var. by rewrite nth_error_app2 repeat_length ?Nat.sub_diag.
Qed.

Lemma stlc_delta Gamma i : i < n -> stlc Gamma (delta i) (arr A A).
Proof.
  rewrite /delta=> ?. constructor.
  apply: stlc_lams; first by apply: repeat_length.
  rewrite rev_repeat. apply: stlc_apps_single; first done.
  - constructor. by rewrite nth_error_app2 repeat_length ?Nat.sub_diag.
  - by apply: stlc_repeat_var_lt.
  - by apply: stlc_repeat_var_lt.
Qed.

Lemma delta_closed i : i < n -> closed (delta i).
Proof. move=> /(stlc_delta []). by apply: stlc_closed. Qed.

Hint Resolve delta_closed : allfv.

Lemma ren_delta xi i : i < n -> ren xi (delta i) = delta i.
Proof. move=> ?. by rewrite ren_closed; auto with allfv. Qed.

Lemma subst_delta i sigma : i < n -> subst sigma (delta i) = delta i.
Proof. move=> ?. by rewrite subst_closed; auto with allfv. Qed.

Lemma fold_left_lt Ms x : x < length Ms -> fold_left (fun sigma N => scons N sigma) Ms var x = nth x (rev Ms) (var 0).
Proof.
  elim /rev_ind: Ms x.
  - move=> /=. lia.
  - move=> M Ms IH. rewrite fold_left_app rev_app_distr /=.
    move=> [|?] /=; first done.
    rewrite length_app=> /= ?. apply: IH. lia.
Qed.

Lemma fold_left_single_ge N1 N2 i x : i < n -> x >= n -> fold_left (fun sigma N => scons N sigma) (single i N1 N2) var x = var (x - n).
Proof.
  move=> Hi Hx.
  have := length_single N1 N2 i Hi.
  rewrite -length_rev -fold_left_rev_right.
  elim: (rev (single i N1 N2)) (n) x Hx.
  - move=> > ? /= <-. by rewrite Nat.sub_0_r.
  - move=> ?? IH [|?]; first done.
    move=> [|x] /=; first by lia.
    by move=> ? [/IH] ->; first by lia.
Qed.

Lemma fold_left_single_eq N1 N2 i : i < n -> fold_left (fun sigma N => scons N sigma) (single i N1 N2) var i = N1.
Proof.
  move=> ?. rewrite fold_left_lt.
  - by rewrite length_single.
  - by apply: nth_single_eq.
Qed.

Lemma fold_left_single_neq N1 N2 i x : i < n -> x < n -> x <> i -> fold_left (fun sigma N => scons N sigma) (single i N1 N2) var x = N2.
Proof.
  move=> ???. rewrite fold_left_lt.
  - by rewrite length_single.
  - apply: nth_single_neq; lia.
Qed.

Lemma steps_apps_lams_n_single M N1 N2 i :
  i < n -> steps (apps (lams n M) (single i N1 N2)) (subst (fold_left (fun sigma N => scons N sigma) (single i N1 N2) var) M).
Proof. move=> ?. apply: stepsReds'. by apply: length_single. Qed.

Lemma steps_pi_eq i N1 N2 : i < n -> steps (apps (pi i) (single i N1 N2)) N1.
Proof.
  move=> ?. rewrite /pi. apply: rt_trans; first by apply: steps_apps_lams_n_single.
  apply: steps_refl. by rewrite /= fold_left_single_eq.
Qed.

Lemma steps_pi_neq i j N1 N2 : i < n -> j < n -> i <> j -> steps (apps (pi i) (single j N1 N2)) N2.
Proof.
  move=> ???. rewrite /pi. apply: rt_trans; first by apply: steps_apps_lams_n_single.
  apply: steps_refl. by rewrite /= fold_left_single_neq.
Qed.

Lemma step_delta i M : i < n -> steps (app (delta i) M) (lams n (apps (ren (Nat.add n) M) (single top (var i) (var bot)))).
Proof.
  move=> ?. apply: rt_trans; first by apply: stepsRed.
  rewrite subst_lams subst_apps /= iter_up_ge; first done.
  rewrite Nat.sub_diag map_single /=.
  rewrite iter_up_lt; first done.
  rewrite iter_up_lt; first done.
  by apply: steps_refl.
Qed.

Lemma steps_delta_eq i M N1 N2 : S i < n ->
  steps (apps (app (delta (S i)) M) (single (S i) N1 N2)) (apps M (single top N1 N2)).
Proof.
  move=> ?. apply: rt_trans.
  { apply: stepsAppsL. by apply: step_delta. }
  apply: rt_trans; first by apply: steps_apps_lams_n_single.
  apply: steps_refl. rewrite subst_apps !map_single /=. congr (apps _ _).
  - rewrite fold_left_single_eq; first done.
    by rewrite fold_left_single_neq.
  - rewrite subst_ren_term /= -[RHS]subst_var_term. apply: ext_subst_term.
    move=> ?. rewrite fold_left_single_ge; [..|congr var]; lia.
Qed.

Lemma steps_delta_pi_top i : i < n -> steps (app (delta i) (pi top)) (pi i).
Proof.
  move=> ?. apply: rt_trans; first by apply: step_delta.
  apply: stepsLams. rewrite ren_pi; first done. by apply: steps_pi_eq.
Qed.

Hint Resolve Forall_single pi_closed delta_closed : allfv.
Hint Resolve stlc_delta stlc_var_atom stlc_apps_single stlc_pi Forall_single length_single stlc_repeat_var_lt stlc_repeat_var_eq stlc_var stlc_lam : stlc.
Hint Extern 1 (stlc _ (app _ _) _) => simple eapply stlc_app : stlc.

Lemma normal_form_pi i : normal_form (pi i).
Proof. rewrite /pi. elim: (n)=> *; by do ? constructor. Qed.

Lemma steps_pi_elim {P : Prop} {M M' : term} {i : nat} : steps M M' -> (steps M' (pi i) -> P) -> steps M (pi i) -> P.
Proof. apply: steps_nf_elim. by apply: normal_form_pi. Qed.

Inductive nf : term -> Prop :=
  | nf_lam M : normal_form M -> nf (lam M)
  | nf_neutral M : neutral normal_form M -> nf M.

Lemma normal_form_nf M : normal_form M -> nf M.
Proof.
  move=> /normal_form_neutral [].
  - by apply: nf_neutral.
  - move=> [?] [->]. by apply: nf_lam.
Qed.

Lemma stlc_normal_form_pi M : normal_form M -> stlc [] M A -> exists i, i < n /\ M = pi i.
Proof.
  move=> HM.
  suff: forall k, stlc (repeat atom k) M A -> exists i, i < k + n /\ M = pi i by move=> /(_ 0); apply.
  rewrite /A /pi. elim /(Nat.measure_induction _ term_size): M HM (n).
  move=> M + /normal_form_nf HM. case: HM.
  - move=> {}M + IH [|n] k /stlcE []; first done.
    move=> /IH {}IH ?? [<- <-] /(IH _ n (S k)) [] /=; first done.
    move=> i [? ->]. exists i. by split; [lia|].
  - move=> {}M /neutralE' [x] [Ms] [-> _] IH n k /stlc_appsE [ss] [HMs] /stlcE.
    move=> /[dup] /nth_error_Some'. rewrite arrs_arrs repeat_length.
    move=> /[dup] ? /(@nth_error_repeat ty) -> [] /(arrs_inj []).
    move: ss Ms n HMs IH=> [|??] [|??] [|?] /Forall2_length; [|done..].
    move=> *. rewrite Nat.add_0_r. by exists x.
Qed.

Lemma stlc_pi_intro i M : stlc [] M A -> (forall j, j < n -> j <> i -> steps M (pi j) -> False) -> steps M (pi i).
Proof.
  move=> /[dup] /stlc_wn [N] /[dup] H2N /stlc_steps + H1N => /[apply].
  move: H1N => /stlc_normal_form_pi /[apply] - [j] [??] H. subst N.
  have [?|?] : j = i \/ j <> i by lia.
  - by subst j.
  - exfalso. by apply: H; eassumption.
Qed.

Lemma subst_case_of sigma M N1 N2 N3 N : subst sigma (case_of M N1 N2 N3 N) =
  case_of (subst sigma M) (subst sigma N1) (subst sigma N2) (subst sigma N3) (subst sigma N).
Proof. rewrite /case_of. by do 3 rewrite !subst_apps !map_single. Qed.

Lemma steps_case_of_head M M' N1 N2 N3 N : steps M M' -> steps (case_of M N1 N2 N3 N) (case_of M' N1 N2 N3 N).
Proof.
  move=> ?. rewrite /case_of.
  apply: rt_trans.
  { apply: stepsAppsL. by eassumption. }
  apply: stepsAppsR. apply: Forall2_single; first by apply: rt_refl.
  apply: rt_trans.
  { apply: stepsAppsL. by eassumption. }
  apply: stepsAppsR. apply: Forall2_single; first by apply: rt_refl.
  apply: rt_trans.
  { apply: stepsAppsL. by eassumption. }
  by apply: rt_refl.
Qed.

Lemma steps_case_of_bullet N1 N2 N3 N : steps (case_of (pi bullet) N1 N2 N3 N) N1.
Proof. by apply: steps_pi_eq. Qed.

Lemma steps_case_of_L N1 N2 N3 N : steps (case_of (pi zero) N1 N2 N3 N) N2.
Proof. by apply: rt_trans; [apply: steps_pi_neq|apply: steps_pi_eq]. Qed.

Lemma steps_case_of_R N1 N2 N3 N : steps (case_of (pi one) N1 N2 N3 N) N3.
Proof. by apply: rt_trans; [apply: steps_pi_neq|apply: rt_trans; [apply: steps_pi_neq|apply: steps_pi_eq]]. Qed.

Lemma steps_case_of_fst M N1 N2 N3 N N1' : steps N1 N1' -> steps (case_of M N1 N2 N3 N) (case_of M N1' N2 N3 N).
Proof.
  move=> H. rewrite /case_of. apply: stepsAppsR. apply: Forall2_single; first done.
  by apply: rt_refl.
Qed.

Lemma steps_case_of_snd M N1 N2 N3 N N2' : steps N2 N2' -> steps (case_of M N1 N2 N3 N) (case_of M N1 N2' N3 N).
Proof.
  move=> H. rewrite /case_of.
  apply: stepsAppsR. apply: Forall2_single; first by apply: rt_refl.
  apply: stepsAppsR. apply: Forall2_single; first by done.
  by apply: rt_refl.
Qed.

Lemma steps_case_of_trd M N1 N2 N3 N N3' : steps N3 N3' -> steps (case_of M N1 N2 N3 N) (case_of M N1 N2 N3' N).
Proof.
  move=> H. rewrite /case_of.
  apply: stepsAppsR. apply: Forall2_single; first by apply: rt_refl.
  apply: stepsAppsR. apply: Forall2_single; first by apply: rt_refl.
  apply: stepsAppsR. apply: Forall2_single; first by done.
  by apply: rt_refl.
Qed.

Lemma allfv_case_of P M N1 N2 N3 N : allfv P M -> allfv P N1 -> allfv P N2 -> allfv P N3 -> allfv P N -> allfv P (case_of M N1 N2 N3 N).
Proof. move=> *. rewrite /case_of. auto 8 with allfv. Qed.

Lemma stlc_case_of Gamma M N1 N2 N3 N : stlc Gamma M A -> stlc Gamma N1 atom -> stlc Gamma N2 atom -> stlc Gamma N3 atom -> stlc Gamma N atom ->
  stlc Gamma (case_of M N1 N2 N3 N) atom.
Proof.
  move=> *. rewrite /case_of. apply: stlc_apps_single; [done..|].
  apply: stlc_apps_single; [done..|].
  by apply: stlc_apps_single.
Qed.

Lemma steps_pi_full i : i < n -> steps (apps (pi i) (map var (rev (seq 0 n)))) (var i).
Proof.
  move=> ?. apply: rt_trans.
  { apply: stepsReds'. by rewrite length_map length_rev length_seq. }
  apply: steps_refl. rewrite /= fold_left_lt.
  - by rewrite length_map length_rev length_seq.
  - by rewrite map_rev rev_involutive map_nth seq_nth.
Qed.

Opaque A pi single delta case_of.

(* Gamma_A facts *)

Definition A_star := arrs [arr A A; arr (arr A A) A] A.
Definition A_0R := arrs [arr A A; A] A. (* A_0 and A_R *)
Definition A_1 := A.

Definition Gamma_A m := repeat (arr A A) m ++ [A_star; A] ++ repeat A_0R (1 + length rules).

Lemma length_Gamma_A m : length (Gamma_A m) = m + 3 + length rules.
Proof. rewrite /Gamma_A !length_app !repeat_length /=. lia. Qed.

Lemma Gamma_A_pos m x : x < m -> nth_error (Gamma_A m) x = Some (arr A A).
Proof.
  move=> ?. rewrite /Gamma_A nth_error_app1 ?repeat_length; first done.
  by apply: nth_error_repeat.
Qed.

Lemma Gamma_A_space m : nth_error (Gamma_A m) m = Some A_star.
Proof.
  rewrite /Gamma_A nth_error_app2 ?repeat_length; first lia.
  by have ->: m - m = 0 by lia.
Qed.

Lemma Gamma_A_fin m : nth_error (Gamma_A m) (S m) = Some A.
Proof.
  rewrite /Gamma_A nth_error_app2 ?repeat_length; first lia.
  by have ->: S m - m = 1 by lia.
Qed.

Lemma Gamma_A_init m : nth_error (Gamma_A m) (S (S m)) = Some A_0R.
Proof.
  rewrite /Gamma_A nth_error_app2 ?repeat_length; first lia.
  by have ->: S (S m) - m = 2 by lia.
Qed.

Lemma Gamma_A_rule m x : x < m + 3 + length rules -> x > S m -> nth_error (Gamma_A m) x = Some A_0R.
Proof.
  move=> ??. rewrite /Gamma_A nth_error_app2 ?repeat_length; first lia.
  have ->: x - m = 2 + (x - m - 2) by lia.
  apply: nth_error_repeat. lia.
Qed.

Inductive Gamma_A_vals (m : nat) (x : nat) : Prop :=
  | Gamma_A_vals_pos : x < m -> nth_error (Gamma_A m) x = Some (arr A A) -> Gamma_A_vals m x
  | Gamma_A_vals_space : x = m -> nth_error (Gamma_A m) x = Some A_star -> Gamma_A_vals m x
  | Gamma_A_vals_fin : x = S m -> nth_error (Gamma_A m) x = Some A -> Gamma_A_vals m x
  | Gamma_A_vals_init : x = S (S m) -> nth_error (Gamma_A m) x = Some A_0R -> Gamma_A_vals m x
  | Gamma_A_vals_rule : x > S (S m) -> nth_error (Gamma_A m) x = Some A_0R -> Gamma_A_vals m x.

Lemma Gamma_A_vals_spec m x : x < length (Gamma_A m) -> Gamma_A_vals m x.
Proof.
  rewrite length_Gamma_A=> ?.
  have [?|[<-|[->|[->|?]]]] : x < m \/ x = m \/ x = S m \/ x = S (S m) \/ x > S (S m) by lia.
  - by apply: Gamma_A_vals_pos; [|apply: Gamma_A_pos].
  - by apply: Gamma_A_vals_space; [|apply: Gamma_A_space].
  - by apply: Gamma_A_vals_fin; [|apply: Gamma_A_fin].
  - by apply: Gamma_A_vals_init; [|apply: Gamma_A_init].
  - apply: Gamma_A_vals_rule; [|apply: Gamma_A_rule]; lia.
Qed.

(* sigma_F facts *)

Definition F_star : term := lam (lam (app (var 0) (lam (var 0)))).
Definition F_0 : term := lam (lam (var 0)).
Definition F_R : term := lam (var 0).

Definition sigma_F m := (fun x => nth x ((repeat (lam (var 0)) m) ++ [F_star; var m; F_0] ++ repeat F_R (length rules)) (var x)).

Lemma sigma_F_pos m i : i < m -> sigma_F m i = lam (var 0).
Proof.
  move=> ?. rewrite /sigma_F app_nth1 ?repeat_length; first done.
  rewrite (nth_indep _ _ (lam (var 0))) ?repeat_length; first done.
  by apply: nth_repeat.
Qed.

Lemma sigma_F_space m : sigma_F m m = F_star.
Proof.
  rewrite /sigma_F app_nth2 ?repeat_length; first lia.
  by have ->: m - m = 0 by lia.
Qed.

Lemma sigma_F_fin m : sigma_F m (S m) = var m.
Proof.
  rewrite /sigma_F app_nth2 ?repeat_length; first lia.
  by have ->: S m - m = 1 by lia.
Qed.

Lemma sigma_F_init m : sigma_F m (S (S m)) = F_0.
Proof.
  rewrite /sigma_F app_nth2 ?repeat_length; first lia.
  by have ->: S (S m) - m = 2 by lia.
Qed.

Lemma sigma_F_rule m x : x < length (Gamma_A m) -> x > S (S m) -> sigma_F m x = F_R.
Proof.
  rewrite length_Gamma_A=> ??. rewrite /sigma_F app_nth2 ?repeat_length; first lia.
  rewrite (nth_indep _ _ F_R).
  { rewrite /= repeat_length. lia. }
  have ->: x - m = 3 + (x - m - 3) by lia.
  by apply: nth_repeat.
Qed.

Lemma stlc_F_0 Gamma : stlc Gamma F_0 A_0R.
Proof. rewrite /F_0 /A_0R. by do ? econstructor. Qed.

Lemma stlc_F_R Gamma : stlc Gamma F_R A_0R.
Proof. rewrite /F_R /A_0R. by do ? econstructor. Qed.

Lemma stlc_F_star Gamma : stlc Gamma F_star A_star.
Proof. rewrite /F_star /A_star. by do ? econstructor. Qed.

Hint Resolve stlc_F_0 stlc_F_star stlc_F_R Forall2_cons Forall2_nil : stlc.

Lemma ren_S_sigma_F m x : x < length (Gamma_A m) -> ren S (sigma_F m x) = sigma_F (S m) (S x).
Proof.
  rewrite /sigma_F /= -(map_nth (ren S))=> H.
  rewrite map_app /= !map_repeat /=.
  apply: nth_indep.
  move: H. by rewrite /Gamma_A !length_app /= !repeat_length.
Qed.

Lemma steps_F_0 {N1 N2} : steps (apps F_0 [N1; N2]) N2.
Proof.
  apply: rt_trans.
  - apply: stepsAppL. by apply: stepsRed.
  - by apply: stepsRed.
Qed.

Lemma steps_F_R {N1 N2} : steps (apps F_R [N1; N2]) (app N1 N2).
Proof.
  apply: stepsAppL. by apply: stepsRed.
Qed.

Lemma steps_F_star N M : steps (apps F_star [N; M]) (app M (lam (var 0))).
Proof.
  apply: rt_trans.
  - rewrite /=. apply: stepsAppL. by apply: stepsRed.
  - by apply: stepsRed.
Qed.

Opaque F_star F_0 F_R.

(* sigma_H facts *)

Definition H_star : term := lams (2 + n) (apps (var n) (delta bullet :: single dollar (var dollar) (var 0))).
Definition H_0 : term := lams 2 (lams n (apps (var n) (single one (var dollar) (var bot)))).
Definition H_R : term := lams 2 (lams n (apps (var (S n)) (pi top :: single bullet (apps (var n) (single one (var one) (var bot))) (var bot)))).
Definition H_1 : term := pi one.

Definition sigma_H m := (fun x => nth x ((repeat (delta bullet) m) ++ [H_star; H_1; H_0] ++ repeat H_R (length rules)) (var x)).

Lemma sigma_H_pos m x : x < m -> sigma_H m x = delta bullet.
Proof.
  move=> ?. rewrite /sigma_H app_nth1 ?repeat_length; first done.
  rewrite (nth_indep _ _ (delta bullet)) ?repeat_length; first done.
  by apply: nth_repeat.
Qed.

Lemma sigma_H_space m : sigma_H m m = H_star.
Proof.
  rewrite /sigma_H app_nth2 ?repeat_length; first lia.
  by have ->: m - m = 0 by lia.
Qed.

Lemma sigma_H_fin m : sigma_H m (S m) = H_1.
Proof.
  rewrite /sigma_H app_nth2 ?repeat_length; first lia.
  by have ->: S m - m = 1 by lia.
Qed.

Lemma sigma_H_init m : sigma_H m (S (S m)) = H_0.
Proof.
  rewrite /sigma_H app_nth2 ?repeat_length; first lia.
  by have ->: S (S m) - m = 2 by lia.
Qed.

Lemma sigma_H_rule m x : x < length (Gamma_A m) -> x > S (S m) -> sigma_H m x = H_R.
Proof.
  rewrite length_Gamma_A=> ??.
  rewrite /sigma_H app_nth2 ?repeat_length; first lia.
  rewrite (nth_indep _ _ H_R).
  { rewrite /= repeat_length. lia. }
  have ->: x - m = 3 + (x - m - 3) by lia.
  by apply: nth_repeat.
Qed.

Lemma stlc_H_1 Gamma : stlc Gamma H_1 A.
Proof.
  by apply: stlc_pi.
Qed.

Lemma stlc_H_star Gamma : stlc Gamma H_star A_star.
Proof.
  rewrite /H_star /=. do 2 constructor.
  apply: stlc_lams; first by rewrite repeat_length.
  rewrite rev_repeat. by auto with stlc.
Qed.

Lemma stlc_H_0 Gamma : stlc Gamma H_0 A_0R.
Proof.
  rewrite /H_0 /=. do 2 constructor. apply: stlc_lams; first by rewrite repeat_length.
  rewrite rev_repeat. by auto with stlc.
Qed.

Lemma stlc_H_R Gamma : stlc Gamma H_R A_0R.
Proof.
  rewrite /H_R /=. do 2 constructor. apply: stlc_lams; first by rewrite repeat_length.
  rewrite rev_repeat.
  have ? : forall t, stlc (repeat atom n ++ A :: t :: Gamma) (var (S n)) t.
  { constructor. rewrite nth_error_app2 repeat_length; first lia.
    by have ->: S n - n = 1 by lia. }
  by auto with stlc.
Qed.

Lemma stlc_sigma_H m x s : nth_error (Gamma_A m) x = Some s -> stlc [] (sigma_H m x) s.
Proof.
  move=> /[dup] /nth_error_Some' /Gamma_A_vals_spec [].
  - move=> /sigma_H_pos -> -> [<-]. by apply: stlc_delta.
  - move=> -> -> [<-]. rewrite sigma_H_space. by apply: stlc_H_star.
  - move=> -> -> [<-]. rewrite sigma_H_fin. by apply: stlc_H_1.
  - move=> -> -> [<-]. rewrite sigma_H_init. by apply: stlc_H_0.
  - move=> ? /[dup] /nth_error_Some' ? -> [<-].
    rewrite sigma_H_rule; [done..|].
    by apply: stlc_H_R.
Qed.

Lemma stlc_subst_sigma_H m M t : 
  stlc (Gamma_A m) M t -> stlc [] (subst (sigma_H m) M) t.
Proof.
  move=> /stlc_subst. apply. by apply: stlc_sigma_H.
Qed.

Lemma H_1_closed : closed H_1.
Proof. apply: stlc_closed. by apply: stlc_H_1. Qed.

Lemma H_star_closed : closed H_star.
Proof. apply: stlc_closed. by apply: stlc_H_star. Qed.

Lemma H_0_closed : closed H_0.
Proof. apply: stlc_closed. by apply: stlc_H_0. Qed.

Lemma H_R_closed : closed H_R.
Proof. apply: stlc_closed. by apply: stlc_H_R. Qed.

Lemma sigma_H_closed m x : x < length (Gamma_A m) -> closed (sigma_H m x).
Proof.
  move=> /nth_error_Some.
  case E: (nth_error (Gamma_A m) x); last done.
  move: E => /stlc_sigma_H /stlc_allfv_not_None + _ ?.
  apply: allfv_impl. by case.
Qed.

Lemma subst_sigma_H_closed m M t : stlc (Gamma_A m) M t -> closed (subst (sigma_H m) M).
Proof.
  move=> /stlc_subst_sigma_H /stlc_allfv_not_None + P.
  apply: allfv_impl. by case.
Qed.

Hint Resolve stlc_H_0 stlc_H_1 stlc_H_star stlc_H_R : stlc.
Hint Resolve H_R_closed H_0_closed H_star_closed H_1_closed sigma_H_closed subst_sigma_H_closed : allfv.

Lemma steps_H_0 {N1 N2} :
  steps (app (app H_0 N1) N2)
    (lams n (apps (ren (Nat.add n) N2) (single one (var dollar) (var bot)))).
Proof.
  apply: rt_trans.
  { rewrite /H_0 /=. apply: stepsAppL. by apply: stepsRed. }
  apply: rt_trans.
  { rewrite /=. by apply: stepsRed. }
  apply: steps_refl.
  rewrite subst_subst_term!subst_lams !subst_apps !map_single /=.
  by rewrite iter_up_eq !iter_up_lt.
Qed.

Lemma steps_H_R {N1 N2} :
  steps (app (app H_R N1) N2)
    (lams n (apps (ren (Nat.add n) N1) (pi top :: single bullet (apps (ren (Nat.add n) N2) (single one (var one) (var bot))) (var bot)))).
Proof.
  apply: rt_trans.
  { rewrite /H_R /=. apply: stepsAppL. by apply: stepsRed. }
  apply: rt_trans.
  { rewrite /=. by apply: stepsRed. }
  rewrite !subst_lams !subst_apps !map_single /= !subst_apps !map_single /=.
  rewrite !subst_pi; [done..|].
  rewrite iter_up_eq !(iter_up_ge n (S n)); first lia.
  have -> : S n - n = 1 by lia.
  rewrite /= Nat.add_0_r iter_up_eq /=.
  apply: stepsLams. apply: steps_refl. congr (apps _ _).
  - rewrite !iter_up_lt; [done..|].
    by rewrite /= !iter_up_lt.
  - congr app. rewrite ren_ren_term subst_ren_term /= [RHS]ren_as_subst_term.
    apply: ext_subst_term=> x.
    rewrite iter_up_ge; first lia.
    by have ->: n + S x - n = S x by lia.
Qed.

Lemma steps_H_star M1 M2 : steps (apps H_star [M1; M2]) (lams n (apps (ren (Nat.add n) M2) (delta bullet :: single dollar (var dollar) (var 0)))).
Proof.
  apply: rt_trans.
  { rewrite /H_star /=. apply: stepsAppL. by apply: stepsRed. }
  apply: rt_trans.
  { rewrite /=. by apply: stepsRed. }
  rewrite !subst_lams !subst_apps !map_single /= !subst_delta; [done..|].
  rewrite iter_up_eq !iter_up_lt; [done..|].
  apply: stepsLams. apply: steps_refl. congr (apps _ _).
  - by rewrite /= !iter_up_lt.
  - congr app. by rewrite /= Nat.add_0_r iter_up_eq.
Qed.

Lemma ren_S_sigma_H m x : x < length (Gamma_A m) -> ren S (sigma_H m x) = sigma_H (S m) (S x).
Proof.
  move=> Hx.
  rewrite ren_closed; first by auto with allfv.
  rewrite /sigma_H /=. apply: nth_indep.
  move: Hx. by rewrite /Gamma_A /= !length_app /= !repeat_length.
Qed.

Lemma steps_subst_sigma_H_pi_intro m M x N1 N2 i :
  stlc (Gamma_A m) M A ->
  allfv (fun y => y <> x) N2 ->
  S i < n ->
  steps (apps (subst (sigma_H m) M) (single (S i) N1 N2)) (var x) ->
  steps (subst (sigma_H m) M) (pi (S i)).
Proof.
  move=> HM HN2 ? H. apply: stlc_pi_intro; first by apply: stlc_subst_sigma_H.
  move=> ??? H'M.
  apply: steps_var_elim H. { apply: stepsAppsL. by eassumption. }
  apply: steps_var_elim; first by apply: steps_pi_neq.
  by apply: steps_var_absurd.
Qed.

Opaque H_star H_0 H_R H_1.

(* sigma_G facts *)

Definition G_pos (m k : nat) :=
  match k with
  | 0 => repeat (delta bullet) m
  | S k => map (fun x => if Nat.eqb k x then delta zero else if Nat.eqb k (S x) then delta one else delta bullet) (seq 0 m)
  end.

Definition G_star := lams (2 + n) (case_of (app (var (S n)) (pi top))
  (* if h (pi top) is bullet then *)
  (apps (app (var n) (delta bullet)) (single zero
    (* if M (delta bullet) is zero then zero *)
    (var zero)
    (* else *)
    (apps (app (var n) (delta bullet)) (single dollar 
      (* if M (delta bullet) is dollar and M (delta zero) is one then dollar *)
      (apps (app (var n) (delta zero)) (single one (var dollar) (var bot))) (var bot)))))
  (* if h (pi top) is zero and M (delta one) is zero then one *)
  (apps (app (var n) (delta one)) (single zero (var one) (var bot)))
  (* if h (pi top) is one and M (delta bullet) is zero then zero *)
  (apps (app (var n) (delta bullet)) (single zero (var zero) (var bot)))
  (* else bot *)
  (var bot)).

Definition G_1 := pi one.

Definition G_0 :=
  lams (2 + n) (case_of (app (var (S n)) (pi top))
    (* bullet |-> if x is zero then * else if is one then $ *)
    (apps (var n) (single zero (var zero) (apps (var n) (single one (var dollar) (var bot)))))
    (* zero |-> if x is zero then one *)
    (apps (var n) (single zero (var one) (var bot)))
    (* one |-> if x is d then b *)
    (apps (var n) (single zero (var zero) (var bot)))
    (* else fail *)
    (var bot)).

Definition G_R (rule : (nat*nat)*(nat*nat)) :=
  lams (2 + n) (case_of (app (var (S n)) (pi top))
    (* bullet |-> no change *)
    (apps (var n) (map var (rev (seq 0 n))))
    (* zero |-> if x is c then a *)
    (apps (var n) (single (sym (fst (snd rule))) (var (sym (fst (fst rule)))) (var 0)))
    (* one |-> if x is d then b *)
    (apps (var n) (single (sym (snd (snd rule))) (var (sym (snd (fst rule)))) (var 0)))
    (* else fail *)
    (var bot)).

Definition sigma_G m k := (fun x => nth x (G_pos m k ++ [G_star; G_1; G_0] ++ map G_R rules) (var x)).

Lemma length_G_pos m k : length (G_pos m k) = m.
Proof.
  case: k=> [|k] /=.
  - by rewrite repeat_length.
  - by rewrite length_map length_seq.
Qed.

Lemma nth_G_pos_neq m k x : x < m -> S x <> k -> S (S x) <> k -> nth x (G_pos m k) (var x) = delta bullet.
Proof.
  move: k => [|k] ???; rewrite /G_pos.
  - rewrite (nth_indep _ _ (delta bullet)).
    + by rewrite repeat_length.
    + by rewrite nth_repeat.
  - set f := (fun _ => _).
    rewrite (nth_indep _ _ (f 0)); first by rewrite length_map length_seq.
    rewrite map_nth seq_nth; first done.
    rewrite /f /=.
    case E1: (Nat.eqb k x).
    { move=> /Nat.eqb_eq in E1. lia. }
    case E2: (Nat.eqb k (S x)).
    { move=> /Nat.eqb_eq in E2. lia. }
    done.
Qed.

Lemma sigma_G_pos_0 m x : x < m -> sigma_G m 0 x = delta bullet.
Proof.
  move=> ?. rewrite /sigma_G app_nth1; first by rewrite length_G_pos.
  rewrite /G_pos (nth_indep _ _ (delta bullet)).
  - by rewrite repeat_length.
  - by rewrite nth_repeat.
Qed.

Lemma sigma_G_pos_S m k x : x < m -> sigma_G m (S k) x = if Nat.eqb k x then delta zero else if Nat.eqb k (S x) then delta one else delta bullet.
Proof.
  move=> ?. rewrite /sigma_G app_nth1; first by rewrite length_G_pos.
  case E1: (Nat.eqb k x).
  { move=> /Nat.eqb_eq in E1. rewrite E1.
    rewrite /G_pos. set f := fun _ => _.
    rewrite (nth_indep _ _ (f 0)); first by rewrite length_map length_seq.
    rewrite map_nth seq_nth /=; first done.
    by rewrite /f Nat.eqb_refl. }
  move=> /Nat.eqb_neq in E1.
  case E2: (Nat.eqb k (S x)).
  { move=> /Nat.eqb_eq in E2. rewrite E2.
    rewrite /G_pos. set f := fun _ => _.
    rewrite (nth_indep _ _ (f 0)); first by rewrite length_map length_seq.
    rewrite map_nth seq_nth /=; first done.
    rewrite /f Nat.eqb_refl.
    by have /Nat.eqb_neq ->: S x <> x by lia. }
  move=> /Nat.eqb_neq in E2.
  by rewrite nth_G_pos_neq; [lia..|].
Qed.

Lemma sigma_G_fin m k : sigma_G m k (S m) = G_1.
Proof.
  rewrite /sigma_G app_nth2 length_G_pos; first lia.
  by have ->: S m - m = 1 by lia.
Qed.

Lemma sigma_G_star m k : sigma_G m k m = G_star.
Proof.
  rewrite /sigma_G app_nth2 length_G_pos; first done.
  by rewrite Nat.sub_diag.
Qed.

Lemma sigma_G_init m k : sigma_G m k (S (S m)) = G_0.
Proof.
  rewrite /sigma_G app_nth2 length_G_pos; first by lia.
  by have ->: S (S m) - m = 2 by lia.
Qed.

Lemma sigma_G_rule m k x rule : nth_error rules x = Some rule -> sigma_G m k (x + 3 + m) = G_R rule.
Proof.
  rewrite /sigma_G app_nth2 length_G_pos; first lia.
  have ->: x + 3 + m - m = 3 + x by lia.
  rewrite /=. elim: (rules) x; first by case.
  move=> ?? IH [|x] /=.
  - by move=> [->].
  - move=> /[dup] Hx /IH <-. apply: nth_indep.
    rewrite length_map. apply /nth_error_Some. by rewrite Hx.
Qed.

Lemma stlc_G_1 Gamma : stlc Gamma G_1 A.
Proof.
  by apply: stlc_pi.
Qed.

Lemma stlc_G_star Gamma : stlc Gamma G_star A_star.
Proof.
  rewrite /G_star.
  rewrite /A_star /=.
  apply: stlc_lam. apply: stlc_lam. apply: stlc_lams; first by apply: repeat_length.
  rewrite rev_repeat.
  have HSn : forall t, stlc (repeat atom n ++ arr (arr A A) A :: t :: Gamma) (var (S n)) t.
  { move=> ?. apply: stlc_var. rewrite nth_error_app2 repeat_length; first lia.
    by have ->: S n - n = 1 by lia. }
  apply: stlc_case_of; by auto 6 with stlc.
Qed.

Lemma stlc_G_0 Gamma : stlc Gamma G_0 A_0R.
Proof.
  rewrite /G_0 /A_0R /=.
  apply: stlc_lam. apply: stlc_lam. apply: stlc_lams; first by apply: repeat_length.
  have HSn : forall t, stlc (repeat atom n ++ A :: t :: Gamma) (var (S n)) t.
  { move=> ?. apply: stlc_var. rewrite nth_error_app2 repeat_length; first lia.
    by have ->: S n - n = 1 by lia. }
  rewrite rev_repeat. by apply: stlc_case_of; auto 6 with stlc.
Qed.

Lemma stlc_G_rule Gamma rule : wf_rule rule -> stlc Gamma (G_R rule) A_0R.
Proof.
  move=> [????]. rewrite /G_R /A_0R /=.
  apply: stlc_lam. apply: stlc_lam. apply: stlc_lams; first by apply: repeat_length.
  have HSn : forall t, stlc (repeat atom n ++ A :: t :: Gamma) (var (S n)) t.
  { move=> ?. apply: stlc_var. rewrite nth_error_app2 repeat_length; first lia.
    by have ->: S n - n = 1 by lia. }
  rewrite rev_repeat. apply: stlc_case_of; [by auto 6 with stlc| |by auto 6 with stlc..].
  apply: stlc_apps; first by apply: stlc_repeat_var_eq.
  apply: Forall2_repeat_r'.
  - apply /Forall_map /Forall_rev /Forall_forall.
    move=> ? /in_seq [??]. by auto with stlc.
  - by rewrite length_map length_rev length_seq.
Qed.

Lemma stlc_sigma_G m k x s : nth_error (Gamma_A m) x = Some s -> stlc [] (sigma_G m k x) s.
Proof.
  move=> Hx.
  have H'x : x < length (Gamma_A m) by (apply /nth_error_Some; rewrite Hx).
  move: (H'x)=> /Gamma_A_vals_spec []; rewrite Hx=> ? [->].
  - move: k=> [|k].
    + rewrite sigma_G_pos_0; first done.
      by apply: stlc_delta.
    + rewrite sigma_G_pos_S; first done.
      case: (Nat.eqb k x); first by apply: stlc_delta.
      case: (Nat.eqb k (S x)); by apply: stlc_delta.
  - subst x. rewrite sigma_G_star. by apply: stlc_G_star.
  - subst x. rewrite sigma_G_fin. by apply: stlc_G_1.
  - subst x. rewrite sigma_G_init. by apply: stlc_G_0.
  - rewrite length_Gamma_A in H'x.
    have ->: x = ((x - 3 - m) + 3 + m) by lia.
    case E: (nth_error rules (x - 3 - m)) => [rule|]; first last.
    { move=> /nth_error_None in E. lia. }
    move: (E) => /nth_error_In.
    move: (wf_rules) => /Forall_forall /[apply] ?.
    move: E => /sigma_G_rule ->.
    by apply: stlc_G_rule.
Qed.

Lemma stlc_subst_sigma_G m k M t : 
  stlc (Gamma_A m) M t -> stlc [] (subst (sigma_G m k) M) t.
Proof.
  move=> /stlc_subst. apply. by apply: stlc_sigma_G.
Qed.

Lemma G_0_closed : closed G_0.
Proof.
  apply: stlc_closed. by apply: stlc_G_0.
Qed.

Lemma G_star_closed : closed G_star.
Proof.
  apply: stlc_closed. by apply: stlc_G_star.
Qed.

Lemma G_R_closed rule : wf_rule rule -> closed (G_R rule).
Proof.
  move=> ?. apply: stlc_closed. by apply: stlc_G_rule.
Qed.

Lemma sigma_G_closed m k x P : x < length (Gamma_A m) -> allfv P (sigma_G m k x).
Proof.
  move=> /nth_error_Some.
  case E: (nth_error (Gamma_A m) x)=> [?|] ?; last done.
  move: E=> /(stlc_sigma_G m k x) /stlc_allfv_not_None.
  apply: allfv_impl. by case.
Qed.

Hint Resolve stlc_G_0 stlc_G_1 stlc_G_star : stlc.
Hint Resolve G_0_closed G_star_closed G_R_closed : allfv.

Lemma sigma_G_0_shift m x : x < m + 3 + length rules -> sigma_G (S m) 0 (S x) = sigma_G m 0 x.
Proof.
  rewrite /sigma_G. move=> ?.
  have [?|?] : x < m \/ x >= m by lia.
  - rewrite [LHS]app_nth1; first by rewrite length_G_pos; lia.
    rewrite [RHS]app_nth1; first by rewrite length_G_pos; lia.
    rewrite /=. apply: nth_indep.
    by rewrite repeat_length.
  - rewrite [LHS]app_nth2; first by rewrite length_G_pos; lia.
    rewrite [RHS]app_nth2; first by rewrite length_G_pos; lia.
    rewrite !length_G_pos.
    apply: nth_indep.
    rewrite /= length_map. lia.
Qed.

Lemma sigma_G_S_shift m k x : x < m + 3 + length rules -> sigma_G (S m) (S k) (S x) = sigma_G m k x.
Proof.
  have [?|?] : x < m \/ x >= m by lia.
  - move: k=> [|k] ?.
    + rewrite sigma_G_pos_0; first done.
      by rewrite sigma_G_pos_S; first lia.
    + by rewrite !sigma_G_pos_S; [lia..|].
  - rewrite /sigma_G. move=> ?.
    rewrite [LHS]app_nth2 length_G_pos; first by lia.
    rewrite [RHS]app_nth2 length_G_pos; first by lia.
    apply: nth_indep. rewrite /= length_map. lia.
Qed.

Lemma steps_G_star M1 M2 :
  steps (apps G_star [M1; M2])
    (lams n
      (case_of (app (ren (Nat.add n) M1) (pi top))
          (apps (app (ren (Nat.add n) M2) (delta bullet))
            (single zero (var zero)
                (apps (app (ren (Nat.add n) M2) (delta bullet))
                  (single dollar (apps (app (ren (Nat.add n) M2) (delta zero)) (single one (var dollar) (var bot))) (var bot)))))
          (apps (app (ren (Nat.add n) M2) (delta one)) (single zero (var one) (var bot)))
          (apps (app (ren (Nat.add n) M2) (delta bullet)) (single zero (var zero) (var bot)))
          (var bot))).
Proof.
  rewrite /G_star /=.
  apply: rt_trans.
  { apply: stepsAppL. by apply: stepsRed. }
  rewrite subst_lam. apply: rt_trans; first by apply: stepsRed.
  apply: steps_refl.
  rewrite subst_subst_term subst_lams subst_case_of /=.
  do ? rewrite subst_apps map_single.
  rewrite /= !iter_up_eq !subst_delta; [done..|].
  rewrite (iter_up_ge n (S n)); first by lia.
  have ->: S n - n = 1 by lia.
  rewrite !iter_up_lt /=; [done..|].
  by rewrite subst_ren_term subst_var_term subst_pi.
Qed.

Lemma steps_G_star_delta M1 M2 i : i < n ->
  steps M1 (delta i) ->
  steps (apps G_star [M1; lam M2])
  (lams n
    (case_of (pi i)
      (apps (ren (Nat.add n) (subst (scons (delta bullet) var) M2))
          (single zero (var zero)
            (apps (ren (Nat.add n) (subst (scons (delta bullet) var) M2))
              (single dollar (apps (ren (Nat.add n) (subst (scons (delta zero) var) M2)) (single one (var dollar) (var bot))) (var bot)))))
      (apps (ren (Nat.add n) (subst (scons (delta one) var) M2)) (single zero (var one) (var bot))) 
      (apps (ren (Nat.add n) (subst (scons (delta bullet) var) M2)) (single zero (var zero) (var bot)))
      (var bot))).
Proof.
  move=> ? HM1. apply: rt_trans; first by apply: steps_G_star.
  apply: stepsLams. apply: rt_trans.
  { apply: steps_case_of_head. apply: rt_trans.
    - apply: stepsAppL. apply: steps_ren. by eassumption.
    - rewrite ren_delta; first done. by apply: steps_delta_pi_top. }
  rewrite /=. apply: rt_trans.
  { apply: steps_case_of_fst. apply: rt_trans.
    { apply: stepsAppsL. by apply: stepsRed. }
    apply: rt_trans.
    { apply: stepsAppsR. apply: Forall2_single; first by apply: rt_refl.
      apply: stepsAppsL. by apply: stepsRed. }
    apply: stepsAppsR. apply: Forall2_single; first by apply: rt_refl.
    apply: stepsAppsR. apply: Forall2_single; last by apply: rt_refl.
    apply: stepsAppsL. by apply: stepsRed. }
  apply: rt_trans.
  { apply: steps_case_of_snd. apply: stepsAppsL. by apply: stepsRed. }
  apply: rt_trans.
  { apply: steps_case_of_trd. apply: stepsAppsL. by apply: stepsRed. }
  have E : forall j, j < n -> subst (scons (delta j) var) (ren (scons 0 (fun x : nat => S (n + x))) M2) =
    ren (Nat.add n) (subst (scons (delta j) var) M2).
  { move=> ??. rewrite subst_ren_term ren_subst_term /=. apply: ext_subst_term=> - [|?]; last done.
    by rewrite /= ren_delta. }
  apply: steps_refl. by rewrite !E.
Qed.

Lemma steps_G_star_dollar M1 M2 :
  steps M1 (delta bullet) ->
  steps (subst (scons (delta bullet) var) M2) (pi dollar) ->
  steps (subst (scons (delta zero) var) M2) (pi one) ->
  steps (apps G_star [M1; lam M2]) (pi dollar).
Proof.
  move=> HM1 H1M2 H2M2. apply: rt_trans.
  { move: HM1. by apply: steps_G_star_delta. }
  apply: stepsLams. apply: rt_trans; first by apply: steps_case_of_bullet.
  apply: rt_trans.
  { apply: stepsAppsL. apply: steps_ren. by eassumption. }
  rewrite ren_pi; first done.
  apply: rt_trans; first by apply: steps_pi_neq.
  apply: rt_trans.
  { apply: stepsAppsL. apply: steps_ren. by eassumption. }
  rewrite ren_pi; first done.
  apply: rt_trans; first by apply: steps_pi_eq.
  apply: rt_trans.
  { apply: stepsAppsL. apply: steps_ren. by eassumption. }
  rewrite ren_pi; first done.
  by apply: steps_pi_eq.
Qed.

Lemma steps_G_star_one M1 M2 :
  steps M1 (delta zero) ->
  steps (subst (scons (delta one) var) M2) (pi zero) ->
  steps (apps G_star [M1; lam M2]) (pi one).
Proof.
  move=> HM1 HM2. apply: rt_trans.
  { move: HM1. by apply: steps_G_star_delta. }
  apply: stepsLams. apply: rt_trans; first by apply: steps_case_of_L.
  apply: rt_trans.
  { apply: stepsAppsL. apply: steps_ren. by eassumption. }
  rewrite ren_pi; first done.
  by apply: steps_pi_eq.
Qed.

Lemma steps_G_star_R_zero M1 M2 :
  steps M1 (delta one) ->
  steps (subst (scons (delta bullet) var) M2) (pi zero) ->
  steps (apps G_star [M1; lam M2]) (pi zero).
Proof.
  move=> HM1 HM2. apply: rt_trans.
  { move: HM1. by apply: steps_G_star_delta. }
  apply: stepsLams. apply: rt_trans; first by apply: steps_case_of_R.
  apply: rt_trans.
  { apply: stepsAppsL. apply: steps_ren. by eassumption. }
  rewrite ren_pi; first done.
  by apply: steps_pi_eq.
Qed.

Lemma steps_G_star_bullet_zero M1 M2 :
  steps M1 (delta bullet) ->
  steps (subst (scons (delta bullet) var) M2) (pi zero) ->
  steps (apps G_star [M1; lam M2]) (pi zero).
Proof.
  move=> HM1 HM2. apply: rt_trans.
  { move: HM1. by apply: steps_G_star_delta. }
  apply: stepsLams. apply: rt_trans; first by apply: steps_case_of_bullet.
  apply: rt_trans.
  { apply: stepsAppsL. apply: steps_ren. by eassumption. }
  rewrite ren_pi; first done.
  by apply: steps_pi_eq.
Qed.

Lemma steps_G_star_one_elim M1 M2 :
  closed M1 ->
  stlc [] (lam M2) (arr (arr A A) A) ->
  steps (apps G_star [M1; lam M2]) (pi one) -> steps (subst (scons (delta one) var) M2) (pi zero).
Proof.
  move=> HM1 /[dup] /stlcE [] ?? [<- <-] H'M2 /stlc_closed HM2.
  apply: steps_pi_elim; first by apply: steps_G_star.
  move=> /steps_lamsE. rewrite !ren_closed; [by auto with allfv..|].
  move=> H. apply: stlc_pi_intro.
  - apply: stlc_subst; first by eassumption.
    move=> [|[|?]] /= ?; [|done..].
    move=> [<-]. by apply: stlc_delta.
  - move=> *. apply: steps_var_elim H.
    { apply: steps_case_of_snd. apply: stepsAppsL.
      apply: rt_trans; first by apply: stepsRed.
      by eassumption. }
    apply: steps_var_elim.
    { apply: steps_case_of_snd. by apply: steps_pi_neq. }
    apply: steps_var_absurd.
    have ? : bot <> one by done.
    apply: allfv_case_of; by auto 9 with allfv.
Qed.

Lemma steps_G_star_dollar_elim M1 M2 :
  closed M1 ->
  stlc [] (lam M2) (arr (arr A A) A) ->
  steps (apps G_star [M1; lam M2]) (pi dollar) ->
  steps (subst (scons (delta bullet) var) M2) (pi dollar) /\ steps (subst (scons (delta zero) var) M2) (pi one).
Proof.
  move=> HM1 /[dup] /stlcE [] ?? [<- <-] H'M2 /stlc_closed HM2.
  apply: steps_pi_elim; first by apply: steps_G_star.
  move=> /steps_lamsE. rewrite !ren_closed; [by auto with allfv..|].
  move=> H [: H']. split.
  - abstract: H'. apply: stlc_pi_intro.
    + apply: stlc_subst; first by eassumption.
      move=> [|[|?]] /= ?; [|done..].
      move=> [<-]. by apply: stlc_delta.
    + move=> *. apply: steps_var_elim H.
      { apply: steps_case_of_fst. apply: stepsAppsR.
        apply: Forall2_single; first by apply: rt_refl.
        apply: rt_trans.
        - apply: stepsAppsL. apply: rt_trans; first by apply: stepsRed.
          by eassumption.
        - by apply: steps_pi_neq. }
      apply: steps_var_absurd.
      by apply: allfv_case_of; auto 8 with allfv.
  - apply: stlc_pi_intro.
    + apply: stlc_subst; first by eassumption.
      move=> [|[|?]] /= ?; [|done..].
      move=> [<-]. by apply: stlc_delta.
    + move=> *. apply: steps_var_elim H.
      { apply: steps_case_of_fst. apply: rt_trans.
        - apply: stepsAppsL. apply: rt_trans; first by apply: stepsRed.
          by apply: H'.
        - by apply: steps_pi_neq. }
      apply: steps_var_elim.
      { apply: steps_case_of_fst. apply: rt_trans.
        - apply: stepsAppsL. apply: rt_trans; first by apply: stepsRed.
          by apply: H'.
        - by apply: steps_pi_eq. }
      apply: steps_var_elim.
      { apply: steps_case_of_fst. apply: rt_trans.
        - apply: stepsAppsL. apply: rt_trans; first by apply: stepsRed.
          by eassumption.
        - by apply: steps_pi_neq. }
      apply: steps_var_absurd.
      by apply: allfv_case_of; auto 8 with allfv.
Qed.

Lemma steps_G_star_zero_elim M1 M2 :
  closed M1 ->
  stlc [] (lam M2) (arr (arr A A) A) ->
  steps (apps G_star [M1; lam M2]) (pi zero) -> steps (subst (scons (delta bullet) var) M2) (pi zero).
Proof.
  move=> HM1 /[dup] /stlcE [] ?? [<- <-] H'M2 /stlc_closed HM2.
  apply: steps_pi_elim; first by apply: steps_G_star.
  move=> /steps_lamsE. rewrite !ren_closed; [by auto with allfv..|].
  move=> H. apply: stlc_pi_intro.
  - apply: stlc_subst; first by eassumption.
    move=> [|[|?]] /= ?; [|done..].
    move=> [<-]. by apply: stlc_delta.
  - move=> *. apply: steps_var_elim H.
    { apply: steps_case_of_fst. apply: rt_trans.
      - apply: stepsAppsL. apply: rt_trans; last by eassumption.
        by apply: stepsRed.
      - by apply: steps_pi_neq. }
    apply: steps_var_elim.
    { apply: steps_case_of_trd. apply: rt_trans.
      - apply: stepsAppsL. apply: rt_trans; last by eassumption.
        by apply: stepsRed.
      - by apply: steps_pi_neq. }
    apply: steps_var_absurd.
    have ? : dollar <> zero by done.
    have ? : bot <> zero by done.
    by apply: allfv_case_of; auto 10 with allfv.
Qed.

Lemma steps_G_0 {M N M'} :
  steps M M' ->
  steps (app (app G_0 N) M)
    (lams n (case_of (app (ren (Nat.add n) (subst (scons M var) (ren S N))) (pi top))
      (apps (ren (Nat.add n) M') (single zero (var zero) (apps (ren (Nat.add n) M') (single one (var dollar) (var bot)))))
      (apps (ren (Nat.add n) M') (single zero (var one) (var bot)))
      (apps (ren (Nat.add n) M') (single zero (var zero) (var bot)))
      (var bot))).
Proof.
  move=> HM. apply: rt_trans.
  { rewrite /G_0 /=. apply: stepsAppL. by apply: stepsRed. }
  apply: rt_trans.
  { rewrite /=. by apply: stepsRed. }
  rewrite subst_subst_term subst_lams subst_case_of.
  do 2 rewrite !subst_apps !map_single /=.
  rewrite (iter_up_ge _ (S n)); first by lia.
  have ->: S n - n = 1 by lia.
  rewrite iter_up_eq /(up _ 0) /(up _ 1) /= subst_pi; first done.
  rewrite !iter_up_lt; [done..|].
  apply: stepsLams. apply: rt_trans.
  { apply: steps_case_of_fst. apply: rt_trans.
    - apply: stepsAppsL. apply: steps_ren. by eassumption.
    - apply: stepsAppsR. apply: Forall2_single; first by apply: rt_refl.
      apply: stepsAppsL. apply: steps_ren. by eassumption. }
  apply: rt_trans.
  { apply: steps_case_of_snd. apply: stepsAppsL. apply: steps_ren. by eassumption. }
  apply: rt_trans.
  { apply: steps_case_of_trd. apply: stepsAppsL. apply: steps_ren. by eassumption. }
  by apply: rt_refl.
Qed.

Lemma steps_G_0_bullet M : steps (app (app G_0 (delta bullet)) M)
  (lams n (apps (ren (Nat.add n) M) (single zero (var zero) (apps (ren (Nat.add n) M) (single one (var dollar) (var 0)))))).
Proof.
  apply: rt_trans.
  { apply: steps_G_0. by apply: rt_refl. }
  rewrite ren_subst_term subst_ren_term subst_delta; first done.
  apply: stepsLams. apply: rt_trans.
  { apply: steps_case_of_head. by apply: steps_delta_pi_top. }
  by apply: steps_case_of_bullet.
Qed.

Lemma steps_G_0_L M : steps (app (app G_0 (delta zero)) M)
  (lams n (apps (ren (Nat.add n) M) (single zero (var one) (var bot)))).
Proof.
  apply: rt_trans.
  { apply: steps_G_0. by apply: rt_refl. }
  rewrite ren_subst_term subst_ren_term subst_delta; first done.
  apply: stepsLams. apply: rt_trans.
  { apply: steps_case_of_head. by apply: steps_delta_pi_top. }
  by apply: steps_case_of_L.
Qed.

Lemma steps_G_0_R M : steps (app (app G_0 (delta one)) M)
  (lams n (apps (ren (Nat.add n) M) (single zero (var zero) (var bot)))).
Proof.
  apply: rt_trans.
  { apply: steps_G_0. by apply: rt_refl. }
  rewrite ren_subst_term subst_ren_term subst_delta; first done.
  apply: stepsLams. apply: rt_trans.
  { apply: steps_case_of_head. by apply: steps_delta_pi_top. }
  by apply: steps_case_of_R.
Qed.

Lemma steps_G_0_dollar_elim M N :
  stlc [] M A ->
  steps (app (app G_0 N) M) (pi dollar) ->
  steps M (pi one).
Proof.
  move=> /stlc_pi_intro + H. apply=> *.
  apply: steps_pi_elim H.
  { apply: steps_G_0. by eassumption. }
  move=> /steps_lamsE. rewrite ren_pi; first done.
  apply: steps_var_elim.
  { apply: steps_case_of_fst. apply: stepsAppsR. apply: Forall2_single; first by apply: rt_refl.
    by apply: steps_pi_neq. }
  apply: steps_var_absurd.
  apply: allfv_case_of; by auto with allfv.
Qed.

Lemma steps_G_0_one_elim M N :
  stlc [] M A ->
  steps (app (app G_0 N) M) (pi one) ->
  steps M (pi zero).
Proof.
  move=> /stlc_pi_intro + H. apply=> *.
  apply: steps_pi_elim H.
  { apply: steps_G_0. by eassumption. }
  move=> /steps_lamsE. rewrite ren_pi; first done.
  apply: steps_var_elim.
  { apply: steps_case_of_fst. by apply: steps_pi_neq. }
  apply: steps_var_elim.
  { apply: steps_case_of_snd. by apply: steps_pi_neq. }
  apply: steps_var_elim.
  { apply: steps_case_of_trd. by apply: steps_pi_neq. }
  apply: steps_var_absurd.
  have ? : bot <> one by done.
  by apply: allfv_case_of; auto with allfv.
Qed.

Lemma steps_G_0_zero_elim M N :
  stlc [] M A ->
  steps (app (app G_0 N) M) (pi zero) ->
  steps M (pi zero).
Proof.
  move=> /stlc_pi_intro + H. apply=> *.
  apply: steps_pi_elim H.
  { apply: steps_G_0. by eassumption. }
  move=> /steps_lamsE. rewrite ren_pi; first done.
  apply: steps_var_elim.
  { apply: steps_case_of_fst. by apply: steps_pi_neq. }
  apply: steps_var_elim.
  { apply: steps_case_of_snd. by apply: steps_pi_neq. }
  apply: steps_var_elim.
  { apply: steps_case_of_trd. by apply: steps_pi_neq. }
  apply: steps_var_absurd.
  have ? : dollar <> zero by done.
  have ? : bot <> zero by done.
  apply: allfv_case_of; auto with allfv.
Qed.

Lemma steps_G_R_bullet' rule M N :
  (forall sigma N', steps (app (subst sigma N) N') (app (delta bullet) N')) ->
  steps (app (app (G_R rule) N) M) (lams n (apps (ren (Nat.add n) M) (map var (rev (seq 0 n))))).
Proof.
  move=> HN.
  apply: rt_trans.
  { rewrite /G_R /=. apply: stepsAppL. by apply: stepsRed. }
  apply: rt_trans.
  { rewrite /=. by apply: stepsRed. }
  rewrite !subst_lams. apply: stepsLams.
  apply: rt_trans.
  { rewrite !subst_case_of /= !subst_pi; [done..|].
    rewrite -Nat.iter_succ_r iter_up_eq.
    apply: steps_case_of_head. rewrite subst_ren_term. by apply: HN. }
  apply: rt_trans.
  { apply: steps_case_of_head. by apply: steps_delta_pi_top. }
  apply: rt_trans.
  { by apply: steps_pi_eq. }
  apply: steps_refl.
  rewrite !subst_apps /=.
  rewrite -Nat.iter_succ iter_up_lt; first lia.
  rewrite /= iter_up_eq /= !map_map.
  congr (apps _ _). apply /map_ext_in_iff.
  move=> x /(iffRL (in_rev _ _)) /in_seq ?.
  rewrite subst_subst_term/=.
  rewrite -Nat.iter_succ iter_up_lt; first lia.
  rewrite /= iter_up_lt; by [|lia].
Qed.

Lemma steps_G_R_bullet rule M : steps (app (app (G_R rule) (delta bullet)) M) (lams n (apps (ren (Nat.add n) M) (map var (rev (seq 0 n))))).
Proof.
  apply: steps_G_R_bullet'=> *. apply: steps_refl. by rewrite subst_delta.
Qed.

Lemma steps_G_R_L' rule M N :
  (forall sigma N', steps (app (subst sigma N) N') (app (delta zero) N')) ->
  wf_rule rule ->
  steps (app (app (G_R rule) N) M) (lams n (apps (ren (Nat.add n) M) ((single (sym (fst (snd rule))) (var (sym (fst (fst rule)))) (var bot))))).
Proof.
  move=> HN [????]. apply: rt_trans.
  { rewrite /G_R /=. apply: stepsAppL. by apply: stepsRed. }
  apply: rt_trans.
  { rewrite /=. by apply: stepsRed. }
  rewrite !subst_lams. apply: stepsLams.
  apply: rt_trans.
  { rewrite !subst_case_of /=.
    rewrite !subst_pi; [done..|].
    rewrite -/(up _) -Nat.iter_succ_r iter_up_eq /=.
    apply: steps_case_of_head. apply: rt_trans.
    - rewrite subst_ren_term. by apply: HN.
    - by apply: steps_delta_pi_top. }
  apply: rt_trans.
  { by apply: steps_case_of_L. }
  apply: steps_refl.
  rewrite !subst_apps /=.
  rewrite -Nat.iter_succ iter_up_lt; first lia.
  rewrite /= iter_up_eq /= !map_map map_single.
  congr (apps _ _). congr single.
  rewrite /= -Nat.iter_succ iter_up_lt; first lia.
  by rewrite /= iter_up_lt.
Qed.

Lemma steps_G_R_L rule M : wf_rule rule -> steps (app (app (G_R rule) (delta zero)) M) (lams n (apps (ren (Nat.add n) M) ((single (sym (fst (snd rule))) (var (sym (fst (fst rule)))) (var bot))))).
Proof.
  apply: steps_G_R_L'=> *. apply: steps_refl. by rewrite subst_delta.
Qed.

Lemma steps_G_R_R' rule M N :
  (forall sigma N', steps (app (subst sigma N) N') (app (delta one) N')) ->
  wf_rule rule ->
  steps (app (app (G_R rule) N) M) (lams n (apps (ren (Nat.add n) M) ((single (sym (snd (snd rule))) (var (sym (snd (fst rule)))) (var bot))))).
Proof.
  move=> HN [????]. apply: rt_trans.
  { rewrite /G_R /=. apply: stepsAppL. by apply: stepsRed. }
  apply: rt_trans.
  { rewrite /=. by apply: stepsRed. }
  rewrite !subst_lams. apply: stepsLams.
  apply: rt_trans.
  { rewrite !subst_case_of /=.
    rewrite !subst_pi; [done..|].
    rewrite -Nat.iter_succ_r iter_up_eq /=.
    apply: steps_case_of_head. apply: rt_trans.
    - rewrite subst_ren_term. by apply: HN.
    - by apply: steps_delta_pi_top. }
  apply: rt_trans.
  { by apply: steps_case_of_R. }
  apply: steps_refl.
  rewrite !subst_apps /=.
  rewrite -Nat.iter_succ iter_up_lt; first lia.
  rewrite /= iter_up_eq /= !map_map map_single.
  congr (apps _ _). congr single.
  rewrite /= -Nat.iter_succ iter_up_lt; first lia.
  by rewrite /= iter_up_lt.
Qed.

Lemma steps_G_R_R rule M : wf_rule rule -> steps (app (app (G_R rule) (delta one)) M) (lams n (apps (ren (Nat.add n) M) ((single (sym (snd (snd rule))) (var (sym (snd (fst rule)))) (var bot))))).
Proof.
  apply: steps_G_R_R'=> *. apply: steps_refl. by rewrite subst_delta.
Qed.

Lemma steps_G_R_bullet_elim' M N i rule :
  (forall sigma N', steps (app (subst sigma N) N') (app (delta bullet) N')) ->
  i < n ->
  stlc [] M A ->
  steps (app (app (G_R rule) N) M) (pi i) ->
  steps M (pi i).
Proof.
  move=> HN ? /stlc_pi_intro + H. apply=> *.
  apply: steps_pi_elim H; first by apply: steps_G_R_bullet'.
  move=> /steps_lamsE. apply: steps_var_elim.
  { apply: rt_trans.
    - apply: stepsAppsL. apply: steps_ren. by eassumption.
    - rewrite ren_pi; first done. by apply: steps_pi_full. }
  by apply: steps_var_absurd.
Qed.

Lemma steps_G_R_bullet_elim M i rule :
  i < n ->
  stlc [] M A ->
  steps (app (app (G_R rule) (delta bullet)) M) (pi i) ->
  steps M (pi i).
Proof.
  apply: steps_G_R_bullet_elim'=> ??. apply: steps_refl. by rewrite subst_delta.
Qed.

Lemma steps_G_R_L_elim' M N rule a :
  (forall sigma N', steps (app (subst sigma N) N') (app (delta zero) N')) ->
  wf_rule rule ->
  stlc [] M A ->
  steps (app (app (G_R rule) N) M) (pi (sym a)) ->
  fst (fst rule) = a /\ steps M (pi (sym (fst (snd rule)))).
Proof.
  move=> HN /[dup] - [????] ? /stlc_pi_intro HM +.
  apply: steps_pi_elim; first by apply: steps_G_R_L'.
  move=> /steps_lamsE H'M [: H'].
  split; first last.
  - abstract: H'. apply: HM=> *.
    apply: steps_var_elim H'M.
    { apply: rt_trans.
      - apply: stepsAppsL. apply: steps_ren. by eassumption.
      - rewrite ren_pi; first done. by apply: steps_pi_neq. }
    by apply: steps_var_absurd.
  - apply: steps_var_elim H'M.
    { apply: rt_trans.
      - apply: stepsAppsL. apply: steps_ren. by apply: H'.
      - rewrite ren_pi; first done. by apply: steps_pi_eq. }
    move=> /normal_form_steps. apply: unnest; first by do 2 constructor.
    by case.
Qed.

Lemma steps_G_R_L_elim M rule a :
  wf_rule rule ->
  stlc [] M A ->
  steps (app (app (G_R rule) (delta zero)) M) (pi (sym a)) ->
  fst (fst rule) = a /\ steps M (pi (sym (fst (snd rule)))).
Proof.
  apply: steps_G_R_L_elim'=> ??. apply: steps_refl. by rewrite subst_delta.
Qed.

Lemma steps_G_R_R_elim' M N rule b :
  (forall sigma N', steps (app (subst sigma N) N') (app (delta one) N')) ->
  wf_rule rule ->
  stlc [] M A ->
  steps (app (app (G_R rule) N) M) (pi (sym b)) ->
  snd (fst rule) = b /\ steps M (pi (sym (snd (snd rule)))).
Proof.
  move=> HN /[dup] - [????] ? /stlc_pi_intro HM +.
  apply: steps_pi_elim; first by apply: steps_G_R_R'.
  move=> /steps_lamsE H'M [: H'].
  split; first last.
  - abstract: H'. apply: HM=> *.
    apply: steps_var_elim H'M.
    { apply: rt_trans.
      - apply: stepsAppsL. apply: steps_ren. by eassumption.
      - rewrite ren_pi; first done. by apply: steps_pi_neq. }
    by apply: steps_var_absurd.
  - apply: steps_var_elim H'M.
    { apply: rt_trans.
      - apply: stepsAppsL. apply: steps_ren. by apply: H'.
      - rewrite ren_pi; first done. by apply: steps_pi_eq. }
    move=> /normal_form_steps. apply: unnest; first by do 2 constructor.
    by case.
Qed.

Lemma steps_G_R_R_elim M rule b :
  wf_rule rule ->
  stlc [] M A ->
  steps (app (app (G_R rule) (delta one)) M) (pi (sym b)) ->
  snd (fst rule) = b /\ steps M (pi (sym (snd (snd rule)))).
Proof.
  apply: steps_G_R_R_elim'=> ??. apply: steps_refl. by rewrite subst_delta.
Qed.

Opaque G_R G_1 G_0 G_pos G_star.

(* Soundness :
   given a simple semi-Thue system,
   if the constructed higher-order matching instance is solvable,
   then 0..0 rewrites to 1..1 *)

(* x_R x_p M or x_R (\w.x_p w) M *)
(* rule application term or concluding term *)
Inductive ring2 (l : nat) : term -> Prop :=
  | ring2_intro x y M : ring2 l M -> x < length rules -> y < l -> ring2 l (app (app (var (x + 3 + l)) (var y)) M)
  | ring2_intro_eta x y M : ring2 l M -> x < length rules -> y < l -> ring2 l (app (app (var (x + 3 + l)) (lam (app (var (S y)) (var 0)))) M)
  | ring2_fin : ring2 l (var (S l)).

(* x_star N (\x_p.M) *)
(* word expansion term or init rule application term *)
Inductive ring1 (l : nat) : term -> Prop :=
  | ring1_intro M N : ring1 (S l) M -> ring1 l (apps (var l) [N; lam M])
  | ring1_init M N : ring2 l M -> ring1 l (apps (var (2 + l)) [N; M]).

Lemma well_typed_neutral_shape m x Ms ss i :
  nth_error (Gamma_A m) x = Some (arrs ss A) ->
  length Ms = length ss ->
  S i < n ->
  steps (apps (sigma_H m x) Ms) (pi (S i)) ->
    if Nat.eqb (S i) bullet then x < m else
    if Nat.eqb (S i) dollar then x = m \/ x = S (S m) else
    if Nat.eqb (S i) one then x = S m \/ x > S (S m) else
    False.
Proof.
  move=> H''x.
  have Hx : x < length (Gamma_A m).
  { apply /nth_error_Some. by rewrite H''x. }
  move: (Hx) (H''x) => /Gamma_A_vals_spec [] H'x -> [].
  - rewrite sigma_H_pos; first done.
    move=> /(arrs_inj [_]) ?. subst ss.
    move: Ms=> [|M [|??]] ??; [done| |done].
    have [-> /=|?] : S i = bullet \/ S i <> bullet by lia.
    * done.
    * apply: steps_pi_elim; first by apply: step_delta.
      move=> /steps_lamsE. apply: steps_var_absurd.
      apply: allfv_apps; last by auto with allfv.
      apply: allfv_ren. apply: allfv_trivial=> /=. lia.
  - subst x. rewrite sigma_H_space.
    move=> /(arrs_inj [_; _]) ?. subst ss.
    move: Ms=> [|M1 [|M2 [|??]]] ??; [done|done| |done].
    have [-> /=|?] : (S i) = dollar \/ dollar <> (S i) by lia.
    * by lia.
    * apply: steps_pi_elim; first by apply: steps_H_star.
      move=> /steps_lamsE. apply: steps_var_absurd.
      apply: allfv_apps; last by auto with allfv.
      apply: allfv_ren. apply: allfv_trivial=> /=. lia.
  - subst x. rewrite sigma_H_fin.
    move=> /(arrs_inj []) ?. subst ss.
    move: Ms=> [|??] ??; [|done].
    have [-> /=|?] : (S i) = one \/ one <> (S i) by lia.
    * by lia.
    * move=> /steps_lamsE. by apply: steps_var_absurd.
  - subst x. rewrite sigma_H_init.
    move=> /arrs_inj ?. subst ss.
    move: Ms=> [|M1 [|M2 [|??]]] ??; [done|done| |done].
    have [-> /=|?] : (S i) = dollar \/ dollar <> (S i) by lia.
    + by lia.
    + apply: steps_pi_elim; first by apply: steps_H_0.
      move=> /steps_lamsE. apply: steps_var_absurd.
      apply: allfv_apps; last by auto with allfv.
      apply: allfv_ren. apply: allfv_trivial=> /=. lia.
  - rewrite sigma_H_rule; [done..|].
    move=> /arrs_inj ?. subst ss.
    move: Ms=> [|M1 [|M2 [|??]]] ??; [done|done| |done].
    have [-> /=|?] : (S i) = one \/ one <> (S i) by lia.
    + by lia.
    + apply: steps_pi_elim; first by apply: steps_H_R.
      move=> /steps_lamsE. apply: steps_var_absurd.
      apply: allfv_apps.
      * apply: allfv_ren. apply: allfv_trivial=> /=. lia.
      * constructor; first by auto with allfv.
        apply: Forall_single; last done.
        apply: allfv_apps; last by auto with allfv.
        apply: allfv_ren. apply: allfv_trivial=> /=. lia.
Qed.

Lemma well_typed_neutral_shape' m x Ms ss N1 N2 i j :
  nth_error (Gamma_A m) x = Some (arrs ss A) ->
  length Ms = length ss ->
  stlc [] (apps (sigma_H m x) Ms) A ->
  allfv (fun y => y <> j) N2 ->
  S i < n ->
  steps (apps (apps (sigma_H m x) Ms) (single (S i) N1 N2)) (var j) ->
    if Nat.eqb (S i) bullet then x < m else
    if Nat.eqb (S i) dollar then x = m \/ x = S (S m) else
    if Nat.eqb (S i) one then x = S m \/ x > S (S m) else
    False.
Proof.
  move=> /well_typed_neutral_shape /[apply] H /stlc_pi_intro Hx HN2 /[dup] ? /H {}H H'x.
  apply: H. apply: Hx=> *.
  apply: steps_var_elim H'x.
  { apply: rt_trans.
    - apply: stepsAppsL. by eassumption.
    - by apply: steps_pi_neq. }
  by apply: steps_var_absurd.
Qed.

Lemma construct_ring2 M m :
  normal_form M ->
  stlc (Gamma_A m) M A ->
  steps (subst (sigma_F m) M) (var m) ->
  steps (subst (sigma_H m) M) (pi one) ->
  ring2 m M.
Proof.
  elim /(Nat.measure_induction _ term_size): M => M IH HM H'M.
  case /normal_form_nf: HM H'M IH; first by move=> ???? /steps_lamE.
  move=> {}M=> /neutralE' [x] [Ms] [->] HMs /stlc_appsE [ss] [H'Ms] /stlcE.
  move=> /[dup] /nth_error_Some' ? Hx IH Hm.
  rewrite !subst_apps /=.
  move: (Hx)=> /well_typed_neutral_shape + /[dup] => /[apply].
  apply: unnest. { move: H'Ms => /Forall2_length. by rewrite length_map. }
  apply: unnest; first done.
  case.
  - (* x_fin *)
    move=> ?. subst x.
    move: (Hx). rewrite Gamma_A_fin=> - [/(arrs_inj [])] ?. subst ss.
    move: Ms H'Ms Hm IH {HMs}=> [|??] /Forall2_length; [|done].
    move=> *. by constructor.
  - (* x_rule _ _ *)
    move=> ?. have ? : x > S m by lia.
    have ? : x < m + 3 + length rules by (by rewrite -length_Gamma_A).
    move: Hx. rewrite Gamma_A_rule; [done..|].
    move=> - [/arrs_inj] ?. subst ss.
    move: Ms H'Ms HMs Hm IH => [|N1 [|N2 [|??]]] /[dup] /Forall2_length; [done|done| |done].
    move=> _ /Forall2_cons_iff [H'N1] /Forall2_cons_iff [H'N2] _.
    move=> /Forall_cons_iff [HN1] /Forall_cons_iff [HN2] _.
    rewrite !subst_apps /= sigma_F_rule; [done..|].
    apply: steps_var_elim; first by apply: steps_F_R.
    move=> Hm IH. rewrite sigma_H_rule; [done..|].
    apply: steps_pi_elim; first by apply: steps_H_R.
    rewrite !ren_closed; [apply: allfv_closed; apply: subst_sigma_H_closed; eassumption..|].
    case /normal_form_nf: HN1 H'N1 Hm IH.
    + (* x_rule (lam _) _ *)
      move=> {}N1 HN1 /stlcE [] ?? [<- <-] H'N1 /=.
      apply: steps_var_elim; first by apply: stepsRed.
      case /normal_form_nf: HN1 H'N1; first by move=> ??? /steps_lamE.
      move=> {}N1 /neutralE' [y] [Ms] [->] HMs /stlc_appsE [ss] [H'Ms] /stlcE.
      move: y=> [|y].
      * (* x_rule (lam (var 0)) _ - semantic contradiction *)
        move=> /= [] /(arrs_inj []) ?. subst ss.
        move: Ms H'Ms {HMs}=> [|??] /Forall2_length; [|done].
        move=> _ /= Hm _ /steps_lamsE.
        apply: steps_var_elim; first by apply /stepsAppsL /stepsRed.
        apply: steps_var_elim; first by apply /steps_pi_neq.
        by apply: steps_var_absurd.
      * move=> /= Hy Hm IH /steps_lamsE.
        apply: steps_var_elim; first by apply /stepsAppsL /stepsRed.
        have ? : y < length (Gamma_A m) by (apply /nth_error_Some; rewrite Hy).
        rewrite subst_subst_term subst_apps /= subst_ren_term.
        rewrite (subst_closed _ (sigma_H m y)); first by auto with allfv.
        move=> /[dup]. move: (Hy)=> /well_typed_neutral_shape' /[apply].
        apply: unnest. { move: H'Ms => /Forall2_length. by rewrite length_map. }
        apply: unnest.
        { apply: stlc_apps.
          - apply: stlc_sigma_H. by eassumption.
          - apply /Forall2_map_l. apply: Forall2_impl H'Ms.
            move=> ?? /stlc_subst. apply=> - [|z] /=.
            + move=> ? [<-]. by apply: stlc_pi.
            + move=> ? /[dup] ? /nth_error_Some' Hz. rewrite subst_ren_term subst_closed.
              * by auto with allfv.
              * by apply: stlc_sigma_H. }
        apply: unnest; first done.
        apply: unnest; first done.
        move=> ?. move: Hy. rewrite Gamma_A_pos; first done.
        move=> [] /(arrs_inj [_]) ?. subst ss.
        move: Ms H'Ms HMs Hm IH=> [|{}N1 [|??]] /[dup] /Forall2_length; [done| |done].
        move=> _ /Forall2_cons_iff [H'N1] _ /Forall_cons_iff [HN1] _.
        rewrite !subst_apps subst_ren_term sigma_F_pos /=; first done.
        apply: steps_var_elim; first by apply: stepsRed.
        case /normal_form_nf: HN1 H'N1; first by move=> ??? /steps_lamE.
        move=> {}N1 /neutralE' [z] [Ms] [->] HMs /stlc_appsE [ss] [H'Ms] /stlcE.
        move: z=> [|z].
        { (* ring2 intro eta *)
          move=> /= [] /(arrs_inj []) ?. subst ss.
          move: Ms H'Ms {HMs}=> [|??] /Forall2_length; last done.
          move=> _ /= Hm IH H_lift. 
          have ->: x = (x - 3 - m) + 3 + m by lia.
          constructor; [|lia..].
          apply: IH; [lia|done..|].
          move: H_lift. rewrite sigma_H_pos; first done.
          apply: steps_var_elim; first by apply: steps_delta_eq.
          apply: steps_var_elim; first by apply: steps_pi_eq.
          by apply: steps_subst_sigma_H_pi_intro. }
        move=> /= Hz Hm _. rewrite sigma_H_pos; first done.
        apply: steps_var_elim; first by apply: steps_delta_eq.
        rewrite subst_apps /=.
        have ? : z < length (Gamma_A m) by (apply /nth_error_Some; rewrite Hz).
        rewrite subst_ren_term (subst_closed _ (sigma_H m z)); first by auto with allfv.
        move=> /[dup]. move: (Hz)=> /well_typed_neutral_shape' /[apply].
        apply: unnest. { move: H'Ms=> /Forall2_length. by rewrite length_map. }
        apply: unnest.
        { apply: stlc_apps.
        - apply: stlc_sigma_H. by eassumption.
        - apply /Forall2_map_l. apply: Forall2_impl H'Ms.
          move=> ?? /stlc_subst. apply=> - [|z'] /=.
          + move=> ? [<-]. by apply: stlc_pi.
          + move=> ? /[dup] ? /nth_error_Some' Hz'. rewrite subst_ren_term subst_closed.
            * by auto with allfv.
            * by apply: stlc_sigma_H. }
        apply: unnest; first done.
        by apply: unnest; first done.
    + move=> {}N1 /neutralE' [y] [Ms] [->] _ /stlc_appsE [ss] [H'Ms] /stlcE Hy Hm IH.
      rewrite subst_apps /= (apps_apps _ [_]) apps_apps app_assoc -apps_apps.
      move=> /[dup]. move: (Hy). rewrite (arrs_arrs _ [_]).
      move=> + /steps_lamsE.
      have ? : y < length (Gamma_A m) by (apply /nth_error_Some; rewrite Hy).
      move=> /well_typed_neutral_shape' /[apply].
      apply: unnest. { rewrite !length_app !length_map. by move: H'Ms => /Forall2_length ->. }
      apply: unnest.
      { apply: stlc_apps.
      - apply: stlc_sigma_H.
        move: Hy. change (arrs ss (arr A A)) with (arrs ss (arrs [A] A)).
        rewrite arrs_arrs. by apply.
      - apply: Forall2_app.
        + apply /Forall2_map_l. apply: Forall2_impl H'Ms.
          move=> ?? /stlc_subst. apply=> *.
          by apply: stlc_sigma_H.
        + by constructor; [apply: stlc_pi|]. }
      apply: unnest; first done.
      apply: unnest; first done.
      move=> ?. move: Hy. rewrite Gamma_A_pos; first done.
      move=> [] /(arrs_inj []) ?. subst ss.
      move: Ms H'Ms Hm IH=> [|??] /Forall2_length; last done.
      move=> _ /=. rewrite sigma_F_pos; first done.
      apply: steps_var_elim; first by apply: stepsRed.
      move=> /= Hm IH H_lift.
      have ->: x = (x - 3 - m) + 3 + m by lia.
      constructor; [|lia..].
      apply: IH; [lia|done..|].
      move: H_lift=> /steps_lamsE. rewrite sigma_H_pos; first done.
      apply: steps_var_elim; first by apply: steps_delta_eq.
      apply: steps_var_elim; first by apply: steps_pi_eq.
      by apply: steps_subst_sigma_H_pi_intro.
Qed.

Lemma construct_ring1 M m :
  normal_form M ->
  stlc (Gamma_A m) M A ->
  steps (subst (sigma_F m) M) (var m) ->
  steps (subst (sigma_H m) M) (pi dollar)  ->
  ring1 m M.
Proof.
  elim /(Nat.measure_induction _ term_size): M m => M IH m HM H'M.
  case /normal_form_nf: HM H'M IH; first by move=> ???? /steps_lamE.
  move=> {}M HM H'M IH.
  move: HM H'M IH=> /neutralE' [x] [Ms] [->] HMs /stlc_appsE [ss] [H'Ms] /stlcE Hx IH Hm.
  rewrite !subst_apps /= => /[dup].
  move: (Hx)=> /well_typed_neutral_shape /[apply].
  apply: unnest. { rewrite length_map. by apply: Forall2_length H'Ms. }
  apply: unnest; first done.
  case=> ?; subst x.
  - (* x_space _ *)
    move: Hx. rewrite Gamma_A_space=> - [/(arrs_inj [_; _])] ?. subst ss.
    move: Ms H'Ms HMs Hm IH (H'Ms)=> [|? [|{}M [|??]]] /Forall2_length; [done|done| |done].
    move=> _ /Forall_cons_iff [_] /Forall_cons_iff [HM] _.
    rewrite /= sigma_F_space sigma_H_space.
    apply: steps_var_elim; first by apply: steps_F_star.
    case /normal_form_nf: HM.
    + (* x_space (lam _) *)
      move=> {}M HM /=.
      apply: steps_var_elim; first by apply: stepsRed.
      case /normal_form_nf: HM; first by move=> ?? /steps_lamE.
      (* x_space (lam (apps y _)) *)
      move=> {}M HM. rewrite subst_subst_term /= => Hm IH.
      move=> /Forall2_cons_iff [_] /Forall2_cons_iff [] /stlcE [] ?? [] <- <- H'M _ H_lift.
      constructor. apply: IH.
      * by lia.
      * by apply: neutral_normal_form.
      * done.
      * move: Hm => /(steps_ren S). congr steps.
        rewrite ren_subst_term.
        apply: ext_stlc_subst_term H'M=> - [|y] /=; first done.
        move=> /nth_error_Some ?. rewrite subst_ren_term /= subst_var_term.
        by apply: ren_S_sigma_F.
      * move: H_lift. apply: steps_pi_elim.
        { apply: rt_trans.
          - by apply: steps_H_star.
          - move=> /=. apply: stepsLams. apply: stepsAppsL. by apply: stepsRed. }
        move=> /steps_lamsE.
        replace (subst (scons (delta bullet) var) _) with (subst (sigma_H (S m)) M); first last.
        { rewrite subst_ren_term subst_subst_term.
          apply: ext_stlc_subst_term H'M=> - [|x] /=; first done.
          move=> /nth_error_Some ?.
          rewrite subst_ren_term subst_closed; first by auto with allfv.
          rewrite -ren_S_sigma_H; first done.
          by rewrite ren_closed; auto with allfv. }
        by apply: steps_subst_sigma_H_pi_intro.
    + (* x_space (apps (var y) _) - typing error / semantic error *)
      move=> {}M /neutralE' [y] [Ms] [->] _ _ _.
      move=> /Forall2_cons_iff [_] /Forall2_cons_iff [] /stlc_appsE [ss] [H'Ms] /stlcE Hy.
      have : y < length (Gamma_A m) by apply /nth_error_Some; rewrite Hy.
      rewrite (arrs_arrs _ [_]) in Hy.
      move=> /Gamma_A_vals_spec [] ?; rewrite Hy.
      * move=> [] /(arrs_inj _ [_]). by move: (ss) => [|? [|??]].
      * move=> [] /arrs_inj. by move: (ss) => [|?[|?[|??]]].
      * move=> [] /= /(f_equal ty_size). rewrite ty_size_arrs map_app list_sum_app /=. lia.
      * move=> [] /arrs_inj. by move: (ss) => [|?[|?[|??]]].
      * move=> [] /arrs_inj. by move: (ss) => [|?[|?[|??]]].
  - (* x_0 _ _ *)
    move: Hx. rewrite Gamma_A_init.
    move=> [/arrs_inj] ?. subst ss.
    move: Ms H'Ms HMs Hm {IH} (H'Ms)=> [|M1 [|M2 [|??]]] /Forall2_length; [done|done| |done].
    move=> _ /Forall_cons_iff [HM1] /Forall_cons_iff [HM2] _.
    rewrite !subst_apps /= sigma_H_init sigma_F_init.
    apply: steps_var_elim; first by apply: steps_F_0.
    move=> ? /Forall2_cons_iff [H'M1] /Forall2_cons_iff [H'M2] _ H.
    constructor. apply: construct_ring2; [done..|].
    move: H. apply: steps_pi_elim; first by apply: steps_H_0.
    move=> /steps_lamsE. rewrite ren_closed.
    { apply: allfv_closed. move: (H'M2)=> /stlc_subst_sigma_H /stlc_allfv_not_None + ?.
      apply: allfv_impl. by case. }
    by apply: steps_subst_sigma_H_pi_intro.
Qed.

Lemma construct_initial_abstractions (M : term) k1 k2 :
  normal_form M ->
  stlc (repeat A_0R k1) M (arrs (repeat A_0R k2 ++ [A; A_star; arr A A]) A) ->
  exists N, M = lams (k2 + 2) N /\ normal_form N.
Proof.
  elim: k2 k1 M.
  - move=> k1 M /normal_form_nf [].
    + move=> ? /normal_form_nf []; first by eexists.
      move=> ? /neutralE' [x] [?] [->] _ /= /stlcE [] ?? [<- <-].
      move=> /stlc_appsE [ss] [_] /stlcE.
      case: x.
      * move=> [] /(f_equal ty_size). rewrite ty_size_arrs /=. lia.
      * move=> x /= /[dup] H. rewrite nth_error_repeat.
        { rewrite -(repeat_length A_0R k1). apply /nth_error_Some. by rewrite H. }
        move=> [] /(f_equal ty_size). rewrite ty_size_arrs /=. lia.
    + move=> ? /neutralE' [x] [?] [->] _ /stlc_appsE [ss] [_] /stlcE.
      move=> /[dup] H. rewrite nth_error_repeat.
      { rewrite -(repeat_length A_0R k1). apply /nth_error_Some. by rewrite H. }
      move=> [] /(f_equal ty_size). rewrite ty_size_arrs /=. lia.
  - move=> k2 IH k1 M HM. case /normal_form_nf: HM IH.
    + move=> ? + IH /= /stlcE [] ?? [<- <-] /(IH (S k1)) H.
      move=> /H [N] [->] ?. by eexists.
    + move=> ? /neutralE' [x] [?] [->] _ _ /stlc_appsE [ss] [_] /stlcE.
      move=> /[dup] H. rewrite nth_error_repeat.
      { rewrite -(repeat_length A_0R k1). apply /nth_error_Some. by rewrite H. }
      move=> [] /(f_equal ty_size). rewrite ty_size_arrs /=. lia.
Qed.

Lemma solution_shape (M : term) :
  normal_form M ->
  (* correctly typed closed term *)
  stlc [] M (arrs (repeat A_0R (length rules + 1) ++ [A; A_star; arr A A]) A) ->
  steps (apps M (repeat F_R (length rules) ++ [F_0; var 0; F_star; (lam (var 0))])) (var 0) ->
  steps (apps M (repeat H_R (length rules) ++ [H_0; H_1; H_star; delta bullet])) (pi dollar) ->
  exists N, M = lams (length rules + 4) N /\ ring1 1 N.
Proof.
  move=> /(construct_initial_abstractions M 0 _) + /[dup] => /[apply].
  move=> [N] [->] HN.
  change [A; A_star; arr A A] with ([A; A_star] ++ [arr A A]).
  rewrite app_assoc -arrs_arrs.
  have E: (length rules + 1 + 2) = length (repeat A_0R (length rules + 1) ++ [A; A_star]) by rewrite length_app repeat_length.
  rewrite [in stlc _ _ _]E.
  move=> /stlc_lamsE. rewrite repeat_app !rev_app_distr /= rev_repeat app_nil_r.
  case /normal_form_nf: HN.
  - move=> {}N HN /stlcE [] ?? [<- <-] + HFN HHN.
    move: HN => /(construct_ring1 _ 1) + /[dup] H'N => /[apply].
    apply: unnest.
    { apply: steps_var_elim HFN.
      { rewrite (lams_lams _ 1). apply: stepsReds'.
        by rewrite length_app repeat_length /=; lia. }
      move=> /(steps_ren S). congr steps.
      rewrite ren_subst_term /sigma_F !fold_left_app.
      apply: ext_stlc_subst_term H'N=> - [|[|[|[|x]]]] /=; [done..|].
      move=> /nth_error_Some. rewrite repeat_length=> H.
      rewrite fold_left_lt; first by (rewrite repeat_length; lia).
      rewrite rev_repeat -(map_nth (ren S)) map_repeat ren_closed; first by auto with allfv.
      apply: nth_indep. rewrite repeat_length. lia. }
    apply: unnest.
    { move: HHN. rewrite (lams_lams _ 1). apply: steps_pi_elim.
      { apply: stepsReds'. rewrite length_app repeat_length /=. lia. }
      congr steps. rewrite /sigma_H !fold_left_app.
      apply: ext_stlc_subst_term H'N=> - [|[|[|[|x]]]] /=; [done..|].
      move=> /nth_error_Some. rewrite repeat_length=> H.
      rewrite fold_left_lt; first by (rewrite repeat_length; lia).
      rewrite rev_repeat. apply: nth_indep. rewrite repeat_length. lia. }
    move=> ?. exists N. rewrite (lams_lams _ 1). split; last done.
    congr (lams _ _). lia.
  - (* typing contradiction *)
    move=> ? /neutralE' [x] [Ms] [->] HMs /stlc_appsE [ss] [H'Ms] /stlcE.
    move: x=> [|[|x]] /=.
    + rewrite (arrs_arrs _ [_]). move=> [] /arrs_inj.
      by move: (ss)=> [|?[|?[|??]]].
    + move=> [] /(f_equal ty_size). rewrite ty_size_arrs /=. lia.
    + move=> /[dup] Hx.
      have {}Hx: x < 1 + length rules.
      { have /nth_error_Some: nth_error (repeat A_0R (1 + length rules)) x <> None by rewrite Hx.
        by rewrite repeat_length. }
      change (_ :: repeat A_0R ?k) with (repeat A_0R (S k)).
      rewrite nth_error_repeat; first done.
      rewrite (arrs_arrs _ [_]). move=> [] /arrs_inj.
      by move: (ss)=> [|?[|?[|??]]].
Qed.

Lemma initial_applications i N :
  i - 2 = 0 ->
  stlc (Gamma_A 1) N A ->
  steps (apps (lams (length rules + 4) N) (rev (map G_R rules) ++ [G_0; G_1; G_star; delta (match i with | 0 => bullet | 1 => zero | _ => one end)]))
    (subst (sigma_G 1 i) N).
Proof.
  move=> Hi H0M.
  apply: rt_trans.
  { apply: stepsReds'. by rewrite length_app length_rev length_map /=. }
  rewrite fold_left_app. apply: steps_refl.
  apply: ext_stlc_subst_term H0M.
  have H : forall x k,
    match x with
    | S (S (S (S y))) => x < length (Gamma_A 1) ->
        fold_left (fun sigma N => scons N sigma) (rev (map G_R rules)) var y = sigma_G 1 k x
    | _ => True
    end.
  { move=> [|[|[|[|x]]]] k; [done..|].
    move=> Hx.
    have H'x : x < length rules.
    { rewrite length_Gamma_A in Hx. lia. }
    rewrite fold_left_lt ?rev_involutive; first by rewrite length_rev length_map.
    apply: nth_error_nth. rewrite nth_error_map.
    move: (H'x) => /nth_error_Some.
    case E: (nth_error rules x) => [rule|]; last done.
    have ->: S (S (S (S x))) = x + 3 + 1 by lia.
    by rewrite (sigma_G_rule _ _ x rule E). }
  move: i Hi=> [|[|[|i]]] ? [|[|[|[|x]]]] /nth_error_Some; by [|apply: (H ((S (S (S (S x))))))].
Qed.

Lemma sigma_G_ring_1_elim m N :
  ring1 m N ->
  stlc (Gamma_A m) N A ->
  steps (subst (sigma_G m 0) N) (pi dollar) ->
  steps (subst (sigma_G m 1) N) (pi one) ->
  Forall (fun i => steps (subst (sigma_G m (S (S i))) N) (pi zero)) (seq 0 m) ->
  exists M k, ring2 (k + m) M /\
    stlc (Gamma_A (k + m)) M A /\
    steps (subst (sigma_G (k + m) 0) M) (pi one) /\
    steps (subst (sigma_G (k + m) 1) M) (pi zero) /\
    Forall (fun i => steps (subst (sigma_G (k + m) (S (S i))) M) (pi zero)) (seq 0 (k+m)).
Proof. 
  elim.
  - move=> {}m {}N N' ? IH.
    move=> /stlc_appsE [[|? [|? [|??]]]] [] /[dup] /Forall2_length; [done|done| |done].
    move=> _ /Forall2_cons_iff [HN'] /Forall2_cons_iff [HN] _.
    move=> /stlcE. rewrite Gamma_A_space=> - [??]. subst.
    move: (HN) => /stlcE [] ?? [<- <-] H'N.
    rewrite !subst_apps /= !sigma_G_star.
    move=> /steps_G_star_dollar_elim.
    apply: unnest.
    { move=> P. apply: stlc_closed. apply: stlc_subst_sigma_G HN'. }
    apply: unnest. 
    { change (lam (subst _ N)) with (subst (sigma_G m 0) (lam N)).
      apply: stlc_subst; first by eassumption.
      by apply: stlc_sigma_G. }
    move=> [].
    have ->: subst (scons (delta zero) var) (subst (up (sigma_G m 0)) N) = subst (sigma_G (S m) 1) N.
    { rewrite subst_subst_term.
      apply: ext_stlc_subst_term H'N=> - [|?] /=; first done.
      move=> /nth_error_Some.
      rewrite subst_ren_term /= subst_var_term length_Gamma_A.
      by move=> /sigma_G_S_shift ->. }
    have ->: (subst (scons (delta bullet) var) (subst (up (sigma_G m 0)) N)) = subst (sigma_G (S m) 0) N.
    { rewrite subst_subst_term.
      apply: ext_stlc_subst_term H'N=> - [|?] /=; first done.
      move=> /nth_error_Some.
      rewrite subst_ren_term /= subst_var_term length_Gamma_A.
      by move=> /sigma_G_0_shift ->. }
    move=> /IH /[apply].
    apply: unnest.
    { by move: HN => /stlcE [] ?? [<- <-]. }
    move=> {}IH /steps_G_star_one_elim.
    apply: unnest. 
    { move=> P. apply: allfv_subst. move: HN' => /stlc_allfv_not_None. apply: allfv_impl.
      move=> ? /nth_error_Some. by apply: sigma_G_closed. }
    apply: unnest. 
    { change (lam (subst _ N)) with (subst (sigma_G m 1) (lam N)).
      apply: stlc_subst; first by eassumption.
      by apply: stlc_sigma_G. }
    have ->: (subst (scons (delta one) var) (subst (up (sigma_G m 1)) N)) = subst (sigma_G (S m) 2) N.
    { rewrite subst_subst_term. apply: ext_stlc_subst_term H'N=> - [|?] /=; first done.
      move=> /nth_error_Some. rewrite length_Gamma_A=> ?.
      by rewrite subst_ren_term subst_var_term sigma_G_S_shift. }
    move=> {}H''N H.
    move: IH. apply: unnest.
    { rewrite /= -seq_shift. constructor; first done.
      apply /Forall_map. apply: Forall_impl H.
      move=> i. rewrite sigma_G_star.
      move=> /steps_G_star_zero_elim.
      apply: unnest. 
      { move=> P. apply: allfv_subst. move: HN' => /stlc_allfv_not_None. apply: allfv_impl.
        move=> ? /nth_error_Some. by apply: sigma_G_closed. }
      apply: unnest. 
      { change (lam (subst _ N)) with (subst (sigma_G m (S (S i))) (lam N)).
        apply: stlc_subst; first by eassumption.
        by apply: stlc_sigma_G. }
      congr steps. rewrite subst_subst_term.
      apply: ext_stlc_subst_term H'N=> - [|?] /=; first done.
      move=> /nth_error_Some. rewrite length_Gamma_A=> ?.
      by rewrite subst_ren_term subst_var_term sigma_G_S_shift. }
    move=> [M] [k] [?] [?] [?] [?] ?.
    exists M, (S k).
    have ->: S k + m = k + S m by lia.
    by split; [|split; [|split; [|split]]].
  - move=> {}m {}N M HN /stlcE [] ? /stlcE [] ? /stlcE.
    rewrite Gamma_A_init=> - [??] _ H'N. subst.
    rewrite /= !sigma_G_init.
    move: (H'N) => /stlc_subst_sigma_G H''N.
    move: (H''N 0)=> /steps_G_0_dollar_elim /[apply] ?.
    move: (H''N 1)=> /steps_G_0_one_elim /[apply] ?.
    exists N, 0. do 4 (split; first done).
    apply: Forall_impl H => - [|y] /=; rewrite sigma_G_init.
    + by move: (H''N 2)=> /steps_G_0_zero_elim /[apply].
    + by move: (H''N (S (S (S y))))=> /steps_G_0_zero_elim /[apply].
Qed.

#[local] Arguments seq : simpl never.

Lemma sigma_G_ring_2_elim v m M :
  m > 0 ->
  length v = S m ->
  ring2 m M ->
  stlc (Gamma_A m) M A ->
  steps (subst (sigma_G m 0) M) (pi one) ->
  Forall2 (fun i a => sym a < n /\ steps (subst (sigma_G m (S i)) M) (pi (sym a))) (seq 0 (S m)) v ->
  SSTS.multi_step rules v (repeat 1 (S m)).
Proof.
  move=> ++ H. elim: H v.
  - move=> x y {}M ? IH Hx Hy v Hm Hv.
    move=> /stlcE [] ? /stlcE [] ? /stlcE.
    case E: (nth_error rules x) => [rule|]; first last.
    { move: E=> /nth_error_None. lia. }
    rewrite Gamma_A_rule; [lia..|].
    move=> [??] _ /=. subst.
    move=> /[dup] /IH {}IH HM.
    move: (E)=> /sigma_G_rule ->.
    rewrite sigma_G_pos_0; first done.
    move=> /steps_G_R_bullet_elim.
    apply: unnest; first done.
    apply: unnest. { by apply: stlc_subst_sigma_G. }
    move=> /IH {}IH H.
    have [u1 [a [b [u2 [??]]]]] : exists u1 a b u2, v = u1 ++ a :: b :: u2 /\ length u1 = y.
    { have /(nth_split _ 0) : y < length v by lia.
      move=> [u1] [[|b u2]].
      - move=> [/(f_equal (@length nat))]. rewrite length_app /=. lia.
      - move=> [-> <-]. by exists u1, (nth (length u1) v 0), b, u2. }
    subst v. move: (H). 
    move=> /Forall2_app_inv_r => - [l1] [l2] [] Hu1.
    move: l2=> [|i1 [|i2 l2]] [] /[dup] /Forall2_length; [done..|].
    move=> [?] /Forall2_cons_iff [[_ Ha]] /Forall2_cons_iff [[_ Hb]] Hu2 H'v.
    move: (Hu1) => /Forall2_length ?.
    have ? : i1 = length u1.
    { move: H'v => /(f_equal (fun (l : list nat) => nth_error l (length l1))).
      rewrite nth_error_seq; first lia.
      rewrite nth_error_app2; first done.
      rewrite Nat.sub_diag /=.
      by move=> [<-]. }
    have ? : i2 = S i1.
    { move: H'v => /(f_equal (fun (l : list nat) => nth_error l (S (length l1)))).
      rewrite nth_error_seq; first lia.
      rewrite nth_error_app2; first lia.
      have ->: S (length l1) - length l1 = 1 by lia.
      move=> [<-]. lia. }
    subst.
    (* left symbol transition *)
    move: (E) Ha => /sigma_G_rule ->.
    rewrite sigma_G_pos_S; first lia.
    rewrite Nat.eqb_refl=> /steps_G_R_L_elim.
    have ? : wf_rule rule by apply: (nth_error_wf_rule _ rule E).
    apply: unnest; first done.
    apply: unnest. { by apply: stlc_subst_sigma_G. }
    move=> [?]. subst a.
    (* right symbol transition *)
    move: (E) Hb => /sigma_G_rule ->.
    rewrite sigma_G_pos_S; first lia.
    rewrite Nat.eqb_refl.
    have /Nat.eqb_neq -> : S (length u1) <> length u1 by lia.
    move=> /steps_G_R_R_elim.
    apply: unnest; first done.
    apply: unnest. { by apply: stlc_subst_sigma_G. }
    move=> [?] Hd Hc. subst b.
    move: (IH (u1 ++ fst (snd rule) :: snd (snd rule) :: u2) Hm).
    apply: unnest. { move: Hv. by rewrite !length_app. }
    apply: unnest.
    { move: H. destruct m as [|m]; first by lia.
      move: (E)=> /nth_error_wf_rule [????].
      apply: Forall2_change2; [done..|].
      move=> i y ? Hi H'i [?] H. split; first done.
      move: (E) H => /sigma_G_rule ->.
      rewrite sigma_G_pos_S; first lia.
      move: Hi H'i => /Nat.eqb_neq -> /Nat.eqb_neq ->.
      apply: steps_G_R_bullet_elim; first done.
      by apply: stlc_subst_sigma_G. }
    apply: rt_trans. apply: rt_step. constructor.
    move: E=> /nth_error_In.
    by move: (rule)=> [[??] [??]].
  - move=> x y {}M ? IH Hx Hy v Hm Hv.
    move=> /stlcE [] ? /stlcE [] ? /stlcE.
    case E: (nth_error rules x) => [rule|]; first last.
    { move: E=> /nth_error_None. lia. }
    rewrite Gamma_A_rule; [lia..|].
    move=> [??] _ /=. subst.
    move=> /[dup] /IH {}IH HM.
    move: (E)=> /sigma_G_rule ->.
    rewrite sigma_G_pos_0; first done.
    rewrite ren_delta; first done.
    move=> /steps_G_R_bullet_elim'.
    apply: unnest.
    { move=> *. apply: rt_trans.
      - move=> /=. by apply: stepsRed.
      - apply: steps_refl. by rewrite /= subst_subst_term subst_delta. }
    apply: unnest; first done.
    apply: unnest. { by apply: stlc_subst_sigma_G. }
    move=> /IH {}IH H.
    have [u1 [a [b [u2 [??]]]]] : exists u1 a b u2, v = u1 ++ a :: b :: u2 /\ length u1 = y.
    { have /(nth_split _ 0) : y < length v by lia.
      move=> [u1] [[|b u2]].
      - move=> [/(f_equal (@length nat))]. rewrite length_app /=. lia.
      - move=> [-> <-]. by exists u1, (nth (length u1) v 0), b, u2. }
    subst v. move: (H). 
    move=> /Forall2_app_inv_r => - [l1] [l2] [] Hu1.
    move: l2=> [|i1 [|i2 l2]] [] /[dup] /Forall2_length; [done..|].
    move=> [?] /Forall2_cons_iff [[_ Ha]] /Forall2_cons_iff [[_ Hb]] Hu2 H'v.
    move: (Hu1) => /Forall2_length ?.
    have ? : i1 = length u1.
    { move: H'v => /(f_equal (fun (l : list nat) => nth_error l (length l1))).
      rewrite nth_error_seq; first lia.
      rewrite nth_error_app2; first done.
      rewrite Nat.sub_diag /=.
      by move=> [<-]. }
    have ? : i2 = S i1.
    { move: H'v => /(f_equal (fun (l : list nat) => nth_error l (S (length l1)))).
      rewrite nth_error_seq; first lia.
      rewrite nth_error_app2; first lia.
      have ->: S (length l1) - length l1 = 1 by lia.
      move=> [<-]. lia. }
    subst.
    (* left symbol transition *)
    move: (E) Ha => /sigma_G_rule ->.
    rewrite sigma_G_pos_S; first lia.
    rewrite Nat.eqb_refl ren_delta; first done.
    move=> /steps_G_R_L_elim'.
    apply: unnest.
    { move=> * /=. apply: rt_trans; first by apply: stepsRed.
      apply steps_refl. by rewrite /= subst_subst_term subst_delta. }
    have ? : wf_rule rule by apply: (nth_error_wf_rule _ rule E).
    apply: unnest; first done.
    apply: unnest. { by apply: stlc_subst_sigma_G. }
    move=> [?]. subst a.
    (* right symbol transition *)
    move: (E) Hb => /sigma_G_rule ->.
    rewrite sigma_G_pos_S; first lia.
    rewrite Nat.eqb_refl.
    have /Nat.eqb_neq -> : S (length u1) <> length u1 by lia.
    rewrite ren_delta; first done.
    move=> /steps_G_R_R_elim'.
    apply: unnest.
    { move=> * /=. apply: rt_trans; first by apply: stepsRed.
      apply steps_refl. by rewrite /= subst_subst_term subst_delta. }
    apply: unnest; first done.
    apply: unnest. { by apply: stlc_subst_sigma_G. }
    move=> [?] Hd Hc. subst b.
    move: (IH (u1 ++ fst (snd rule) :: snd (snd rule) :: u2) Hm).
    apply: unnest. { move: Hv. by rewrite !length_app. }
    apply: unnest.
    { move: H. destruct m as [|m]; first by lia.
      move: (E)=> /nth_error_wf_rule [????].
      apply: Forall2_change2; [done..|].
      move=> i y ? Hi H'i [?] H. split; first done.
      move: (E) H => /sigma_G_rule ->.
      rewrite sigma_G_pos_S; first lia.
      move: Hi H'i => /Nat.eqb_neq -> /Nat.eqb_neq ->.
      rewrite ren_delta; first done.
      apply: steps_G_R_bullet_elim'.
      - move=> * /=. apply: rt_trans; first by apply: stepsRed.
        apply steps_refl. by rewrite /= subst_subst_term subst_delta.
      - done.
      - by apply: stlc_subst_sigma_G. }
    apply: rt_trans. apply: rt_step. constructor.
    move: E=> /nth_error_In.
    by move: (rule)=> [[??] [??]].
  - move=> v _ H1v _ _ H2v.
    suff: v = (repeat 1 (S m)).
    { move=> ->. by apply: rt_refl. }
    elim: v m H1v H2v; first done.
    move=> a v IH [|m] /= [].
    + move: (v) => [|??]; last done.
      move=> _ /Forall2_cons_iff [] [_]. rewrite sigma_G_fin.
      move=> /steps_lamsE /normal_form_steps.
      apply: unnest. { by constructor. }
      by move=> [->].
    + rewrite /seq /= -/seq.
      move=> /IH {}IH /Forall2_cons_iff [[_ Ha] Hv]. congr cons.
      * move: Ha. rewrite sigma_G_fin.
        move=> /steps_lamsE /normal_form_steps.
        apply: unnest. { by constructor. }
        by move=> [->].
      * apply: IH. move: Hv.
        change (1 :: seq 2 m) with (seq 1 (S m)).
        rewrite -seq_shift.
        move=> /Forall2_map_l. apply: Forall2_impl.
        move=> ??. by rewrite /= !sigma_G_fin.
Qed.

Theorem soundness M :
  stlc [] M (arrs (repeat A_0R (length rules + 1) ++ [A; A_star; arr A A]) A) ->
  steps (apps M (repeat F_R (length rules) ++ [F_0; var 0; F_star; lam (var 0)])) (var 0) ->
  steps (apps M (repeat H_R (length rules) ++ [H_0; H_1; H_star; delta bullet])) (pi dollar) ->
  steps (apps M (rev (map G_R rules) ++ [G_0; G_1; G_star; delta bullet])) (pi dollar) ->
  steps (apps M (rev (map G_R rules) ++ [G_0; G_1; G_star; delta zero])) (pi one) ->
  steps (apps M (rev (map G_R rules) ++ [G_0; G_1; G_star; delta one])) (pi zero) ->
  exists m, SSTS.multi_step rules (repeat 0 (S m)) (repeat 1 (S m)).
Proof.
  move=> /[dup] /stlc_wn [N] /[dup] HMN /stepsAppsL H'MN H1N.
  move: (HMN)=> /stlc_steps /[apply] H2N.
  apply: steps_var_elim; first by apply: H'MN.
  move=> /(solution_shape N H1N H2N) H.
  apply: steps_pi_elim; first by apply: H'MN.
  move=> /H - [N'] [?] HN'. subst N.
  have {}H2N : stlc (Gamma_A 1) N' A.
  { move: H2N => /stlc_lamsE'.
    rewrite length_app repeat_length -Nat.add_assoc /=.
    rewrite rev_app_distr rev_repeat /= app_nil_r (Nat.add_comm _ 1).
    by apply. }
  apply: steps_pi_elim; first by (apply: rt_trans; [apply: H'MN|apply: (initial_applications 0)]).
  move=> ?.
  apply: steps_pi_elim; first by (apply: rt_trans; [apply: H'MN|apply: (initial_applications 1)]).
  move=> ?.
  apply: steps_pi_elim; first by (apply: rt_trans; [apply: H'MN|apply: (initial_applications 2)]).
  move=> ?.
  move: HN' (H2N)=> /sigma_G_ring_1_elim /[apply].
  do 2 (apply: unnest; first done).
  apply: unnest; first by constructor.
  move=> [M'] [m] [?] [?] [?] [?] {}H. exists (m + 1).
  apply: (sigma_G_ring_2_elim _ (m + 1) M'); [lia|by rewrite repeat_length|done..|].
  rewrite /seq /= -/seq. constructor; first done.
  apply: Forall2_repeat_r'; last by rewrite length_seq.
  rewrite -seq_shift. apply /Forall_map.
  by apply: Forall_impl H.
Qed.

(* Correctness :
   given a simple semi-Thue system,
   if 0..0 rewrites to 1..1,
   then the constructed higher-order matching instance is solvable *)

(* expand tape to proper length *)
Fixpoint expand_tape m M :=
  match m with
  | 0 => M
  | S m => expand_tape m (apps (var (S m)) [var 0; lam M])
  end.

(* initialize tape with zeros *)
Definition init_tape m M := app (app (var (3 + m)) (var 0)) M.

Lemma stlc_expand_tape m N : stlc (Gamma_A (S m)) N A -> stlc (Gamma_A 1) (expand_tape m N) A.
Proof.
  elim: m N; first done.
  move=> m IH N ? /=. apply: IH.
  apply: stlc_app; [apply: stlc_app|].
  - apply: stlc_var. by apply: Gamma_A_space.
  - by apply: stlc_var.
  - by apply: stlc_lam.
Qed.

Lemma stlc_init_tape m N : stlc (Gamma_A (S m)) N A -> stlc (Gamma_A (S m)) (init_tape m N) A.
Proof.
  move=> ?. rewrite /init_tape.
  apply: stlc_app; [apply: stlc_app|].
  - apply: stlc_var. by apply: Gamma_A_init.
  - by apply: stlc_var.
  - done.
Qed.

Lemma steps_sigma_F_expand_tape m M : stlc (Gamma_A (S m)) M A -> steps (subst (sigma_F (S m)) M) (var (S m)) ->
  steps (subst (scons (lam (var 0)) var) (subst (up (sigma_F 0)) (expand_tape m M))) (var 0).
Proof.
  move=> HM.
  have -> : subst (sigma_F (S m)) M = ren S (subst (scons (lam (var 0)) var) (subst (up (sigma_F m)) M)).
  { rewrite ren_subst_term subst_subst_term.
    apply: ext_stlc_subst_term HM=> - [|?] /=; first done.
    move=> /nth_error_Some ?.
    by rewrite subst_ren_term /= -ren_as_subst_term -ren_S_sigma_F. }
  move=> /(steps_ren Nat.pred). rewrite ren_ren_term ren_id_term /=.
  elim: m M HM; first done.
  - move=> m IH M HM H'M. apply: IH.
    { apply: stlc_apps.
      - apply: stlc_var. by apply: Gamma_A_space.
      - constructor; [|constructor; [|constructor]].
        + by apply: stlc_var.
        + by apply: stlc_lam. }
    rewrite subst_apps /= subst_ren_term subst_var_term sigma_F_space.
    apply: rt_trans; first by apply: steps_F_star.
    apply: rt_trans; first by apply: stepsRed.
    rewrite !subst_subst_term/=.
    move: H'M => /(steps_ren Nat.pred). congr steps.
    rewrite ren_subst_term subst_subst_term/=.
    apply: ext_stlc_subst_term HM=> - [|[|?]] /=; [done..|].
    move=> /nth_error_Some ?.
    rewrite !subst_ren_term -ren_S_sigma_F; first done.
    by rewrite subst_ren_term.
Qed.

Lemma steps_sigma_F_init_tape m M : steps (subst (sigma_F (S m)) M) (var (S m)) -> steps (subst (sigma_F (S m)) (init_tape m M)) (var (S m)).
Proof.
  move=> H. rewrite /init_tape /= sigma_F_init.
  by apply: rt_trans; first apply: steps_F_0.
Qed.

(* any ring 1 term which is properly typed reduces to the desired variable wrt. the shape constraint *)
Lemma ring2_steps_sigma_G m (M N : term) :
  M = lams (length rules + 4) (expand_tape m (init_tape m N)) ->
  ring2 (S m) N ->
  (* correctly typed closed term *)
  stlc (Gamma_A (S m)) N A ->
  (* Loader equation *)
  steps (apps M (repeat F_R (length rules) ++ [F_0; var 0; F_star; (lam (var 0))])) (var 0).
Proof.
  move=> -> HN /[dup] H' /stlc_init_tape /stlc_expand_tape H.
  apply: rt_trans.
  { apply: stepsReds'. by rewrite length_app repeat_length /=. }
  apply: rt_trans; first last.
  { move: (H') => /stlc_init_tape /steps_sigma_F_expand_tape. apply.
    apply: steps_sigma_F_init_tape.
    move: (S m) HN H' {H}=> {}m. elim.
    - move=> > ? IH ?? /stlcE [] ? /stlcE [] ? /stlcE + _.
      rewrite Gamma_A_rule; [lia..|].
      move=> [_ <-] ?.
      rewrite /= sigma_F_rule; [rewrite ?length_Gamma_A; lia..|].
      rewrite sigma_F_pos; first done.
      apply: rt_trans; first by apply: steps_F_R.
      apply: rt_trans; first by apply: stepsRed.
      by apply: IH.
    - move=> > ? IH ?? /stlcE [] ? /stlcE [] ? /stlcE + _.
      rewrite Gamma_A_rule; [lia..|].
      move=> [_ <-] ?.
      rewrite /= sigma_F_rule; [rewrite ?length_Gamma_A; lia..|].
      apply: rt_trans; first by apply: steps_F_R.
      rewrite /= sigma_F_pos; first done.
      apply: rt_trans; first by apply: stepsRed.
      apply: rt_trans.
      { rewrite /=. by apply: stepsRed. }
      by apply: IH.
    - move=> _. rewrite /= sigma_F_fin. by apply: rt_refl. }
  apply: steps_refl.
  rewrite /sigma_F. rewrite fold_left_app subst_subst_term.
  apply: ext_stlc_subst_term H=> - [|[|[|[|x]]]] /= Hx; [done..|].
  have ? : x < length (repeat F_R (length rules)).
  { move: Hx=> /nth_error_Some. by rewrite !repeat_length. }
  rewrite fold_left_lt; first done.
  rewrite rev_repeat subst_ren_term /= subst_var_term.
  by apply: nth_indep.
Qed.

Lemma steps_sigma_H_expand_tape m M : stlc (Gamma_A (S m)) M A -> steps (subst (sigma_H (S m)) M) (pi dollar)->
  steps (subst (sigma_H 1) (expand_tape m M)) (pi dollar).
Proof.
  elim: m M; first done.
  move=> m IH M HM H'M. apply: IH.
  { apply: stlc_apps.
    - apply: stlc_var. by apply: Gamma_A_space.
    - constructor; [|constructor; [|constructor]].
      + by apply: stlc_var.
      + by apply: stlc_lam. }
  rewrite subst_apps /= sigma_H_space sigma_H_pos; first by lia.
  apply: rt_trans; first by apply: steps_H_star.
  apply: stepsLams.
  apply: rt_trans.
  { rewrite /=. apply: stepsAppsL. by apply: stepsRed. }
  rewrite subst_ren_term subst_subst_term/=.
  apply: rt_trans.
  { apply: stepsAppsL. move: H'M. congr steps.
    apply: ext_stlc_subst_term HM=> - [|?] /=; first done.
    move=> /nth_error_Some /= ?. rewrite ren_S_sigma_H; first done.
    rewrite subst_closed; last done.
    apply: allfv_closed. apply: sigma_H_closed. rewrite /=. lia. }
  by apply: steps_pi_eq.
Qed.

Lemma steps_sigma_H_init_tape m M : steps (subst (sigma_H (S m)) M) (pi one) ->
  steps (subst (sigma_H (S m)) (init_tape m M)) (pi dollar).
Proof.
  move=> H. rewrite /init_tape /= sigma_H_init.
  apply: rt_trans; first by apply: steps_H_0.
  apply: stepsLams. apply: rt_trans.
  { apply: stepsAppsL. apply: steps_ren. by eassumption. }
  rewrite ren_pi; first done.
  by apply: steps_pi_eq.
Qed.

(* any well-typed ring1 solution reduces correctly wrt. second shape constraint *)
Lemma ring2_steps_sigma_H m (M N : term) :
  M = lams (length rules + 4) (expand_tape m (init_tape m N)) ->
  ring2 (S m) N ->
  (* correctly typed closed term *)
  stlc (Gamma_A (S m)) N A ->
  (* Dudenhefner equation *)
  steps (apps M (repeat H_R (length rules) ++ [H_0; H_1; H_star; delta bullet])) (pi dollar).
Proof.
  move=> -> HN /[dup] H' /stlc_init_tape /stlc_expand_tape H.
  apply: rt_trans.
  { apply: stepsReds'. by rewrite length_app repeat_length. }
  apply: rt_trans; first last.
  { move: (H') => /stlc_init_tape /steps_sigma_H_expand_tape. apply.
    apply: steps_sigma_H_init_tape.
    move: (S m) HN H' {H}=> {}m. elim.
    - move=> > ? IH ?? /stlcE [] ? /stlcE [] ? /stlcE + _.
      rewrite Gamma_A_rule; [lia..|].
      move=> [_ <-] H.
      rewrite /= sigma_H_rule; [rewrite ?length_Gamma_A; lia..|].
      rewrite sigma_H_pos; first done.
      apply: rt_trans; first by apply: steps_H_R.
      apply: stepsLams. apply: rt_trans.
      { rewrite /= ren_delta; first done. by apply: steps_delta_eq. }
      apply: rt_trans; first by apply: steps_pi_eq.
      rewrite ren_closed.
      { apply: allfv_closed. apply: subst_sigma_H_closed. by eassumption. }
      apply: rt_trans.
      { apply: stepsAppsL. by apply: IH. }
      by apply: steps_pi_eq.
    - move=> > ? IH ?? /stlcE [] ? /stlcE [] ? /stlcE + _.
      rewrite Gamma_A_rule; [lia..|].
      move=> [_ <-] H.
      rewrite /= sigma_H_rule; [rewrite ?length_Gamma_A; lia..|].
      apply: rt_trans; first by apply: steps_H_R.
      apply: stepsLams. rewrite /= sigma_H_pos; first done.
      apply: rt_trans.
      { apply: stepsAppsL. by apply: stepsRed. }
      apply: rt_trans.
      { rewrite /= !subst_ren_term subst_delta; first done. by apply: steps_delta_eq. }
      apply: rt_trans; first by apply: steps_pi_eq.
      rewrite ren_closed.
      { apply: allfv_closed. apply: subst_sigma_H_closed. by eassumption. }
      apply: rt_trans.
      { apply: stepsAppsL. by apply: IH. }
      by apply: steps_pi_eq.
    - move=> _. rewrite /= sigma_H_fin. by apply: rt_refl. }
  apply: steps_refl. rewrite fold_left_app /sigma_H.
  apply: ext_stlc_subst_term H=> - [|[|[|[|x]]]] /= Hx; [done..|].
  have ? : x < length (repeat H_R (length rules)).
  { move: Hx=> /nth_error_Some. by rewrite !repeat_length. }
  rewrite fold_left_lt; first done.
  rewrite rev_repeat. by apply: nth_indep.
Qed.

Lemma ring2_allfv m M : ring2 m M -> allfv (fun x => x < m + 3 + length rules) M.
Proof.
  elim=> * /=.
  - split; last done. lia.
  - split; last done. lia.
  - lia.
Qed.

Lemma ssts_simulate_rewrite m v :
  SSTS.multi_step rules v (repeat 1 (S (S m))) ->
  exists M, ring2 (S m) M /\
    stlc (Gamma_A (S m)) M A /\ 
    steps (subst (sigma_G (S m) 0) M) (pi one) /\
    Forall2 (fun i a => sym a < n /\ steps (subst (sigma_G (S m) (S i)) M) (pi (sym a))) (seq 0 (S (S m))) v.
Proof.
  move E: (repeat 1 (S (S m))) => w /clos_rt_rt1n_iff H.
  elim: H E.
  { move=> ? <-. exists (var (S (S m))). split; [|split; [|split]].
    - by constructor.
    - constructor. by rewrite Gamma_A_fin.
    - rewrite /= sigma_G_fin. by apply: rt_refl.
    - apply: Forall2_repeat_r'; last by rewrite length_seq.
      apply /Forall_forall=> ? /in_seq ?. split; first done.
      rewrite /= sigma_G_fin. by apply: rt_refl. }
  move=> > [] u1 u2 > /(In_nth_error rules) [x] Hx.
  move=> _ /[apply] - [M] [H1M] [H0M] [H2M H3M].
  exists (app (app (var (x + 3 + (S m))) (var (length u1))) M).
  have ? : length u1 < S m.
  { move: H3M => /Forall2_length. rewrite length_app /= length_seq. lia. }
  have ? : x < length rules by (apply /nth_error_Some; rewrite Hx).
  split; [|split; [|split]].
  - by constructor.
  - apply: stlc_app; [apply: stlc_app; apply: stlc_var|].
    + rewrite Gamma_A_rule; by [|lia].
    + by rewrite Gamma_A_pos.
    + done.
  - rewrite /=. move: (Hx)=> /sigma_G_rule ->.
    rewrite sigma_G_pos_0; first done.
    apply: rt_trans; first by apply: steps_G_R_bullet.
    apply: stepsLams. apply: rt_trans.
    { apply: stepsAppsL. apply: steps_ren. by eassumption. }
    rewrite ren_pi; first done.
    by apply: steps_pi_full.
  - move: (Hx) => /nth_error_In.
    move: (wf_rules) => /Forall_forall /[apply] /[dup] H_rule [????].
    apply: Forall2_change2 H3M.
    + move=> [_ H3M]. split; first done.
      rewrite /=. move: (Hx)=> /sigma_G_rule ->.
      rewrite sigma_G_pos_S; first done.
      rewrite Nat.eqb_refl.
      apply: rt_trans; first by apply: steps_G_R_L.
      apply: stepsLams. apply: rt_trans.
      { apply: stepsAppsL. apply: steps_ren. by eassumption. }
      rewrite ren_pi; first done.
      by apply: steps_pi_eq.
    + move=> [_ H3M]. split; first done.
      rewrite /=. move: (Hx)=> /sigma_G_rule ->.
      rewrite sigma_G_pos_S; first done.
      rewrite Nat.eqb_refl.
      have /Nat.eqb_neq -> : S (length u1) <> length u1 by lia.
      apply: rt_trans; first by apply: steps_G_R_R.
      apply: stepsLams. apply: rt_trans.
      { apply: stepsAppsL. apply: steps_ren. by eassumption. }
      rewrite ren_pi; first done.
      by apply: steps_pi_eq.
    + move=> y a H1y H2y H3y [? ?]. split; first done.
      rewrite /=. move: (Hx)=> /sigma_G_rule ->.
      rewrite sigma_G_pos_S; first done.
      move: H2y H3y => /Nat.eqb_neq -> /Nat.eqb_neq ->.
      apply: rt_trans; first by apply: steps_G_R_bullet.
      apply: stepsLams. apply: rt_trans.
      { apply: stepsAppsL. apply: steps_ren. by eassumption. }
      rewrite ren_pi; first done.
      by apply: steps_pi_full.
Qed.

Lemma ssts_to_sigma_G_steps m :
  SSTS.multi_step rules (repeat 0 (S (S m))) (repeat 1 (S (S m))) ->
  exists N : term, ring2 (S m) N /\
    stlc (Gamma_A (S m)) N A /\
    steps (subst (sigma_G 1 0) (expand_tape m (init_tape m N))) (pi dollar) /\
    steps (subst (sigma_G 1 1) (expand_tape m (init_tape m N))) (pi one) /\
    steps (subst (sigma_G 1 2) (expand_tape m (init_tape m N))) (pi zero).
Proof.
  move=> H_ssts.
  (* verify tape expansion *)
  suff: exists N, ring2 (S m) N /\
    stlc (Gamma_A (S m)) N A /\
    steps (subst (sigma_G (S m) 0) (init_tape m N)) (pi dollar) /\
    steps (subst (sigma_G (S m) 1) (init_tape m N)) (pi one) /\
    Forall (fun i => steps (subst (sigma_G (S m) (S (S i))) (init_tape m N)) (pi zero)) (seq 0 (S m)).
  { move=> [N] [HN] [H0N] [H1N] [H2N H3N]. exists N. split; [|split]; [done..|].
    have : allfv (fun x => x <= m + 3 + length rules) (init_tape m N).
    { rewrite /=. split; first lia. move: HN => /ring2_allfv.
      apply: allfv_impl. lia. }
    elim: m (init_tape m N) {H0N} H1N H2N H3N {HN H_ssts}.
    { by move=> > ?? /Forall_cons_iff []. }
    move=> m IH {}N H1N H2N H3N HN /=. apply: IH.
    - rewrite /= sigma_G_star (sigma_G_pos_0 _ 0); first lia.
      apply: steps_G_star_dollar.
      + by apply: rt_refl.
      + move: H1N. congr steps.
        rewrite subst_subst_term. apply: ext_allfv_subst_term. apply: allfv_impl HN.
        move=> [|x] /= ?; first done.
        rewrite subst_ren_term /= subst_var_term.
        apply: sigma_G_0_shift. lia.
      + move: H2N. congr steps.
        rewrite subst_subst_term. apply: ext_allfv_subst_term. apply: allfv_impl HN.
        move=> [|x] /= ?; first done.
        rewrite subst_ren_term /= subst_var_term.
        apply: sigma_G_S_shift. lia.
    - rewrite /= sigma_G_star (sigma_G_pos_S _ 0) /=; first lia.
      apply: steps_G_star_one.
      + by apply: rt_refl.
      + move: H3N => /= /Forall_cons_iff [+ _]. congr steps.
        rewrite subst_subst_term. apply: ext_allfv_subst_term. apply: allfv_impl HN.
        move=> [|x] /= ?; first done.
        rewrite subst_ren_term /= subst_var_term.
        apply: sigma_G_S_shift. lia.
    - apply /Forall_forall=> - [|x].
      + move=> _. rewrite /= sigma_G_star sigma_G_pos_S /=; first lia.
        apply: steps_G_star_R_zero.
        * by apply: rt_refl.
        * move: H3N => /= /Forall_cons_iff [_] /Forall_cons_iff [+ _]. congr steps.
          rewrite subst_subst_term. apply: ext_allfv_subst_term. apply: allfv_impl HN.
          move=> [|x] /= ?; first done.
          rewrite subst_ren_term /= subst_var_term.
          apply: sigma_G_S_shift. lia.
      + move=> /in_seq ?.
        rewrite /= sigma_G_star sigma_G_pos_S /=; first lia.
        apply: steps_G_star_bullet_zero.
        * by apply: rt_refl.
        * move: H3N => /Forall_forall /(_ (S (S x))).
          apply: unnest. { apply /in_seq. lia. }
          congr steps.
          rewrite /= subst_subst_term. apply: ext_allfv_subst_term. apply: allfv_impl HN.
          move=> [|y] /= ?; first done.
          rewrite subst_ren_term /= subst_var_term.
          apply: sigma_G_S_shift. lia.
    - rewrite /=. split; [split|]; [lia..|].
      apply: allfv_impl HN=> - [|x] /=; by [|lia]. }
  (* init tape *)
  suff: exists N : term, ring2 (S m) N /\
    stlc (Gamma_A (S m)) N A /\
    steps (subst (sigma_G (S m) 0) N) (pi one) /\
    Forall (fun i : nat => steps (subst (sigma_G (S m) (S i)) N) (pi zero)) (seq 0 (S (S m))).
  { move=> [N] [HN] [H0N] [H1N H2N]. exists N. split; [|split]; [done..|].
    rewrite /init_tape /=. split; [|split].
    - rewrite sigma_G_init sigma_G_pos_0; first lia.
      apply: rt_trans; first by apply: steps_G_0_bullet.
      apply: stepsLams. apply: rt_trans.
      { apply: stepsAppsL. apply: steps_ren. by eassumption. }
      apply: rt_trans.
      { rewrite ren_pi; first done. by apply: steps_pi_neq. }
      apply: rt_trans.
      { apply: stepsAppsL. apply: steps_ren. by eassumption. }
      rewrite ren_pi; first done. by apply: steps_pi_eq.
    - rewrite sigma_G_init sigma_G_pos_S /=; first lia.
      apply: rt_trans; first by apply: steps_G_0_L.
      apply: stepsLams. apply: rt_trans.
      { apply: stepsAppsL. apply: steps_ren. move: H2N => /Forall_cons_iff [+ _]. by apply. }
      rewrite ren_pi; first done. by apply: steps_pi_eq.
    - move: H2N => /= /Forall_cons_iff [_].
      have ->: 1 :: seq 2 m = map S (seq 0 (S m)) by rewrite /= seq_shift.
      move=> /Forall_map.
      apply: Forall_Forall_impl.
      apply /Forall_forall => - [|x] /in_seq ? H3N.
      + rewrite sigma_G_init sigma_G_pos_S /=; first lia.
        apply: rt_trans; first by apply: steps_G_0_R.
        apply: stepsLams. apply: rt_trans.
        { apply: stepsAppsL. apply: steps_ren. by eassumption. }
        rewrite ren_pi; first done. by apply: steps_pi_eq.
      + rewrite sigma_G_init sigma_G_pos_S /=; first lia.
        apply: rt_trans; first by apply: steps_G_0_bullet.
        apply: stepsLams. apply: rt_trans.
        { apply: stepsAppsL. apply: steps_ren. by eassumption. }
        rewrite ren_pi; first done. by apply: steps_pi_eq. }
  (* actual tape operations *)
  move: H_ssts => /ssts_simulate_rewrite [N] [?] [? [? /Forall2_repeat_r HN]].
  exists N. split; [|split; [|split]]; [done..|].
  apply: Forall_impl HN. by move=> ? [].
Qed.

(* if ssrs rewrites zeroes to ones, then there is a solution of the higher-order matching problem *)
Theorem completeness m :
  SSTS.multi_step rules (repeat 0 (S m)) (repeat 1 (S m)) ->
  exists M,
    stlc [] M (arrs (repeat A_0R (length rules + 1) ++ [A; A_star; arr A A]) A) /\
    steps (apps M (repeat F_R (length rules) ++ [F_0; var 0; F_star; lam (var 0)])) (var 0) /\
    steps (apps M (repeat H_R (length rules) ++ [H_0; H_1; H_star; delta bullet])) (pi dollar) /\
    steps (apps M (rev (map G_R rules) ++ [G_0; G_1; G_star; delta bullet])) (pi dollar) /\
    steps (apps M (rev (map G_R rules) ++ [G_0; G_1; G_star; delta zero])) (pi one) /\
    steps (apps M (rev (map G_R rules) ++ [G_0; G_1; G_star; delta one])) (pi zero).
Proof.
  case: m => [|m].
  { (* impossible to rewrite 0 to 1 *)
    move=> H.
    suff: forall v w, SSTS.multi_step rules v w -> v = w \/ length v > 1.
    { move=> /(_ _ _ H) /=. case; by [|lia]. }
    move=> ??. elim.
    - move=> > [] *. right. rewrite length_app /=. lia.
    - move=> ?. by left.
    - by move=> > _ [<-|?] _ [<-|?]; tauto. }
  move=> /ssts_to_sigma_G_steps [M] [HM] [H0M] [H1M [H2M H3M]].
  exists (lams (length rules + 4) (expand_tape m (init_tape m M))).
  have H'0M : stlc (Gamma_A 1) (expand_tape m (init_tape m M)) A.
  { apply: stlc_expand_tape. by apply: stlc_init_tape. }
  split; [|split; [|split]].
  - apply: stlc_lams.
    + rewrite length_app repeat_length /=. lia.
    + move: H'0M. congr stlc.
      by rewrite /Gamma_A app_nil_r rev_app_distr rev_repeat (Nat.add_comm 1).
  - by apply: ring2_steps_sigma_G.
  - by apply: ring2_steps_sigma_H.
  - split; [|split].
    + apply: rt_trans; last by eassumption.
      by apply: (initial_applications 0).
    + apply: rt_trans; last by eassumption.
      by apply: (initial_applications 1).
    + apply: rt_trans; last by eassumption.
      by apply: (initial_applications 2).
Qed.

(* combination of soundness and completeness theorems *)
Lemma correctness : SSTS.SSTS01 rules <-> 
  (exists M,
    stlc [] M (arrs (repeat A_0R (length rules + 1) ++ [A; A_star; arr A A]) A) /\
    steps (apps M (repeat F_R (length rules) ++ [F_0; var 0; F_star; lam (var 0)])) (var 0) /\
    steps (apps M (repeat H_R (length rules) ++ [H_0; H_1; H_star; delta bullet])) (pi dollar) /\
    steps (apps M (rev (map G_R rules) ++ [G_0; G_1; G_star; delta bullet])) (pi dollar) /\
    steps (apps M (rev (map G_R rules) ++ [G_0; G_1; G_star; delta zero])) (pi one) /\
    steps (apps M (rev (map G_R rules) ++ [G_0; G_1; G_star; delta one])) (pi zero)).
Proof.
  split.
  - by move=> [m] /completeness.
  - move=> [M] ?. by apply: (soundness M); tauto.
Qed.

Definition HOM_A := (arrs (repeat A_0R (length rules + 1) ++ [A; A_star; arr A A]) A).
Definition HOM_B := arr (arrs [arr A A; A; A; A; A] atom) atom.
Definition HOM_f := lam (lam (apps (var 0) [
  (lam (apps (var 2) (repeat F_R (length rules) ++ [F_0; var 0; F_star; lam (var 0)])));
  (apps (var 1) (repeat H_R (length rules) ++ [H_0; H_1; H_star; delta bullet]));
  (apps (var 1) (rev (map G_R rules) ++ [G_0; G_1; G_star; delta bullet]));
  (apps (var 1) (rev (map G_R rules) ++ [G_0; G_1; G_star; delta zero]));
  (apps (var 1) (rev (map G_R rules) ++ [G_0; G_1; G_star; delta one]))])).
Definition HOM_b := lam (apps (var 0) [lam (var 0); pi dollar; pi dollar; pi one; pi zero]).

Lemma stlc_HOM_f : stlc [] HOM_f (arr HOM_A HOM_B).
Proof.
  rewrite /HOM_f /HOM_A /HOM_B.
  apply: stlc_lam. apply: stlc_lam.
  apply: stlc_apps; first by apply: stlc_var.
  constructor; [|constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]]].
  - apply: stlc_lam. apply: stlc_apps; first by apply: stlc_var.
    rewrite repeat_app -app_assoc /=.
    apply: Forall2_app.
    + apply: Forall2_repeat. by apply: stlc_F_R.
    + by auto 7 with stlc.
  - apply: stlc_apps; first by apply: stlc_var.
    rewrite repeat_app -app_assoc /=. apply: Forall2_app.
    + apply: Forall2_repeat. by apply: stlc_H_R.
    + by auto 6 with stlc.
  - apply: stlc_apps; first by apply: stlc_var.
    rewrite repeat_app -app_assoc /=. apply: Forall2_app.
    + apply: Forall2_repeat_r'; last by rewrite length_rev length_map.
      apply /Forall_rev /Forall_map. apply: Forall_impl (wf_rules).
      move=> ?. by apply: stlc_G_rule.
    + by auto 6 with stlc.
  - apply: stlc_apps; first by apply: stlc_var.
    rewrite repeat_app -app_assoc /=. apply: Forall2_app.
    + apply: Forall2_repeat_r'; last by rewrite length_rev length_map.
      apply /Forall_rev /Forall_map. apply: Forall_impl (wf_rules).
      move=> ?. by apply: stlc_G_rule.
    + by auto 6 with stlc.
  - apply: stlc_apps; first by apply: stlc_var.
    rewrite repeat_app -app_assoc /=. apply: Forall2_app.
    + apply: Forall2_repeat_r'; last by rewrite length_rev length_map.
      apply /Forall_rev /Forall_map. apply: Forall_impl (wf_rules).
      move=> ?. by apply: stlc_G_rule.
    + by auto 6 with stlc.
Qed.

Lemma stlc_HOM_b : stlc [] HOM_b HOM_B.
Proof.
  rewrite /HOM_b /HOM_B. apply: stlc_lam. apply: stlc_apps.
  - by apply: stlc_var.
  - constructor; [|constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]]]; [|by apply: stlc_pi..].
    apply: stlc_lam. by apply: stlc_var.
Qed.

Definition HOM_inst : { '(A, B, f, b) : (ty * ty * term * term) | stlc nil f (arr A B) /\ stlc nil b B } :=
  exist _ (HOM_A, HOM_B, HOM_f, HOM_b) (conj stlc_HOM_f stlc_HOM_b).

Lemma nf_HOM_b : normal_form HOM_b.
Proof. do ? constructor; by apply normal_form_pi. Qed.

Lemma steps_HOM_f M : stlc [] M HOM_A -> steps (app HOM_f M) 
  (lam (apps (var 0) [
    (lam (apps M (repeat F_R (length rules) ++ [F_0; var 0; F_star; lam (var 0)])));
    (apps M (repeat H_R (length rules) ++ [H_0; H_1; H_star; delta bullet]));
    (apps M (rev (map G_R rules) ++ [G_0; G_1; G_star; delta bullet]));
    (apps M (rev (map G_R rules) ++ [G_0; G_1; G_star; delta zero]));
    (apps M (rev (map G_R rules) ++ [G_0; G_1; G_star; delta one]))])).
Proof.
  move=> HM.
  have ren_M : forall xi, ren xi M  = M.
  { move=> xi. move: HM => /stlc_closed ?.
    rewrite ren_closed; last done. by apply: allfv_closed. }
  rewrite /HOM_f. apply: rt_trans; first by apply: stepsRed.
  rewrite subst_lam subst_apps. apply: stepsLam. apply: steps_refl.
  congr (apps _ _). rewrite /= !subst_apps /= !ren_M.
  move=> [: H]. congr ([_; _; _; _; _]).
  - by rewrite map_app map_repeat.
  - rewrite map_app map_repeat /= !subst_closed; auto with allfv.
  - rewrite map_app. congr (apps _ _). congr (_ ++ _).
    + abstract: H.
      rewrite map_rev map_map. congr rev. apply: map_ext_Forall.
      apply: Forall_impl (wf_rules)=> ??.
      rewrite subst_closed; auto with allfv.
    + by rewrite /= !subst_closed; auto with allfv.
  - rewrite map_app H. by rewrite /= !subst_closed; auto with allfv.
  - rewrite map_app H. by rewrite /= !subst_closed; auto with allfv.
Qed.

Lemma eq_beta_normal_form_elim (P : Prop) M M' N : normal_form N -> steps M M' -> (steps M' N -> P) -> clos_refl_sym_trans term step M N -> P.
Proof.
  move=> HN HMM' + /clos_rst_rst1n_iff HMN. apply.
  elim: HMN M' HN HMM'.
  - move=> > /normal_form_steps /[apply] ->. by apply: rt_refl.
  - move=> > [].
    + move=> + _ IH ? /IH {}IH.
      move=> /(@rt_step term) /confluence_step /[apply] - [?] [/IH] *.
      apply: rt_trans; by eassumption.
    + move=> + _ IH ? /IH {}IH.
      move=> /(@rt_step term) *. apply: IH.
      apply: rt_trans; by eassumption.
Qed.

End Argument.

Require Import Undecidability.Synthetic.Definitions.
Import SSTS (SSTS01).

(* Reduction from: Simple semi-Thue system 01 rewriting (SSTS01)
   to: Higher-Order Matching wrt. beta-equivalence (HOMbeta) *)
Theorem reduction : SSTS01 ⪯ HOMbeta.
Proof.
  exists @HOM_inst. split.
  - move=> /correctness [M] [H1M] [H2M] [H3M] [H4M] [H5M] H6M.
    exists M. split; first done.
    apply: clos_rt_clos_rst.
    apply: rt_trans; first by apply: steps_HOM_f.
    rewrite /HOM_b. apply: stepsLam. apply: stepsAppsR.
    constructor; [|constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]]]; [|done..].
    by apply: stepsLam.
  - move=> [M] [H1M H2M]. apply /correctness.
    exists M. split; first done.
    apply: eq_beta_normal_form_elim H2M.
    + by apply: nf_HOM_b.
    + by apply: steps_HOM_f.
    + rewrite /HOM_b. move=> /steps_lamE /steps_apps_varE.
      move=> /Forall2_cons_iff [/steps_lamE ?].
      do 4 (move=> /Forall2_cons_iff [?]). tauto.
Qed.
