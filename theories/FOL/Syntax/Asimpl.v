From Undecidability.FOL.Syntax Require Import Core Facts.

Section Asimpl.

#[local] Ltac print_goal := match goal with |- ?g => idtac g end.
#[local] Ltac try_solve_reflexivity := try reflexivity.
#[local] Ltac unfold_commons := repeat (unfold up, scons, funcomp).
#[local] Ltac check_id n max := let rec go nn mm := 
   match mm with 0 => try_solve_reflexivity; fail 
      | S ?mmm => let nnn := fresh "n" in (destruct nn as [|nnn]; 
        [try_solve_reflexivity;easy;fail
        |try_solve_reflexivity;cbn; go nnn mmm]) end in go n max.
#[local] Ltac try_id_subst phi sigma := try (erewrite (@subst_id _ _ _ _ phi sigma); [|let n := fresh "n" in check_id n 10]).
#[local] Ltac try_id_tsubst t sigma := try (erewrite (@subst_term_id _ t sigma); [|let n := fresh "n" in check_id n 10]).
#[local] Ltac do_subst_comp_goal := repeat match goal with | |- context ctx [?phi[?sigma][?tau]] => rewrite (@subst_comp _ _ _ _ phi sigma tau) end.
#[local] Ltac do_subst_comp_in H := repeat match type of H with context ctx [?phi[?sigma][?tau]] => rewrite (@subst_comp _ _ _ _ phi sigma tau) in H end.
#[local] Ltac do_tsubst_comp_goal := repeat match goal with | |- context ctx [?t`[?sigma]`[?tau]] => rewrite (@subst_term_comp _ t sigma tau) end.
#[local] Ltac do_tsubst_comp_in H := repeat match type of H with  context ctx [?t`[?sigma]`[?tau]] => rewrite (@subst_term_comp _ t sigma tau) in H end.
#[local] Ltac to_scons_form phi rho := erewrite (@subst_ext _ _ _ _ phi rho (ltac:(idtac) .: ltac:(idtac))).
#[local] Ltac to_scons_term t rho := erewrite (@subst_term_ext _ t rho (ltac:(idtac) .: ltac:(idtac))).
#[local] Ltac asimpl_term_goal_for tt rrho := 
  let rec go t rho := try_id_tsubst t rho || (to_scons_term t rho;
  [|let n := fresh "n" in intros [|n]; [cbn; try_solve_reflexivity; fail "could not find head!" | cbn; unfold_commons; do_tsubst_comp_goal;
  match goal with |- ?t2`[?rho2] => go t2 rho2 | _ => try_solve_reflexivity; fail "Could not close continuation!" end] ])
  in go tt rrho.
#[local] Ltac asimpl_form_goal_for phi rho := 
  try_id_subst phi rho || (to_scons_form phi rho;
  [|let n := fresh "n" in intros [|n]; [cbn; try_solve_reflexivity; fail "could not find head!" | cbn; unfold_commons; do_subst_comp_goal;
  match goal with |- ?t2`[?rho2] => print_goal; asimpl_term_goal_for t2 rho2 | _ => print_goal; try_solve_reflexivity; fail "Could not close continuation!" end] ]).
#[local] Ltac asimpl_term_goal :=  try_solve_reflexivity; unfold_commons; do_tsubst_comp_goal; unfold_commons;
                                   repeat match goal with | |- context ctx [?t`[?rho]] => progress (asimpl_term_goal_for t rho) end.
#[local] Ltac asimpl_form_goal :=  try_solve_reflexivity; unfold_commons; do_subst_comp_goal; unfold_commons;
                                   repeat match goal with | |- context ctx [?phi[?rho]] => progress (asimpl_form_goal_for phi rho) end.

Section Test.
  Context {Σf : funcs_signature} {Σp : preds_signature}.
  Context {ff : falsity_flag}.
  Import FragmentSyntax.

  Lemma up_shift_t phi t sigma :
    phi`[up ↑]`[t.:sigma] = phi`[t.:S>>sigma].
  Proof.
    asimpl_term_goal. reflexivity.
  Qed.

  Lemma up_shift phi t sigma :
    phi[up ↑][t.:sigma] = phi[t.:S>>sigma].
  Proof.
    asimpl_form_goal. reflexivity.
  Qed.

  Lemma help phi :
    phi[up ↑][up (up ↑)][up $0..] = phi[$0 .: S >> ↑].
  Proof.
    asimpl_form_goal. reflexivity.
  Qed.

  Lemma help2 phi :
    phi[$0.:↑] = phi.
  Proof.
    asimpl_form_goal. easy.
  Qed.
  
  Lemma help3 phi x :
    phi[up ↑][up $x..] = phi.
  Proof.
    asimpl_form_goal. easy.
  Qed.

  Lemma help4 phi :
    phi[up ↑][$0..] = phi.
  Proof.
    asimpl_form_goal. easy.
  Qed.

  Lemma help5 phi x :
    phi[up ↑][up $x..][up ↑][up $x..] = phi[up ↑][up $x..][up ↑][up $x..][up ↑][up $x..].
  Proof.
    asimpl_form_goal. easy.
  Qed.

  Lemma help6 phi :
    phi[up ↑][up (up ↑)][up $0..][up ↑][up (up ↑)][up $0..] = phi[$0 .: S >> S >> ↑].
  Proof.
    asimpl_form_goal. reflexivity.
  Qed.

  Lemma foo phi rho : (forall x, rho x = $(S x)) -> phi[$0 .: $0 .: rho] = phi[rho].
  Proof.
    intros H. asimpl_form_goal.
  Qed.
