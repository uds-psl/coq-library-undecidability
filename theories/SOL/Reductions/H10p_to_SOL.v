From Stdlib Require Import PeanoNat Lia Vector List.
From Undecidability.SOL Require Import SOL PA2.
From Undecidability.Shared.Libs.PSL Require Import Vectors.
From Undecidability.SOL.Util Require Import Syntax Subst Tarski PA2_facts PA2_categoricity.
From Undecidability.Synthetic Require Import Definitions DecidabilityFacts EnumerabilityFacts ListEnumerabilityFacts ReducibilityFacts.
From Undecidability.H10 Require Import H10p.
Require Import Undecidability.Shared.Dec.

Import ListNotations SOLNotations PA2Notations.

Fixpoint encode_number n := match n with 
  | 0 => zero 
  | S n => σ (encode_number n) 
end.

Fixpoint encode_polynomial p := match p with
  | dp_nat_pfree n => encode_number n
  | dp_var_pfree x => $x
  | dp_comp_pfree do_add_pfree p q => encode_polynomial p ⊕ encode_polynomial q
  | dp_comp_pfree do_mul_pfree p q => encode_polynomial p ⊗ encode_polynomial q
end.


Lemma find_largest_variable p :
  { n | bounded_indi_term n (encode_polynomial p) }.
Proof.
  induction p; cbn.
  - exists 0. now induction n.
  - exists (S n). lia.
  - destruct d; cbn.
    + destruct IHp1 as [n], IHp2 as [m]. destruct (Arith.Compare_dec.le_lt_dec n m).
      * exists m. repeat split. 2: easy.
        now apply (bounded_indi_term_up n m).
      * exists n. repeat split. easy. 
        apply (bounded_indi_term_up m n). lia. easy.
    + destruct IHp1 as [n], IHp2 as [m]. destruct (Arith.Compare_dec.le_lt_dec n m).
      * exists m. repeat split. 2: easy.
        now apply (bounded_indi_term_up n m).
      * exists n. repeat split. easy.
        apply (bounded_indi_term_up m n). lia. easy.
Qed.

Fixpoint exists_n n phi := match n with
  | 0 => phi
  | S n => ∃i exists_n n phi
end.

Definition encode_problem equation := match equation with
  | (p, q) => exists_n (max (proj1_sig (find_largest_variable p)) (proj1_sig (find_largest_variable q))) (encode_polynomial p == encode_polynomial q)
end.



(* Encoding is closed *)

Lemma exists_n_switch n phi :
  ∃i exists_n n phi = exists_n n (∃i phi).
Proof.
  induction n. easy. cbn. now rewrite IHn.
Qed.

Lemma exists_n_bounded n phi :
  bounded_indi 0 (exists_n n phi) <-> bounded_indi n phi.
Proof.
  induction n in phi |- *.
  - easy.
  - cbn [exists_n]. rewrite exists_n_switch. apply IHn.
Qed.

Lemma encoding_closed e :
  bounded_indi 0 (encode_problem e).
Proof.
  destruct e as [p q]; cbn.
  destruct (find_largest_variable p) as [n H1].
  destruct (find_largest_variable q) as [m H2].
  apply exists_n_bounded. cbn.
  destruct (Arith.Compare_dec.le_lt_dec n m).
  - assert (max n m = m) as -> by lia. repeat split. 2: easy.
    now apply (bounded_indi_term_up n m).
  - assert (max n m = n) as -> by lia. repeat split. easy.
    apply (bounded_indi_term_up m n). lia. easy.
Qed.


(* Encoding is first-order *)

Lemma polynomial_first_order p :
  first_order_term (encode_polynomial p).
Proof.
  induction p; try destruct d; try easy. now induction n.
Qed.

Lemma exists_n_first_order n phi :
  first_order phi -> first_order (exists_n n phi).
Proof.
  now induction n.
Qed.

Lemma encoding_first_order e :
  first_order (encode_problem e).
Proof.
  destruct e as [p q]; cbn.
  destruct (find_largest_variable p) as [n H1].
  destruct (find_largest_variable q) as [m H2].
  apply exists_n_first_order.
  repeat split; apply polynomial_first_order.
Qed.


(* Encoding is satisfiable iff the diophantine equation has
    a solution. *)

Lemma eval_encoding alpha rho p :
  @eval _ _ (M_domain Standard_Model) _ ⟨alpha, get_func rho, get_pred rho⟩ (encode_polynomial p) = dp_eval_pfree alpha p.
Proof.
  induction p; cbn.
  - induction n. reflexivity. cbn. now repeat f_equal.
  - reflexivity.
  - destruct d; cbn; now repeat f_equal.
Qed.

Lemma sat_encoding alpha rho p q :
  (Standard_Model, ⟨alpha, get_func rho, get_pred rho⟩) ⊨ (encode_polynomial p == encode_polynomial q) 
  <-> dp_eval_pfree alpha p = dp_eval_pfree alpha q.
Proof.
  split.
  - intros H%eq_sem. now repeat rewrite eval_encoding in H. apply std_model_correct.
  - intros. apply eq_sem. apply std_model_correct. now repeat rewrite eval_encoding.
Qed.

Section Model.
  Variable M : Model.

  Lemma exists_n_sat phi n :
    first_order phi -> bounded_indi n phi -> M ⊨ exists_n n phi <-> exists rho, (M, rho) ⊨ phi.
  Proof.
    intros FO B. split.
    - enough (forall rho, (M, rho) ⊨ (exists_n n phi) -> exists sigma, (M, sigma) ⊨ phi) as X.
      { intros H. apply (X (empty_PA2_env _)), H. }
      revert phi FO B. induction n; intros phi FO B rho H.
      + now exists rho.
      + cbn [exists_n] in H. rewrite exists_n_switch in H.
        destruct (IHn (∃i phi) FO B rho H) as [sigma [x H1]]. eexists. apply H1.
    - intros [rho H]. revert rho phi FO B H. induction n; intros rho phi FO B H sigma.
      + eapply sat_ext_closed_FO; try easy. apply H.
      + cbn [exists_n]. rewrite exists_n_switch. 
        apply (IHn ⟨fun n => get_indi rho (S n), get_func rho, get_pred rho⟩).
        apply FO. apply B. cbn. exists (get_indi rho 0).
        eapply sat_ext. 2: apply H. split. now induction n0. easy.
  Qed.

  Lemma exists_n_sat_1 rho phi n :
    (M, rho) ⊨ phi -> first_order phi -> bounded_indi n phi -> forall sigma, (M, sigma) ⊨ (exists_n n phi).
  Proof.
    intros. apply exists_n_sat; eauto.
  Qed.

  Lemma exists_n_sat_2 rho phi n :
    (M, rho) ⊨ (exists_n n phi) -> first_order phi -> bounded_indi n phi -> exists sigma, (M, sigma) ⊨ phi.
  Proof.
    intros. eapply exists_n_sat; eauto. intros sigma. eapply sat_ext_closed_FO.
    now apply exists_n_first_order. now apply exists_n_bounded. eassumption.
  Qed.
End Model.



(* ** Reductions *)

Lemma H10p_to_PA2_standard_model_sat e :
  H10p e <-> Standard_Model ⊨ encode_problem e.
Proof.
  split.
  - destruct e as [p q]; cbn; intros [alpha H]; hnf.
    eapply exists_n_sat_1.
    + now apply (sat_encoding alpha (empty_PA2_env _)).
    + repeat split; apply polynomial_first_order.
    + apply exists_n_bounded. apply (encoding_closed (p, q)).
  - destruct e as [p q]; unfold H10p; cbn. intros H.
    specialize (H (empty_PA2_env Standard_Model)).
    apply exists_n_sat_2 in H.
    + destruct H as [sigma H]. exists (get_indi sigma).
      apply (sat_encoding _ sigma). eapply sat_ext.
      2: apply H. easy.
    + repeat split; apply polynomial_first_order.
    + apply exists_n_bounded. apply (encoding_closed (p, q)).
Qed.

Lemma solution_from_PA2_model (M : Model) e :
  M ⊨ PA2 -> M ⊨ encode_problem e -> H10p e.
Proof.
  intros M_correct H. eapply H10p_to_PA2_standard_model_sat, PA2_models_agree_FO with (rho := empty_PA2_env _).
  apply encoding_first_order. apply encoding_closed. apply M_correct. apply H.
  apply std_model_correct.
Qed. 

Theorem H10p_to_PA2_model_sat e (M : Model) rho :
  M ⊨ PA2 -> (H10p e <-> (M, rho) ⊨ (encode_problem e)).
Proof.
  intros M_correct. split.
  - intros H. eapply PA2_models_agree_FO with (rho := empty_PA2_env _).
    apply encoding_first_order. apply encoding_closed.
    2: now apply H10p_to_PA2_standard_model_sat. apply std_model_correct. apply M_correct.
  - intros H. eapply H10p_to_PA2_standard_model_sat, PA2_models_agree_FO with (rho := rho).
    apply encoding_first_order. apply encoding_closed. 2: apply H.
    apply M_correct. apply std_model_correct.
Qed.

Theorem H10p_to_PA2_validity e :
  H10p e <-> PA2 ⊨ encode_problem e.
Proof.
  split.
  - intros H. apply PA2_valid_alternative. intros M HM rho. now apply H10p_to_PA2_model_sat.
  - intros H. eapply H10p_to_PA2_model_sat with (rho := empty_PA2_env Standard_Model). apply std_model_correct. eapply PA2_valid_alternative in H. 
    apply H. apply std_model_correct.
Qed.

Theorem H10p_to_PA2_satisfiability e :
  H10p e <-> exists M rho, (M, rho) ⊨ PA2 /\ (M, rho) ⊨ (encode_problem e).
Proof.
  split.
  - intros H. exists Standard_Model, (empty_PA2_env _). split.
    + intros phi H1. now apply std_model_correct.
    + now apply H10p_to_PA2_standard_model_sat.
  - intros [M [rho [H1 H2]]]. eapply H10p_to_PA2_model_sat with (M := M) (rho := empty_PA2_env _).
    + intros phi H rho'. eapply sat_ext_closed. 4: apply H1, H. all: apply PA2_closed, H.
    + eapply sat_ext_closed_FO. apply encoding_first_order. apply encoding_closed. apply H2.
Qed.

Theorem H10p_to_validity Σf Σp e :
  H10p e <-> forall (M : @Model Σf Σp) rho, (M, rho) ⊨ (∀f(0) ∀f(1) ∀f(2) ∀f(2) ∀p(2) (embed_form 0 0 0 0 (PA2_form ~> encode_problem e))).
Proof.
  split.
  - intros H M rho. apply PA2_model_valid_iff_model_valid. apply PA2_valid_alternative. 
    intros M' H1 rho'. now apply H10p_to_PA2_model_sat.
  - intros H. apply H10p_to_PA2_standard_model_sat. intros rho. 
    apply PA2_model_valid_iff_model_valid; trivial. intros phi H1. now apply std_model_correct.
Qed.

Theorem H10p_to_SOL_valid :
  H10p ⪯ SOL_valid.
Proof.
  exists (fun e => ∀f(0) ∀f(1) ∀f(2) ∀f(2) ∀p(2) (embed_form 0 0 0 0 (PA2_form ~> encode_problem e))).
  intros e. apply H10p_to_validity.
Qed.

Theorem H10p_to_satisfiability Σf Σp e :
  H10p e <-> exists (M : @Model Σf Σp) rho, (M, rho) ⊨ (∃f(0) ∃f(1) ∃f(2) ∃f(2) ∃p(2) (embed_form 0 0 0 0 (PA2_form ∧ encode_problem e))).
Proof.
  split.
  - intros H. apply PA2_model_sat_iff_model_sat. exists Standard_Model, (empty_PA2_env _).
    split. intros ? ?. now apply std_model_correct. now apply H10p_to_PA2_standard_model_sat.
  - intros [M [rho H]]. edestruct PA2_model_sat_iff_model_sat as [_ H1].
    destruct H1 as [M' [rho' [H1 H2]]]. exists M, rho. apply H.
    eapply H10p_to_PA2_model_sat with (M := M') (rho := rho').
    + intros phi H3 rho''. eapply sat_ext_closed. 4: apply H1, H3. all: apply PA2_closed, H3.
    + eapply sat_ext_closed_FO. apply encoding_first_order. apply encoding_closed. apply H2.
Qed.

Theorem H10p_to_SOL_satis :
  H10p ⪯ SOL_satis.
Proof.
  exists (fun e => (∃f(0) ∃f(1) ∃f(2) ∃f(2) ∃p(2) (embed_form 0 0 0 0 (PA2_form ∧ encode_problem e)))).
  intros e. unfold SOL_satis. apply H10p_to_satisfiability.
Qed.
