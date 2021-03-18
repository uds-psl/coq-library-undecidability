Require Import Undecidability.Synthetic.Definitions Undecidability.Synthetic.Undecidability.
From Undecidability.FOL.Util Require Import Syntax Syntax_facts FullTarski FullTarski_facts FullDeduction_facts FullDeduction FA_facts.
Require Import Undecidability.FOL.PA.
From Undecidability.H10 Require Import H10p.
Require Import List Lia.


Fixpoint embed_poly p : term :=
    match p with
    | dp_nat_pfree n => num n
    | dp_var_pfree k => $k
    | dp_comp_pfree do_add_pfree a b => (embed_poly a) ⊕ (embed_poly b)
    | dp_comp_pfree do_mul_pfree a b => (embed_poly a) ⊗ (embed_poly b)
    end.

  
(* We translate h10 problems to formulas in PA *)
Definition embed_problem (E : H10p_PROBLEM) : form :=
  let (a, b) := E in embed_poly a == embed_poly b.

Definition H10p_sem E sigma := dp_eval_pfree sigma (fst E) = dp_eval_pfree sigma (snd E).


Definition poly_bound p := proj1_sig (find_bounded_t (embed_poly p)).
Definition problem_bound (E : H10p_PROBLEM) :=
  let (a, b) := E in proj1_sig (find_bounded (embed_poly a == embed_poly b) ).

Definition embed E := exist_times (problem_bound E) (embed_problem E).


Lemma embed_is_closed E : bounded 0 (embed E).
Proof.
  unfold embed. rewrite exists_close_form.
  unfold problem_bound. destruct E as [a b]; cbn.
  apply (proj2_sig (find_bounded _)).
Qed.



Fact numeral_subst_invariance n rho : subst_term rho (num n) = num n.
Proof.
  induction n.
  - reflexivity.
  - cbn. now rewrite IHn.
Qed.

Lemma prv_poly sigma q Gamma :
  incl FAeq Gamma -> Gamma ⊢I ( (embed_poly q)`[sigma >> num] == num (dp_eval_pfree sigma q) ).
Proof.
  intros H.
  induction q; cbn.
  - change ((num n)`[sigma >> num]) with (subst_term (sigma >> num) (num n)).
    rewrite numeral_subst_invariance.
    now apply reflexivity.
  - now apply reflexivity.
  - destruct d; cbn.
    + eapply transitivity. assumption.
      apply (eq_add _ _ H IHq1 IHq2).
      now apply num_add_homomorphism.
    + eapply transitivity. assumption.
      apply (eq_mult _ _ H IHq1 IHq2).
      now apply num_mult_homomorphism.
Qed.

Lemma problem_to_prv :
  forall E sigma, H10p_sem E sigma -> FAeq ⊢I (embed_problem E)[sigma >> num].
Proof.
  intros [a b] sigma HE. cbn -[FAeq].
  eapply transitivity; firstorder.
  apply prv_poly; firstorder.
  apply symmetry; firstorder.
  unfold H10p_sem in *. cbn in HE. rewrite HE.
  apply prv_poly; firstorder.
Qed.




Section FA_ext_Model.

  Context {D : Type}.
  Context {I : interp D}.

  Hypothesis ext_model : extensional I.
  Hypothesis FA_model : forall ax rho, In ax FA -> rho ⊨ ax.

  Notation "'iO'" := (i_func (f:=Zero) (Vector.nil D)) (at level 2) : PA_Notation.
  
  Fact eval_poly sigma p : eval (sigma >> iμ) (embed_poly p) = iμ (dp_eval_pfree sigma p).
    Proof.
      induction p; cbn.
      - now rewrite eval_num.
      - reflexivity.
      - destruct d; cbn.
        + now rewrite IHp1, IHp2, add_hom.
        + now rewrite IHp1, IHp2, mult_hom.
    Qed.

    Lemma problem_to_ext_model : forall E sigma, H10p_sem E sigma -> (sigma >> iμ) ⊨ embed_problem E.
    Proof.
      intros [a b] sigma Hs. cbn -[sat].
      unfold H10p_sem in *. cbn -[FA] in *.
      apply ext_model. rewrite !eval_poly. congruence.
    Qed.      
    
End FA_ext_Model.



Section FA_Model.

  (* Model of FA with equality. *)
  
  Context {D : Type}.
  Context {I : interp D}.

  Hypothesis FA_model : forall rho ax, In ax FAeq -> rho ⊨ ax.

  Notation "'iO'" := (i_func (f:=Zero) (Vector.nil D)) (at level 2) : PA_Notation.
  
  Lemma problem_to_model E sigma : H10p_sem E sigma -> (sigma >> iμ) ⊨ embed_problem E.
  Proof.
    intros HE%problem_to_prv%soundness.
    specialize (HE D I).
    setoid_rewrite sat_comp in HE.
    eapply sat_ext. 2: apply HE.
    intros x. unfold ">>". now rewrite eval_num.
    intros. instantiate (1 := (fun _ => iO)).
    now apply FA_model.
  Qed.

  
End FA_Model.



Fact nat_eval_poly (sigma : env nat) p :
  @eval _ _ _ interp_nat sigma (embed_poly p) = dp_eval_pfree sigma p.
Proof.
  induction p; cbn.
  - now rewrite nat_eval_num.
  - reflexivity.
  - destruct d; cbn.
    + now rewrite IHp1, IHp2.
    + now rewrite IHp1, IHp2.
Qed.


Lemma nat_sat :
  forall E rho, sat interp_nat rho (embed_problem E) <-> H10p_sem E rho.
Proof.
  intros E rho. split.
  - destruct E as [a b]. unfold H10p_sem. cbn.
    now rewrite !nat_eval_poly.
  - intros. eapply (@sat_ext _ _ _ _ _ (rho >> @iμ nat interp_nat)).
    intros x. change ((rho >> iμ) x) with (@iμ nat interp_nat (rho x)).
    induction (rho x). reflexivity. cbn. now rewrite IHn.
    eapply problem_to_model.
    apply nat_is_FA_model.
    assumption.
Qed.


Lemma nat_sat' E :
  (exists sigma, sat interp_nat sigma (embed_problem E)) <-> H10p E.
Proof.
  split; intros [sigma ]; exists sigma; now apply nat_sat.
Qed.


Theorem H10p_to_FA_ext_sat E :
  H10p E <-> ext_entailment_PA (embed E).
Proof.
  split.
  - intros [sigma HE].
    intros D I rho Hext H.
    eapply subst_exist_sat.
    apply problem_to_ext_model.
    + apply Hext.
    + intros. apply H. now constructor.
    + apply HE.
    + rewrite <-exists_close_form; apply embed_is_closed. 
  - intros H.
    specialize (H nat interp_nat id nat_extensional).
    unfold embed in *. apply subst_exist_sat2 in H.
    now apply nat_sat'.
    apply nat_is_PA_model.
Qed.


Theorem H10p_to_FA_sat E :
  H10p E <-> valid_ctx FAeq (embed E).
Proof.
  split.
  - intros [sigma HE].
    intros D I rho H.
    eapply subst_exist_sat.
    apply problem_to_model.
    + intros ρ' ax Hax. eapply sat_closed.
      2: now apply H.
      repeat (destruct Hax as [<- | Hax]; cbn; repeat solve_bounds; auto).
      inversion Hax.
    + apply HE.
    + rewrite <-exists_close_form; apply embed_is_closed.
  - intros H.
    specialize (H nat interp_nat id (nat_is_FA_model id)).
    unfold embed in *. apply subst_exist_sat2 in H.
    now apply nat_sat'.
Qed.


Theorem H10p_to_PA_sat E :
  H10p E <-> forall D (I : interp D) rho, (forall psi rho, PAeq psi -> rho ⊨ psi) -> rho ⊨ (embed E).
Proof.
  split.
  - intros [sigma HE].
    intros D I rho H.
    eapply subst_exist_sat.
    apply problem_to_model.
    + intros ρ' ax Hax. apply sat_closed with rho.
      repeat (destruct Hax as [<- | Hax]; cbn; repeat solve_bounds; auto).
      1:inversion Hax.
      apply H. now constructor.
    + apply HE.
    + rewrite <-exists_close_form; apply embed_is_closed.
  - intros H.
    specialize (H nat interp_nat id nat_is_PAeq_model).
    unfold embed in *. apply subst_exist_sat2 in H.
    now apply nat_sat'.
Qed.


Theorem H10p_to_FA_prv E :
  H10p E <-> FAeq ⊢I embed E.
Proof.
  split.
  - intros [sigma HE].
    eapply subst_exist_prv.
    apply problem_to_prv,  HE.
    rewrite <-exists_close_form; apply embed_is_closed.
  - intros H%soundness.
    now apply H10p_to_FA_sat.
Qed.


Theorem H10p_to_PA_prv E :
  H10p E <-> PAeq ⊢TI embed E.
Proof.
  split.
  - intros [sigma HE].
    exists FAeq. split. intros. now constructor.
    apply H10p_to_FA_prv.
    now exists sigma.
  - intros H. apply nat_sat'.
    eapply subst_exist_sat2.
    apply (tsoundness H interp_nat id).
    intros. now apply nat_is_PAeq_model.
Qed.


(* ** Reduction for the axiomatisation PA assuming extensionality of models. *)

Theorem H10_to_ext_entailment_PA :
  H10p ⪯ ext_entailment_PA.
Proof.
  exists embed. intros E. apply H10p_to_FA_ext_sat.
Qed.

(* ** Reductions for the axiomatisations PAeq and FAeq, which include the axioms for equatlity. *)

Theorem H10_to_entailment_FA :
  H10p ⪯ entailment_FA.
Proof.
  exists embed; intros E. apply H10p_to_FA_sat.
Qed.

Corollary H10_to_entailment_PA :
  H10p ⪯ entailment_PA.
Proof.
  exists embed; intros E. apply H10p_to_PA_sat.
Qed.

Theorem H10_to_deduction_FA :
  H10p ⪯ deduction_FA.
Proof.
  exists embed; intros E. apply H10p_to_FA_prv.
Qed.

Corollary H10_to_deduction_PA :
  H10p ⪯ deduction_PA.
Proof.
  exists embed; intros E. apply H10p_to_PA_prv.
Qed.
