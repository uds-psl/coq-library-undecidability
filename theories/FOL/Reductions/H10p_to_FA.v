From Undecidability.FOL.Util Require Import Syntax Syntax_facts FullTarski FullDeduction_facts FullDeduction FA_facts.
Require Import Undecidability.FOL.PA.
From Undecidability.H10 Require Import H10p.
Require Import List.


Fixpoint embed_poly p : term :=
    match p with
    | dp_nat_pfree n => num n
    | dp_var_pfree k => $k
    | dp_comp_pfree do_add_pfree a b => (embed_poly a) ⊕ (embed_poly b)
    | dp_comp_pfree do_mul_pfree a b => (embed_poly a) ⊗ (embed_poly b)
    end.

  
(* We translate h10 problems to formulas in PA *)
Definition embed_problem (E : H10p_PROBLEM) : form := let (a, b) := E in
                                                      embed_poly a == embed_poly b.

Definition H10p_sem E sigma := dp_eval_pfree sigma (fst E) = dp_eval_pfree sigma (snd E).


Definition poly_bound p := proj1_sig (find_bounded_t (embed_poly p)).
Definition problem_bound (E : H10p_PROBLEM) := let (a, b) := E in
                                               proj1_sig (find_bounded (embed_poly a == embed_poly b) ).


Fixpoint iter {X: Type} f n (x : X) :=
  match n with
    0 => x
  | S m => f (iter f m x)
  end.

Fact iter_switch {X} f n x : f (@iter X f n x) = iter f n (f x).
Proof. induction n; cbn; now try rewrite IHn. Qed.


Definition exist_times n (phi : form) := iter (fun psi => ∃ psi) n phi.
Definition forall_times n (phi : form) := iter (fun psi => ∀ psi) n phi.


Definition embed E := exist_times (problem_bound E) (embed_problem E).


Lemma exists_close_form N phi : bounded 0 (exist_times N phi) <-> bounded N phi.
Proof.
  induction N in phi |- *.
  - reflexivity.
  - cbn. rewrite iter_switch.
    change (iter _ _ _) with (exist_times N (∃ phi)).
    setoid_rewrite IHN.
Admitted.


Lemma embed_is_closed E : bounded 0 (embed E).
Proof.
  unfold embed. rewrite exists_close_form.
  unfold problem_bound. destruct E as [a b]; cbn.
  apply (proj2_sig (find_bounded _)).
Qed.


Lemma prv_poly sigma q Gamma :
  incl FA_facts.FA Gamma -> Gamma ⊢I ( (embed_poly q)`[sigma >> num] == num (dp_eval_pfree sigma q) ).
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
  forall E sigma, H10p_sem E sigma -> FA_facts.FA ⊢I (embed_problem E)[sigma >> num].
Proof.
  intros [a b] sigma HE. cbn -[FA].
  eapply transitivity; firstorder.
  apply prv_poly; firstorder.
  apply symmetry; firstorder.
  unfold H10p_sem in *. cbn in HE. rewrite HE.
  apply prv_poly; firstorder.
Qed.



  Section FA_Model.

    Context {D : Type}.
    Context {I : interp D}.

    Hypothesis ext_model : extensional I.
    Hypothesis FA_model : forall rho ax, In ax FA -> rho ⊨ ax.
    

    Fact eval_num sigma n : eval sigma (num n) = iμ n.
    Proof.
      induction n.
      - reflexivity.
      - cbn. now rewrite IHn.
    Qed.
    
    Lemma problem_to_model E sigma : H10_sem E sigma -> (sigma >> iμ) ⊨ embed_problem E.
    Proof.
      intros HE%problem_to_prv%Soundness.
      specialize (HE D I).
      setoid_rewrite sat_comp in HE.
      eapply sat_ext. 2: apply HE.
      intros x. unfold ">>". now rewrite eval_num.
      intros. instantiate (1 := (fun _ => iO)). now apply sat_FA.  
    Qed.
    
    
  End FA_Model.




Theorem Reduction_sat :
  forall E, H10p_SAT E <-> valid_ctx FA_facts.FA (embed E).
Proof.
  split.
  - intros [sigma HE].
    intros D I rho H.
    eapply subst_exist_sat.
    apply problem_to_model.
    + intros ρ' ax Hax. eapply sat_closed.
      2: now apply H.
      repeat (destruct Hax as [<- | Hax]; auto).
    + apply HE.
    + rewrite <-exists_close_form; apply embed_is_closed.
  - intros H.
    specialize (H nat interp_nat id (nat_is_FA_model id)).
    unfold embed in *. apply subst_exist_sat2 in H.
    destruct H as [sigma Hs]. exists sigma.
    now apply nat_sat.
Qed.



Theorem Reduction_prv : forall E, H10p_SAT E <-> FA_facts.FA ⊢I embed E.
Proof.
  intros E. split.
  - intros [sigma HE].
    eapply subst_exist_prv.
    apply problem_to_prv,  HE.
    rewrite <-exists_close_form; apply embed_is_closed.
  - intros H%soundness.
    (* now apply Reduction_sat. *)
Admitted.



