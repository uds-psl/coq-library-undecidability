From Undecidability.FOL.Util Require Import Syntax Syntax_facts FullTarski FullDeduction_facts FullDeduction FA_facts.
Require Import Undecidability.FOL.PA.
From Undecidability.H10 Require Import H10p.



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


(* Lemma prv_poly sigma q Gamma : *)
(*   FA <<= Gamma -> Gamma ⊢I ( (embed_poly q)[sigma >> num] == num (dp_eval sigma q) ). *)
(* Proof. *)
(*   intros H. *)
(*   induction q; cbn. *)
(*   - change ((num n)[sigma >> num]) with (subst_term (sigma >> num) (num n)). *)
(*     rewrite numeral_subst_invariance. *)
(*     now apply reflexivity. *)
(*   - now apply reflexivity. *)
(*   - destruct d; cbn. *)
(*     + eapply transitivity. assumption. *)
(*       apply (eq_add _ _ H IHq1 IHq2). *)
(*       now apply num_add_homomorphism. *)
(*     + eapply transitivity. assumption. *)
(*       apply (eq_mult _ _ H IHq1 IHq2). *)
(*       now apply num_mult_homomorphism. *)
(* Qed. *)
