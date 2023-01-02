From Undecidability.FOL Require Import FullSyntax.
From Undecidability.FOL.Arithmetics Require Import Signature PA DeductionFacts.
From Undecidability.FOL.Syntax Require Import Theories.
From Undecidability.Shared Require Import ListAutomation.
From Undecidability.FOL.Tennenbaum Require Import NumberUtils Formulas SyntheticInType Peano CantorPairing.

(* Require Import FOL Peano Tarski Deduction CantorPairing NumberTheory Synthetic Formulas DecidabilityFacts Church. *)
Require Import Lia.
From Equations Require Import Equations.

Import Vector.VectorNotations.
  

Notation "x 'el' A" := (List.In x A) (at level 70).
Notation "A '<<=' B" := (List.incl A B) (at level 70).
Notation "x ∣ y" := (exists k, x * k = y) (at level 50).

Definition unary alpha := bounded 1 alpha.
Definition binary alpha := bounded 2 alpha.


Section Model.

  Variable D : Type.
  Variable I : interp D.
  Local Definition I' : interp D := extensional_model I.
  Existing Instance I | 100.
  Existing Instance I' | 0.
  Notation "⊨ phi" := (forall rho, rho ⊨ phi) (at level 21).
  Variable axioms : forall ax, PAeq ax -> ⊨ ax.

  Notation "N⊨ phi" := (forall rho, @sat _ _ nat (extensional_model interp_nat) _ rho phi) (at level 40).


  Notation "x 'i=' y"  := (@i_atom PA_funcs_signature PA_preds_signature D I Eq ([x ; y])) (at level 80).
  Notation "'iσ' x" := (@i_func PA_funcs_signature PA_preds_signature D I Succ ([x])) (at level 60).
  Notation "x 'i⊕' y" := (@i_func PA_funcs_signature PA_preds_signature D I Plus ([x ; y])) (at level 62).
  Notation "x 'i⊗' y" := (@i_func PA_funcs_signature PA_preds_signature D I Mult ([x ; y])) (at level 61).
  Notation "'i0'" := (i_func (Σ_funcs:=PA_funcs_signature) (f:=Zero) []) (at level 2) : PA_Notation.
  Notation "x 'i⧀' y" := (exists d : D, y = iσ (x i⊕ d) ) (at level 80).
  Notation inu := (@inu D I).

Section Facts.


(*  We show some facts about standard numbers. Namely:
    - If x + y is standard, then so are x and y.
    - If x * y =/= 0 is standard, then so are x and y.
    - The embedding of nat into a PA model preserves the
      order on natural numbers.
    - A non-standard number is bigger than any natural number.   
 *)


Lemma std_add x y : 
  std (x i⊕ y) -> std x /\ std y.
Proof.
  intros [n Hn].
  revert Hn.  revert x y.
  induction n.
  - intros ?? H. symmetry in H. apply sum_is_zero in H as [-> ->].
    split; exists 0; auto. apply axioms. 
  - intros. destruct (@zero_or_succ D I axioms x) as [-> | [e ->]].
    + rewrite add_zero in Hn. rewrite <-Hn. split.
      exists 0; auto. exists (S n); auto. apply axioms.
    + cbn in *. rewrite add_rec in Hn. apply succ_inj in Hn.
      assert (std e /\ std y) as []. now apply IHn.
      split; auto.
      destruct H as [k <-]. exists (S k); auto.
      all: apply axioms.
Qed.

Lemma std_mult x y m : 
  (iσ x) i⊗ y = inu m -> std y.
Proof.
  cbn. rewrite mult_rec. intros E.
  assert (std (y i⊕ x i⊗ y)) as H%std_add.
  exists m; auto. tauto.
  apply axioms.
Qed.


Lemma std_mult' x y m : 
  x i⊗ y = inu (S m) -> std x /\ std y.
Proof.
  destruct (@zero_or_succ D I axioms x) as [-> | [e ->]],
    (@zero_or_succ D I axioms y) as [-> | [d ->]].
  + intros _. split; now exists 0.
  + rewrite mult_zero; auto.
    intros []%zero_succ; auto.
  + rewrite mult_zero_r; auto. 
    intros []%zero_succ; auto.
  + intros E. split.
    * eapply std_mult. 
      rewrite mult_comm; auto.
      apply E.  
    * eapply std_mult, E.
Qed.



Lemma lt_equiv x y : 
  x < y <-> inu x i⧀ inu y.
Proof.
  assert (x < y <-> exists k, S x + k = y) as H.
  split.
  - induction y in x |-*; [lia|].
    destruct x; intros; [exists y; lia|].
    destruct (IHy x) as [k <-]; [lia|].
    exists k; lia.
  - intros []. lia.
  - split.
    + intros [k <-]%H. exists (inu k); cbn.
      now rewrite inu_add_hom.
    + intros [k Hk].
      assert (std (inu (S x) i⊕ k)) as [_ [l Hl]]%std_add.
      * exists y. cbn. now rewrite add_rec.
      * rewrite <-Hl in *.
        apply H. exists l.
        rewrite <-inu_inj, inu_add_hom; cbn;
        [now rewrite add_rec, Hk | apply axioms | apply axioms].
Qed.

Lemma num_lt_nonStd n d : 
  ~ std d -> inu n i⧀ d.
Proof.
  intros nonStd.
  destruct (@trichotomy D I axioms (inu n) d) as [H|[<-|H]]; auto.
  all : contradiction nonStd.
  - exists n; auto.
  - apply lessthen_num in H. 
    destruct H as [k [? ->]].
    exists k; auto.
    apply axioms.
Qed.

End Facts.



(*  The following Lemma shows that if there is a formula which
    is satisfied only by the standard elements of a PA model,
    then the model is already the standard model.
 *)

Lemma stdModel_equiv :
  @stdModel D I <-> exists phi, unary phi /\ (forall e, std e <-> forall ρ, (e .: ρ) ⊨ phi).
Proof.
  split.
  - intros H.
    pose (phi := $0 == $0).
    exists phi. split.
    1: unfold unary; repeat solve_bounds.
    intros e; split; intros ?; [reflexivity|apply H].
  - intros [phi Hphi] e.
    apply Hphi, induction. 
    + apply axioms.
    + apply Hphi.
    + apply Hphi. exists 0. reflexivity.
    + intros d [x <-]%Hphi. apply Hphi.
      exists (S x). reflexivity.
Qed.

(** * Overspill *)

(*  From the above we can conclude that if the model is not standard 
    and a formula is satisfied for every standard element, then it cannot 
    only be satisfied on standard elements. 

    Given further assumptions, this can even gives us the existence of a
    non-standard element.
 *)

Section Overspill.

  Variable alpha : form.
  Hypothesis Halpha : unary alpha.

  Variable nStd : ~ stdModel D.

  Corollary Overspill :
    (forall e, std e -> (forall rho, (e.:rho) ⊨ alpha) ) -> ~ (forall e, (forall rho, (e.:rho) ⊨ alpha) -> std e ).
  Proof.
    intros ??. apply nStd, stdModel_equiv. exists alpha. split.
    - apply Halpha.
    - split; auto.
  Qed.
  
  
  Lemma Overspill_DN' :
    (forall x, stable (std x)) ->
    (forall e, std e -> (forall rho, (e.:rho) ⊨ alpha) ) ->  ~ ~ exists e, ~ std e /\ (forall rho, (e.:rho) ⊨ alpha).
  Proof.
    intros stable_std H1 H2. apply Overspill in H1. apply H1. intros e.
    intros H. apply stable_std. intros He. apply H2. now exists e.
  Qed.


  Lemma on_std_equiv :
    (forall n rho, ((inu n).:rho) ⊨ alpha) <-> (forall e, std e -> (forall rho, (e.:rho) ⊨ alpha)).
  Proof.
    split; intros H.
    - intros e [n <-]. apply H.
    - intros n. apply H. exists n; reflexivity.
  Qed.

  Lemma Overspill_DN :
    (forall x, stable (std x)) ->
    (forall n rho, ((inu n).:rho) ⊨ alpha) ->  ~ ~ exists e, ~ std e /\ (forall rho, (e.:rho) ⊨ alpha).
  Proof.
    intros dne.
    setoid_rewrite on_std_equiv.
    now apply Overspill_DN'.
  Qed.


  Lemma Overspill_DNE :
    DNE ->
    (forall n rho, ((inu n).:rho) ⊨ alpha) ->  exists e, ~ std e /\ (forall rho, (e.:rho) ⊨ alpha).
  Proof.
    intros dne H.
    now apply dne, Overspill_DN.
  Qed.


End Overspill.

(** * Coding Lemmas *)



Section Coding.

  (*  We assume that we have a formula ψ representing an injective function 
      which only produces prime numbers.
   *)
  Variable ψ : form.
  Variable Hψ : binary ψ /\ (forall x, Q ⊢I ∀ ψ[up (num x)..] ↔ $0 == num (Irred x) ).


  Definition div e d := exists k : D, e i⊗ k = d.
  Definition div_num n (d : D) := exists e, inu n i⊗ e = d.
  Definition Div_nat (d : D) := fun n => div_num n d.
  Definition div_pi n a :=  (inu n .: (fun _ => a)) ⊨ (∃ (ψ ∧ ∃ $1 ⊗ $0 == $3)).

  Lemma sat_Qeq ax : (ax el Qeq -> ⊨ ax).
  Proof using axioms. cbn.
    intros [<- |[<- |[<- |[<- |[<- |[<- |[<- |[<- |[<- |[<- |[<- |[<- |[<- |[]]]]]]]]]]]]]].
    1-10: apply axioms; apply PAeq_FA; cbn; eauto 15; fail.
    - apply axioms. apply PAeq_discr.
    - apply axioms. apply PAeq_inj.
    - apply axioms. apply PAeq_induction.
  Qed.
  
  Lemma ψ_repr x d rho : 
    (d .: inu x .: rho) ⊨ ψ <-> d = inu (Irred x).
  Proof.
    destruct Hψ as (_ & H).
    specialize (H x).
    apply soundness in H.
    specialize (H D I'). cbn -[Q] in H.
    setoid_rewrite eval_num in H.
    rewrite <-(@switch_up_num D I).
    apply H.
    intros ax Hax. apply sat_Qeq. easy.
  Qed.


  Lemma ψ_equiv n a : div_pi n a <-> div_num (Irred n) a.
  Proof.
    unfold div_pi. cbn. split.
    - intros [d [->%ψ_repr H]]. apply H.
    - intros. exists (inu (Irred n)). rewrite ψ_repr. now split.
  Qed.


  (** In the standard model, up to some bound. *)
  (*  This shows that we can potentially get a code representing any
      predicate on natural numbers up to some bound.
   *)
  Lemma Coding_nat A n :
    ~ ~ exists c, forall u, (u < n -> A u <-> Mod (Irred u) c = 0) /\ (Mod (Irred u) c = 0 -> u < n).
  Proof.
    induction n.
    - apply DN. exists 1. intros u. split. lia.
      intros [k ]%Mod_divides.
      assert (Irred u > 1). apply irred_Irred.
      destruct k; lia.
    - assert (~ ~ (A n \/ ~ A n)) as Dec_An by tauto.
      apply (DN_chaining Dec_An), (DN_chaining IHn), DN.
      clear IHn Dec_An.
      intros [a Ha] [A_n | NA_n].
      + exists (a * Irred n). intros u.
        assert (u < S n <-> u < n \/ u = n) as -> by lia.
        split.
        ++ intros [| ->]. split.
           +++ intros A_u%Ha.
               rewrite Mod_mult_hom, A_u.
               now rewrite Mod0_is_0.
               apply H.
           +++ intros [|H']%irred_integral_domain.
               apply Ha; assumption.
               apply irred_Mod_eq, inj_Irred in H'. lia. 
               all: apply irred_Irred.
           +++ intuition. apply Mod_divides. 
               now exists a.
        ++ intros [H |H]%irred_integral_domain.
           apply Ha in H. auto.
           apply irred_Mod_eq, inj_Irred in H. lia. 
           all: apply irred_Irred.
      + exists a. intros u.
        assert (u < S n <-> u < n \/ u = n) as -> by lia.
        split.
        ++ intros Hu. destruct Hu as [| ->]. 
           now apply Ha.
           split. now intros ?%NA_n.
           intros H%Ha. lia.
        ++ intros H%Ha. tauto.
  Qed.

  (*  The same as above, but if the predicate is definite, we get not only
      potential existence of a code, but actual existence.
   *)
  Lemma Coding_nat_Definite A n :
    Definite A -> exists c, forall u, (u < n -> A u <-> Mod (Irred u) c = 0) /\ (Mod (Irred u) c = 0 -> u < n).
  Proof.
    intros Def_A.
    induction n.
    - exists 1. intros u. split. lia.
      intros [k ]%Mod_divides.
      assert (Irred u > 1). apply irred_Irred.
      destruct k; lia.
    - destruct IHn as [a Ha], (Def_A n) as [A_n | NA_n].
      + exists (a * Irred n). intros u.
        assert (u < S n <-> u < n \/ u = n) as -> by lia.
        split.
        ++ intros [| ->]. split.
           +++ intros A_u%Ha.
               rewrite Mod_mult_hom, A_u.
               now rewrite Mod0_is_0.
               apply H.
           +++ intros [|H']%irred_integral_domain.
               apply Ha; assumption.
               apply irred_Mod_eq, inj_Irred in H'. lia. 
               all: apply irred_Irred.
           +++ intuition. apply Mod_divides. 
               now exists a.
        ++ intros [H |H]%irred_integral_domain.
           apply Ha in H. auto.
           apply irred_Mod_eq, inj_Irred in H. lia. 
           all: apply irred_Irred.
      + exists a. intros u.
        assert (u < S n <-> u < n \/ u = n) as -> by lia.
        split.
        ++ intros Hu. destruct Hu as [| ->]. 
           now apply Ha.
           split. now intros ?%NA_n.
           intros H%Ha. lia.
        ++ intros H%Ha. tauto.
  Qed.


  Lemma Divides_num x y : 
    div_num x (inu y) <-> Mod x y = 0.
  Proof.
    split.
    - intros [k Hk]. destruct x.
      + cbn in Hk. rewrite mult_zero in Hk.
        change i0 with (inu 0) in Hk.
        cbn. now apply inu_inj in Hk.
        apply axioms.
      + cbn in *. destruct (std_mult Hk) as [l <-]. unfold I' in Hk. rewrite <- inu_I in Hk.
        apply Mod_divides. exists l.
        change (iσ inu x) with (inu (S x)) in Hk.
        rewrite <-inu_mult_hom, inu_inj in Hk. lia.
        all: apply axioms.
    - intros [k Hk]%Mod_divides.
      exists (inu k).
      rewrite <-inu_mult_hom, inu_inj. lia.
      all: apply axioms.
  Qed.

  (** In an arbitrary model, up to some bound. *)
  (*  By using the coding lemma for natural numbers, we can now
      similarly verify that formulas can be coded in arbitrary 
      models of PA. Here, we show this for unary and binary formulas.
   *)
  Lemma Coding_model_unary alpha : 
    unary alpha -> 
    forall n rho, rho ⊨ ¬ ¬ ∃ ∀ $0 ⧀ (num n) → alpha ↔ ∃ (ψ ∧ ∃ $1 ⊗ $0 == $3).
  Proof.
    intros unary_alpha n rho. cbn.
    apply (@DN_chaining _ _ (@Coding_nat (fun (n:nat) => forall rho, rho ⊨ alpha[(num n)..] ) n)). apply DN.
    intros [a Ha].
    exists (inu a).
    intros u' Hu. cbn in Hu.
    rewrite num_subst in Hu.
    setoid_rewrite eval_num in Hu.
    apply lessthen_num in Hu. 2: apply axioms.
    destruct Hu as [u [Hu ->]]. split.
    + intros alpha_u.
      exists (inu (Irred u)).
      split; [now apply ψ_repr| ].
      apply Divides_num.
      apply Ha; [apply Hu|].
      intros ?. pose (@switch_num D I) as switch_num. cbn in switch_num. rewrite switch_num.
      eapply bound_ext; [apply unary_alpha| |apply alpha_u].
      intros []; try lia; reflexivity.
    + intros [d [->%ψ_repr H]].
      eapply Divides_num, (proj1 (Ha u)) in H; auto.
      pose (@switch_num D I) as switch_num. cbn in switch_num. rewrite <- switch_num.
      apply H.
  Qed.


  Lemma Coding_model_binary alpha : 
    binary alpha -> 
    forall n rho, rho ⊨ ∀ ¬ ¬ ∃ ∀ $0 ⧀ (num n) → alpha[up $1..] ↔ ∃ (ψ ∧ ∃ $1 ⊗ $0 == $3).
  Proof.
    intros binary_alpha n rho b. cbn.
    apply (@DN_chaining _ _ (@Coding_nat (fun n => forall rho, (b .: rho) ⊨ alpha[(num n)..] ) n)), DN.
    intros [a Ha].
    exists (inu a).
    intros u' Hu. cbn in Hu.
    rewrite num_subst in Hu.
    setoid_rewrite eval_num in Hu.
    apply lessthen_num in Hu. 2: apply axioms.
    destruct Hu as [u [Hu ->]]. split.
    + intros alpha_u.
      exists (inu (Irred u)).
      split; [now apply ψ_repr| ].
      apply Divides_num.
      apply Ha; [apply Hu|].
      intros ?. pose (@switch_num D I) as switch_num. cbn in switch_num. rewrite switch_num.
      rewrite sat_comp in alpha_u.
      eapply bound_ext. eauto.
      2 : apply alpha_u.
      intros [|[]]; now cbn; try lia.
    + intros [d [->%ψ_repr H]].
      eapply Divides_num, (proj1 (Ha u)) in H; auto.
      pose (@switch_num D I) as switch_num. cbn in switch_num. rewrite switch_num in H. rewrite sat_comp.
      eapply bound_ext. eauto.
      2 : apply H.
      intros [|[]]; now cbn; try lia.
    Unshelve. intros _. exact i0.
  Qed.

  (*  We specialize the above results for the case where the formulas 
      are definite. It is then possible to get rid of the double negations.
   *)
  Lemma Coding_model_binary_Definite alpha : 
    binary alpha -> (forall b u, definite (forall rho, (inu u .: b .: rho) ⊨ alpha )) ->
    forall n rho, rho ⊨ ∀ ∃ ∀ $0 ⧀ (num n) → alpha[up $1..] ↔ ∃ (ψ ∧ ∃ $1 ⊗ $0 == $3).
  Proof.
    intros binary_alpha Def_alpha n rho b.
    refine (
      let Ha := @Coding_nat_Definite (fun u => forall rho, (b .: rho) ⊨ alpha[(num u)..] ) n _ 
      in _).
    destruct Ha as [a Ha].
    exists (inu a).
    intros u' Hu. cbn in Hu.
    rewrite num_subst in Hu.
    setoid_rewrite eval_num in Hu.
    apply lessthen_num in Hu. 2: apply axioms.
    destruct Hu as [u [Hu ->]]. split.
    + intros alpha_u.
      exists (inu (Irred u)).
      split; [now apply ψ_repr| ].
      apply Divides_num.
      apply Ha; [apply Hu|].
      intros ?. pose (@switch_num D I) as switch_num. cbn in switch_num. rewrite switch_num.
      rewrite sat_comp in alpha_u.
      eapply bound_ext. eauto.
      2 : apply alpha_u.
      intros [|[]]; now cbn; try lia.
    + intros [d [->%ψ_repr H]].
      eapply Divides_num, (proj1 (Ha u)) in H; auto.
      pose (@switch_num D I) as switch_num. cbn in switch_num. rewrite switch_num in H. rewrite sat_comp.
      eapply bound_ext. eauto.
      2 : apply H.
      intros [|[]]; now cbn; try lia.
    Unshelve.
    - intros u. destruct (Def_alpha b u) as [h|h].
      * left. now setoid_rewrite switch_num.
      * right. now setoid_rewrite switch_num.
    - intros _. exact i0.
  Qed.




Section notStd.

  (** In a non-standard model. *)

  (*  Above we have established coding results for arbitrary PA models.
      We will now focus on the special case where the model is not standard.
      Using Overspill we can eliminate the bound on the coding; in a non-standard
      model, we can find elements which code the entirety of a predicate.
   *)

  Variable notStd : ~ stdModel D.
  Variable stable_std : forall x, stable (std x).

  Theorem Coding_nonStd_unary alpha : 
    unary alpha -> ~ ~ exists c, forall u rho, (inu u .: c .: rho) ⊨ (alpha ↔ ∃ (ψ ∧ ∃ $1 ⊗ $0 == $3)).
  Proof.
    intros unary_alpha.
    specialize (@Coding_model_unary _ unary_alpha) as H.
    assert (forall n rho, (inu n .: rho) ⊨ ¬ ¬ ∃ ∀ $0 ⧀ $2 → alpha ↔ ∃ (ψ ∧ ∃ $1 ⊗ $0 == $3) ) as H'.
    intros n rho. pose (@switch_num D I) as switch_num. cbn in switch_num.
    rewrite <-switch_num. cbn -[sat].
    specialize (H n rho).
    rewrite !num_subst in *.
    assert (ψ[var] = ψ[up (up (up (num n)..))] ) as <-.
    { eapply bounded_subst. apply Hψ.
    intros [|[]]; try now intros. lia. }
    assert (alpha[var] = alpha[up (up (num n)..)] ) as E.
    { eapply bounded_subst. apply unary_alpha.
    intros []; try now intros. lia. }
    setoid_rewrite <-E. rewrite !subst_var.
    rewrite unfold_sless, !num_subst in *.
    apply H.
    apply Overspill_DN in H'; auto.
    2 : { unfold unary. solve_bounds.
          all: eapply bounded_up; try apply binary_alpha; try apply Hψ.
          all: eauto; lia. }
    rewrite <-NNN_N.
    apply (DN_chaining H'), DN. clear H' H.
      intros (e & He1 & He2).
      specialize (He2 (fun _ => i0)).
      cbn in He2. apply (DN_chaining He2), DN.
      intros [a Ha].
      exists a. intros n rho.
      assert (inu n i⧀ e) as Hne;  [now apply num_lt_nonStd|].
      specialize (Ha _ Hne) as [Ha1 Ha2].
      split; cbn.
    + intros H. destruct Ha1 as [d Hd].
      eapply bound_ext. apply unary_alpha. 2: apply H.
      intros []; try now intros. lia.
      exists d. split.
      eapply bound_ext. apply Hψ. 2: apply Hd.
      intros [|[]]; try now intros. lia.
      apply Hd.
    + intros [k Hk].
      eapply bound_ext. apply unary_alpha. 2: apply Ha2.
      intros []; try now intros. lia.
      exists k. split.
      eapply bound_ext. apply Hψ. 2: apply Hk.
      intros [|[]]; try now intros. lia.
      apply Hk.
  Qed.


  Theorem Coding_nonstd_binary_Definite alpha :
    binary alpha -> (forall b u, definite (forall rho, (inu u .: b .: rho) ⊨ alpha ) ) ->
     ~ ~ forall b, exists a, forall u rho, (inu u .: b .: a .: rho) ⊨ (alpha ↔ ∃ (ψ ∧ ∃ $1 ⊗ $0 == $4)).
  Proof.
    intros binary_alpha Def_A.
    specialize (@Coding_model_binary_Definite _ binary_alpha Def_A) as H.
    assert (forall n rho, (inu n .: rho) ⊨ ∀ ∃ ∀ $0 ⧀ $3 → alpha[up $1..] ↔ ∃ (ψ ∧ ∃ $1 ⊗ $0 == $3) ) as H'.
    intros n rho. pose (@switch_num D I) as switch_num. cbn in switch_num.
    rewrite <-switch_num. cbn -[sat]. rewrite !num_subst.
    assert (ψ[var] = ψ[up (up (up (up (num n)..)))] ) as <-.
    eapply bounded_subst. apply Hψ.
    intros [|[]]; try now intros. lia.
    assert (alpha[up $1..][var] = alpha[up $1..][up (up (up (num n)..))] ) as E.
    rewrite !subst_comp.
    eapply bounded_subst. apply binary_alpha.
    intros [|[]]; cbn; try reflexivity; lia.
    setoid_rewrite <-E. rewrite !subst_var.
    specialize (H n). 
    rewrite unfold_sless, !num_subst in H.
    apply H.
    apply Overspill_DN in H'; auto.
    2 : { unfold unary. solve_bounds.
          2, 3: try eapply bounded_up; try apply binary_alpha; try apply Hψ; lia.
          all: eapply subst_bound; eauto.
          all: intros [|[]] ?; solve_bounds. }
    apply (DN_chaining H'), DN. clear H' H.
      intros (e & He1 & He2). intros b.
      cbn in He2. specialize (He2 (fun _ => i0) b) as [a Ha].
      exists a. intros n rho.
      assert (inu n i⧀ e) as Hne;  [now apply num_lt_nonStd|].
      specialize (Ha _ Hne) as [Ha1 Ha2].
      split; cbn.
    + intros H. destruct Ha1 as [d Hd].
      rewrite sat_comp.
      eapply bound_ext. apply binary_alpha. 2: apply H.
      intros [|[]]; try now intros. lia.
      exists d. split.
      eapply bound_ext. apply Hψ. 2: apply Hd.
      intros [|[]]; try now intros. lia.
      apply Hd.
    + intros [k Hk].
      rewrite sat_comp in Ha2.
      eapply bound_ext. apply binary_alpha. 2: apply Ha2.
      intros [|[]]; try now intros. lia.
      exists k. split.
      eapply bound_ext. apply Hψ. 2: apply Hk.
      intros [|[]]; try now intros. lia.
      apply Hk.
  Qed.

End notStd.
End Coding.
End Model.