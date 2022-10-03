From Undecidability.Synthetic Require Import Definitions.
From Undecidability.FOL Require Import FullSyntax.
From Undecidability.FOL.Arithmetics Require Import Signature PA DeductionFacts.
From Undecidability.FOL.Syntax Require Import Theories.
From Undecidability.FOL.Tennenbaum Require Import Peano.
From Undecidability.FOL.Tennenbaum.Utils Require Import DN PrimeFunc Synthetic.
Require Import List Lia.
Import Vector.VectorNotations.
Require Import Setoid Morphisms.

Notation "x 'el' A" := (List.In x A) (at level 70).
Notation "A '<<=' B" := (List.incl A B) (at level 70).
Notation "x ∣ y" := (PrimeFunc.div x y) (at level 50).

Definition unary α := bounded 1 α.
Definition binary α := bounded 2 α.


Section Arithmetic.

  Existing Instance PA_preds_signature.
  Existing Instance PA_funcs_signature.
  Notation "⊨ ϕ" := (forall ρ, ρ ⊨ ϕ) (at level 21).

  Variable D : Type.
  Variable I : @interp PA_funcs_signature _ D.
  Existing Instance I.
  Context {axioms : forall ax, PAeq ax -> ⊨ ax}.

  Notation "x 'i=' y"  := (@i_atom PA_funcs_signature PA_preds_signature D I Eq ([x ; y])) (at level 80).
  Notation "'iσ' x" := (@i_func PA_funcs_signature PA_preds_signature D I Succ ([x])) (at level 60).
  Notation "x 'i⊕' y" := (@i_func PA_funcs_signature PA_preds_signature D I Plus ([x ; y])) (at level 62).
  Notation "x 'i⊗' y" := (@i_func PA_funcs_signature PA_preds_signature D I Mult ([x ; y])) (at level 61).
  Notation "'i0'" := (i_func (Σ_funcs:=PA_funcs_signature) (f:=Zero) []) (at level 2) : PA_Notation.

  Context {extensional : forall x y, x i= y <-> x = y}.

  Notation "x 'i⧀' y" := (Peano.iless I x y) (at level 80).


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
      split; exists 0; auto. 
      + apply axioms. 
      + apply extensional. 
    - intros. destruct (@zero_or_succ D I axioms extensional x) as [-> | [e ->]].
      + rewrite add_zero in Hn. rewrite <-Hn. split.
        exists 0; auto. exists (S n); auto.
        ++ apply axioms.
        ++ apply extensional.
      + cbn in *. rewrite add_rec in Hn. apply succ_inj in Hn.
        assert (std e /\ std y) as []. now apply IHn.
        split; auto.
        destruct H as [k <-]. exists (S k); auto.
        all: (apply axioms + apply extensional).
  Qed.

  Lemma std_mult x y m : 
    (iσ x) i⊗ y = inu I m -> std y.
  Proof.
    cbn. rewrite mult_rec. 
    - intros E.
    assert (std (y i⊕ x i⊗ y)) as H%std_add.
      + exists m; auto. + tauto.
    - apply axioms.
    - apply extensional.
  Qed.


  Lemma std_mult' x y m : 
    x i⊗ y = inu I (S m) -> std x /\ std y.
  Proof.
    destruct (@zero_or_succ D I axioms extensional x) as [-> | [e ->]],
      (@zero_or_succ D I axioms extensional y) as [-> | [d ->]].
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
    x < y <-> inu I x i⧀ inu I y.
  Proof.
    assert (x < y <-> exists k, S x + k = y) as H.
  split.
  - induction y in x |-*; [lia|].
    destruct x; intros; [exists y; lia|].
    destruct (IHy x) as [k <-]; [lia|].
    exists k; lia.
  - intros []. lia.
  - split.
    + intros [k <-]%H. exists (inu I k); cbn.
      rewrite inu_add_hom.
      * now apply iEq_refl.
      * apply axioms.
      * apply extensional.
    + intros [k Hk].
      assert (std (inu I (S x) i⊕ k)) as [_ [l Hl]]%std_add.
      * exists y. cbn. rewrite add_rec.
        ** apply extensional, Hk.
        ** apply axioms.
        ** apply extensional.
      * rewrite <-Hl in *.
        apply H. exists l.
        rewrite <-inu_inj, inu_add_hom; cbn.
        all: try (apply axioms + apply extensional).
        rewrite extensional in *.
        now rewrite add_rec, Hk.
  Qed.

  Lemma num_lt_nonStd n d : 
    ~ std d -> inu I n i⧀ d.
  Proof.
    intros nonStd.
    destruct (@trichotomy D I axioms extensional (inu I n) d) as [H|[<-|H]]; auto.
    all : contradiction nonStd.
    - exists n; auto.
    - apply lessthen_num in H. 
      + destruct H as [k [? ->]].
        exists k; auto.
      + apply axioms.
      + apply extensional.
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
    repeat solve_bounds.
    intros e; split; intros ?; [cbn|apply H].
    intros _. now apply extensional.
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

  Variable nStd : ~ @stdModel D I.

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
    (forall n rho, ((inu I n).:rho) ⊨ alpha) <-> (forall e, std e -> (forall rho, (e.:rho) ⊨ alpha)).
  Proof.
    split; intros H.
    - intros e [n <-]. apply H.
    - intros n. apply H. exists n; reflexivity.
  Qed.

  Lemma Overspill_DN :
    (forall x, stable (std x)) ->
    (forall n rho, ((inu I n).:rho) ⊨ alpha) ->  ~ ~ exists e, ~ std e /\ (forall rho, (e.:rho) ⊨ alpha).
  Proof.
    intros dne.
    setoid_rewrite on_std_equiv.
    now apply Overspill_DN'.
  Qed.


  Lemma Overspill_DNE :
    DNE ->
    (forall n rho, ((inu I n).:rho) ⊨ alpha) ->  exists e, ~ std e /\ (forall rho, (e.:rho) ⊨ alpha).
  Proof.
    intros dne H.
    now apply dne, Overspill_DN.
  Qed.


  End Overspill.


  Section Coding.

  (*  We assume that we have a formula ψ representing an injective function 
      which only produces prime numbers.
   *)
  Variable ψ : form.
  Variable Hψ : binary ψ /\ (forall x, Q ⊢I ∀ ψ[up (num x)..] ↔ $0 == num (Prime x) ).


  Definition div e d := exists k : D, e i⊗ k = d.
  Definition div_num n (d : D) := exists e, inu I n i⊗ e = d.
  Definition Div_nat (d : D) := fun n => div_num n d.
  Definition div_pi n a :=  (inu I n .: (fun _ => a)) ⊨ (∃ (ψ ∧ ∃ $1 ⊗ $0 == $3)).



  Lemma ψ_repr x d rho : 
    (d .: inu I x .: rho) ⊨ ψ <-> d = inu I (Prime x).
  Proof.
    destruct Hψ as (_ & H).
    specialize (H x).
    apply soundness in H.
    specialize (H D I). cbn -[Q] in H.
    setoid_rewrite extensional in H.
    setoid_rewrite eval_num in H.
    rewrite switch_up_num.
    apply H.
    intros ax Hax.
    repeat destruct Hax as [<- | Hax].
    1-4: apply axioms; constructor; cbn; auto 11.
    - apply axioms. constructor 2.
    - apply axioms. constructor 3.
    - cbn. setoid_rewrite extensional.
      now apply zero_or_succ.
    - tauto.
  Qed.


  Lemma ψ_equiv n a : div_pi n a <-> div_num (Prime n) a.
  Proof.
    unfold div_pi. cbn. split.
    - intros [d [->%ψ_repr H]]. unfold div_num. 
      setoid_rewrite <-extensional. apply H.
    - intros. exists (inu I (Prime n)). rewrite ψ_repr.
      setoid_rewrite extensional. now split.
  Qed.

  (** In the standard model, up to some bound. *)
  (*  This shows that we can potentially get a code representing any
      predicate on natural numbers up to some bound.
   *)
   Lemma Coding_nat A n :
   ~ ~ exists c, forall u, (u < n -> A u <-> Prime u ∣ c) /\ (Prime u ∣ c -> u < n).
 Proof.
  induction n.
  - apply DN. exists 1. intros u. split. lia.
    intros [x ].
    assert (Prime u > 1) by apply (Prime_prime u).
    destruct x; lia.
  - assert (~ ~ (A n \/ ~ A n)) as Dec_An by tauto.
    apply (DN_chaining Dec_An), (DN_chaining IHn), DN.
    clear IHn Dec_An.
    intros [a Ha] [A_n | NA_n].
    + exists (a * Prime n). intros u.
      assert (u < S n <-> u < n \/ u = n) as -> by lia.
      split.
      ++ intros [| ->]. split.
         +++ intros [k Hu]%Ha.
             * exists (k * Prime n). lia.
             * assumption.
         +++ assert (prime (Prime u)) as [_ Hu] by apply (Prime_prime u).
             intros [|H']%Hu; clear Hu.
             * apply Ha; assumption.
             * apply Prime_div_eq in H'.
               now rewrite H'.
          +++ intuition. exists a; lia.
       ++ assert (prime (Prime u)) as [_ Hu] by apply (Prime_prime u).
          intros [H |H]%Hu.
          * apply Ha in H; auto.
          * right. now apply Prime_div_eq.
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
    Definite A -> exists c, forall u, (u < n -> A u <-> Prime u ∣ c) /\ (Prime u ∣ c -> u < n).
  Proof.
    intros Def_A.
    induction n.
    - exists 1. intros u. split. lia.
      assert (Prime u > 1) by apply (Prime_prime u).
      intros [x ]; destruct x; lia.
    - destruct IHn as [a Ha], (Def_A n) as [A_n | NA_n].
      + exists (a * Prime n). intros u.
        assert (u < S n <-> u < n \/ u = n) as -> by lia.
        split.
        ++ intros [| ->]. split.
          +++ intros [k Hu]%Ha.
              * exists (k * Prime n). lia.
              * assumption.
          +++ assert (prime (Prime u)) as [_ Hu] by apply (Prime_prime u).
              intros [|H']%Hu; clear Hu.
              * apply Ha; assumption.
              * apply Prime_div_eq in H'.
                now rewrite H'.
            +++ intuition. exists a; lia.
        ++ assert (prime (Prime u)) as [_ Hu] by apply (Prime_prime u).
            intros [H |H]%Hu.
            * apply Ha in H; auto.
            * right. now apply Prime_div_eq.
      + exists a. intros u.
        assert (u < S n <-> u < n \/ u = n) as -> by lia.
        split.
        ++ intros Hu. destruct Hu as [| ->]. 
          now apply Ha.
          split. now intros ?%NA_n.
          intros H%Ha. lia.
        ++ intros H%Ha. tauto.
  Qed.

  Section notStd.

  (** In a non-standard model. *)

  (*  Above we have established coding results for arbitrary PA models.
      We will now focus on the special case where the model is not standard.
      Using Overspill we can eliminate the bound on the coding; in a non-standard
      model, we can find elements which code the entirety of a predicate.
   *)

  Variable notStd : ~ @stdModel D I.
  Variable stable_std : forall x, stable (std x).

  Theorem Coding_nonStd_unary alpha : 
    unary alpha -> ~ ~ exists c, forall u rho, (inu I u .: c .: rho) ⊨ (alpha ↔ ∃ (ψ ∧ ∃ $1 ⊗ $0 == $3)).
  Proof.
  Admitted.


  End notStd.

  End Coding.

End Arithmetic.