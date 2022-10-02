From Undecidability.Synthetic Require Import Definitions.
From Undecidability.FOL Require Import FullSyntax.
From Undecidability.FOL.Arithmetics Require Import Signature PA DeductionFacts.
From Undecidability.FOL.Syntax Require Import Theories.
From Undecidability.FOL.Tennenbaum Require Import Peano Coding Church.
From Undecidability.FOL.Tennenbaum.Utils Require Import DN DecidabilityFacts PrimeFunc Synthetic.
Require Import List Lia.
Import Vector.VectorNotations.
Require Import Setoid Morphisms.

Notation "x 'el' A" := (List.In x A) (at level 70).
Notation "A '<<=' B" := (List.incl A B) (at level 70).
Notation "x ∣ y" := (exists k, x * k = y) (at level 50).

Definition unary α := bounded 1 α.
Definition binary α := bounded 2 α.


Section Arithmetic.

  Variable peirce_ : peirce.

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

  Variable ψ : form.
  Variable Hψ : binary ψ /\ (forall x, Q ⊢I ∀ ψ[up (num x)..] ↔ $0 == num (Prime x) ).


  Definition div_num n (d : D) := exists e, inu I n i⊗ e = d.
  Definition div_pi n a := (inu I n .: (fun _ => a)) ⊨ (∃ (ψ ∧ ∃ $1 ⊗ $0 == $3)).

  (** * Enumerable and discrete PA models have decidable divisibility. *)

  Lemma dec_div :
    Enumerable D -> Discrete D -> Dec (fun '(n, d) => div_num n d).
  Proof.
    intros [G Hg] [eq]%Discrete_sum.
    pose (g n := match G n with None => i0 | Some d => d end).
    constructor. intros [n d].
    destruct (eq d i0) as [->|h].
    { left; exists i0. now rewrite mult_zero_r. }
    destruct n as [|n].
    { right; intros [k Hk]. rewrite mult_zero in Hk; auto. }
    refine (let H' := @iEuclid' D I axioms _ d (S n) _ in _).
    assert (exists q r, r < S n /\ d = (g q) i⊗ inu I (S n) i⊕ inu I r) as H.
    { destruct H' as [Q [r ]], (Hg Q) as [q Hq]. 
      exists q, r. unfold g. now rewrite Hq. 
    } clear H'.
    apply ProductWO in H.
    destruct H as [q [r [? Hr]]].
    * destruct (dec_eq_nat r 0) as [E|E].
      + left. exists (g q).
        now rewrite Hr, E, add_zero_r, mult_comm.
      + right. intros [k Hk]. apply E.
        enough (iE : inu I r = inu I 0). 
        { now apply inu_inj in iE. }
        enough ((g q) = k /\ inu I r = inu I 0) by tauto.
        unshelve eapply (@iFac_unique _ _ _ _ (inu I (S n))).
        -- apply axioms.
        -- apply extensional.
        -- apply lt_equiv; auto.
        -- apply lt_equiv; auto. lia.
        -- now rewrite add_zero, add_comm, <-Hr, mult_comm.
    * intros x y. apply dec_conj; [apply lt_dec|apply eq].
    Unshelve.
    - apply extensional.
    - lia.
  Qed.


  (*  We can show the same for types that are witnessing and discrete. 
      This is a bit more general, since every enumerable type is witnessing.
   *)
  Lemma dec_div_2 :
    Witnessing D -> Discrete D -> Dec (fun '(n, d) => div_num n d).
  Proof.
    intros wo [eq]%Discrete_sum.
    constructor. intros [n d].
    destruct (eq d i0) as [->|h].
    { left; exists i0. now rewrite mult_zero_r. }
    destruct n as [|n].
    { right; intros [k Hk]. rewrite mult_zero in Hk; auto. }
    refine (let H := @iEuclid' D I axioms _ d (S n) _ in _).
    apply wo in H.
    - destruct H as [a Ha].
      apply Witnessing_nat in Ha. 
      * destruct Ha as [r [? Hr]].
        destruct (dec_eq_nat r 0) as [E|E].
        + left. exists a.
          now rewrite Hr, E, add_zero_r, mult_comm.
        + right. intros [k Hk]. apply E.
          enough (iE : inu I r = inu I 0). 
          { now apply inu_inj in iE. }
          enough (a = k /\ inu I r = inu I 0) by tauto.
          unshelve eapply (@iFac_unique _ _ _ _ (inu I (S n))).
          -- apply axioms.
          -- apply extensional.
          -- now apply lt_equiv.
          -- apply lt_equiv; auto. lia.
          -- now rewrite add_zero, add_comm, <-Hr, mult_comm.
      * intros x. apply dec_conj; [apply lt_dec|apply eq].
    - intros ?. apply dec_lt_bounded_exist.
      intros ?. apply eq.
    Unshelve. 
    + apply extensional.
    + lia.
  Qed.


  (** * Tennenbaum's Theorem via a diagnoal argument. *)

  Fact dec_contraposition A B :
    dec B -> (~B -> ~A) -> (A -> B).
  Proof. intros []; intros; tauto. Qed.

  (*  This lemma is similar to the coding lemmas in Coding.v as
      it allows decidable predicates to be coded.
   *)
  Lemma Coding_Dec' p :
    WCT_Q -> Stable std -> ~ @stdModel D I ->
    Dec p -> ~~ exists c, forall n, p n <-> div_pi n c.
  Proof.
    intros wrt%WCT_WRTs ? notStd Dec_p.
    apply (DN_remove (wrt _ Dec_p)).
    intros [ϕ (b1 & _ & H1 & H2)] nonStd.
    unshelve refine (let H:= @Coding_nonStd_unary _ _ _ _ _ Hψ _ _ ϕ _ in _); auto.
    2-3: admit.
    enough (~~False) by tauto.
    apply (DN_chaining H), DN.
    intros [c Hc]; clear H. apply nonStd.
    exists c; intros n. split.
    - intros H. specialize (Hc n (fun _ => c)) as [Hc1 _].
      apply H1 in H. apply soundness in H.
      unfold div_pi.
      eapply bound_ext with (N:= 2)(sigma:= inu I n .: c .: (fun _ => c)).
      { repeat solve_bounds.
        eapply bounded_up; [apply Hψ|lia]. }
      { intros [|[]]; cbn; [reflexivity|reflexivity|lia]. }
      cbn in Hc1; apply Hc1.
      specialize (H D I (fun _ => c)).
      rewrite switch_num.
      eapply sat_ext. 2: apply H.
      + now intros [].
      + admit.
    - specialize (Hc n (fun _ => c)) as [_ Hc2].
      destruct (Dec_p) as [dec_p]; auto.
      apply dec_contraposition; [apply dec_p|].
      intros h [d Hd].
      specialize (H2 _ h). apply soundness in H2.
      eapply H2 with (rho := fun _ => i0); fold sat.
      { admit. }
      rewrite <-switch_num. cbn in Hc2.
      eapply bound_ext with (N:= 1)(sigma:= inu I n .: c .: (fun _ => c)).
      { now solve_bounds. }
      intros []; cbn; [reflexivity|lia].
      apply Hc2. exists d. split.
      { eapply bound_ext. apply Hψ. 2: apply Hd.
        intros [|[]]; cbn; [reflexivity|reflexivity|lia]. }
      destruct Hd as [_ [k Hk]]. cbn in Hk. now exists k.
  Admitted.

  Lemma Coding_Dec p :
    WCT_Q -> Stable std -> ~ @stdModel D I ->
    Dec p -> ~~ exists c, forall n, p n <-> div_pi n c.
  Proof.
    intros ?. now apply Coding_Dec'.
  Qed.


  (*  We can now use the above coding lemma in combination with RT 
      to give a diagonal argument which shows that enumerable and  
      discrete PA models must potentially be standard.             
      The double negation can actually also be eliminated, and this
      is done in Variants.v, where the needed lemmas are shown.    
   *)
  Local Fact MP_Discrete_stable_std :
    MP -> Discrete D -> Stable std.
  Proof.
    intros mp [eq]%Discrete_sum e. unfold Stable.
    refine (MP_Dec_stable mp _ _).
    constructor. intros ?; apply eq.
  Qed.

  (*  We can still establish the same result, with the weaker
      assumption of WCT_Q.
   *)
   Theorem Tennenbaum_diagonal' :
    WCT_Q -> MP -> Enumerable D -> Discrete D -> ~~ forall e, std e.
  Proof.
    intros wct mp enum eq notStd.
    specialize (dec_div enum eq) as [dec_div].
    specialize enum as [G HG].
    pose (g n := match G n with None => i0 | Some d => d end).
    pose (p n := ~ div_pi n (g n)).
    apply (@Coding_Dec' p wct); auto.
    - now apply MP_Discrete_stable_std.
    - unfold p. constructor. intros n.
      destruct (dec_div (Prime n, g n)) as [h|nh].
      + right. apply DN. now apply ψ_equiv.
      + left. intros ?. apply nh. eapply ψ_equiv; eauto.
    - intros [c' H]. destruct (HG c') as [c Hc].
      specialize (H c). revert H. 
      unfold p, g. rewrite Hc.
      tauto.
  Qed.

  Corollary Tennenbaum_diagonal :
    WCT_Q -> MP -> Enumerable D -> Discrete D -> ~~ forall e, std e.
  Proof.
    intros ?. now apply Tennenbaum_diagonal'.
  Qed.



End Arithmetic.