From Undecidability.FOL Require Import FullSyntax.
From Undecidability.FOL.Arithmetics Require Import Signature PA DeductionFacts.
From Undecidability.FOL.Syntax Require Import Theories.
From Undecidability.Shared Require Import ListAutomation.
From Undecidability.FOL.Tennenbaum2 Require Import MoreDecidabilityFacts Church Coding NumberUtils Formulas SyntheticInType Peano CantorPairing.

(* Require Import FOL Peano Tarski Deduction CantorPairing NumberTheory Synthetic DecidabilityFacts Formulas Coding Church. *)
Require Import Lia.

Import Vector.VectorNotations.



Notation "x 'el' A" := (List.In x A) (at level 70).
Notation "A '<<=' B" := (List.incl A B) (at level 70).
Notation "x ∣ y" := (exists k, x * k = y) (at level 50).

Definition unary α := bounded 1 α.
Definition binary α := bounded 2 α.


Section Model.

  Context {Δ1 : Delta1}.

  Variable D : Type.
  Variable I : interp D.
  Local Definition I' : interp D := extensional_model I.
  Existing Instance I | 100.
  Existing Instance I' | 0.
  Notation "⊨ phi" := (forall rho, rho ⊨ phi) (at level 21).
  Variable axioms : forall ax, PA ax -> ⊨ ax.

  Notation "N⊨ phi" := (forall rho, @sat _ _ nat interp_nat _ rho phi) (at level 40).


  Notation "x 'i=' y"  := (@i_atom PA_funcs_signature PA_preds_signature D I Eq ([x ; y])) (at level 80).
  Notation "'iσ' x" := (@i_func PA_funcs_signature PA_preds_signature D I Succ ([x])) (at level 60).
  Notation "x 'i⊕' y" := (@i_func PA_funcs_signature PA_preds_signature D I Plus ([x ; y])) (at level 62).
  Notation "x 'i⊗' y" := (@i_func PA_funcs_signature PA_preds_signature D I Mult ([x ; y])) (at level 61).
  Notation "'i0'" := (i_func (Σ_funcs:=PA_funcs_signature) (f:=Zero) []) (at level 2) : PA_Notation.
  Notation "x 'i⧀' y" := (exists d : D, y = iσ (x i⊕ d) ) (at level 40).

  Variable ψ : form.
  Variable Hψ : binary ψ /\ (forall x, Q ⊢I ∀ ψ[up (num x)..] ↔ $0 == num (Irred x) ).


  Definition div_num n (d : D) := @Coding.div_num D I n d.
  Definition div_pi n a := @Coding.div_pi D I ψ n a.

  (** * Enumerable and discrete PA models have decidable divisibility. *)

  Lemma nat_eq_dec (n m : nat) : {n=m} + {n <> m}.
  Proof. decide equality. Qed.

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
    refine (let H' := @iEuclid' D I axioms d (S n) _ in _).
    assert (exists q r, r < S n /\ d = (g q) i⊗ inu (S n) i⊕ inu r) as H.
    { destruct H' as [Q [r ]], (Hg Q) as [q Hq]. 
      exists q, r. unfold g. now rewrite Hq. 
    } clear H'.
    apply ProductWO in H.
    destruct H as [q [r [? Hr]]].
    * destruct (nat_eq_dec r 0) as [E|E].
      + left. exists (g q).
        now rewrite Hr, E, add_zero_r, mult_comm.
      + right. intros [k Hk]. apply E.
        enough (iE : inu r = inu 0). 
        { now apply inu_inj in iE. }
        enough ((g q) = k /\ inu r = inu 0) by tauto.
        eapply (@iFac_unique D I axioms).
        -- pose (@lt_equiv D I) as lt_equiv. unfold I'. rewrite <- inu_I. apply lt_equiv. easy. apply H.
        -- pose (@lt_equiv D I axioms 0 (S n)) as lt_equiv. unfold I'. rewrite <- inu_I.
           apply lt_equiv. lia.
        -- rewrite add_zero. rewrite add_comm. unfold I' in *. rewrite <- inu_I. rewrite <- ! inu_I in Hr. 
           rewrite <- Hr. rewrite mult_comm. all:eauto.
    * intros x y. apply and_dec; [apply Compare_dec.lt_dec|apply eq].
    Unshelve. lia.
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
    refine (let H := @iEuclid' D I axioms d (S n) _ in _).
    apply wo in H.
    - destruct H as [a Ha].
      apply Witnessing_nat in Ha. 
      * destruct Ha as [r [? Hr]].
        destruct (nat_eq_dec r 0) as [E|E].
        + left. exists a.
          now rewrite Hr, E, add_zero_r, mult_comm.
        + right. intros [k Hk]. apply E.
          enough (iE : inu r = inu 0). 
          { now apply inu_inj in iE. }
          enough (a = k /\ inu r = inu 0) by tauto.
          unshelve eapply (@iFac_unique D I axioms (inu (S n))).
          -- pose (@lt_equiv D I) as lt_equiv. unfold I'. rewrite <- inu_I. apply lt_equiv. easy. apply H.
          -- pose (@lt_equiv D I axioms 0 (S n)) as lt_equiv. unfold I'. rewrite <- inu_I.
             apply lt_equiv. lia.
          -- rewrite add_zero. rewrite add_comm. unfold I' in *. rewrite <- inu_I. rewrite <- ! inu_I. rewrite <- Hr. rewrite mult_comm. all:eauto.
      * intros x. apply and_dec; [apply Compare_dec.lt_dec|apply eq].
    - intros ?. apply dec_lt_bounded_exist.
      intros ?. apply eq.
    Unshelve. lia.
  Qed.


  (** * Tennenbaum's Theorem via a diagnoal argument. *)

  Fact dec_contraposition A B :
    dec B -> (~B -> ~A) -> (A -> B).
  Proof. intros HB nB a. destruct HB; tauto. Qed.

  (*  This lemma is similar to the coding lemmas in Coding.v as
      it allows decidable predicates to be coded.
   *)
  Lemma Coding_Dec p :
    CT_Q -> Stable std -> ~ stdModel D ->
    Dec p -> ~~ exists c, forall n, p n <-> div_pi n c.
  Proof.
    intros rt%CT_RTs ? notStd Dec_p.
    destruct (rt _ Dec_p) as [ϕ (b1 & _ & H1 & H2)].
    unshelve refine (let H:= @Coding_nonStd_unary _ _ _ _ Hψ _ _ (∃ ϕ) _ in _); auto.
    - unfold Coding.unary. now solve_bounds.
    - apply (DN_chaining H), DN; clear H.
      intros [c Hc].
      exists c; intros n. split.
      + intros H. specialize (Hc n (fun _ => c)) as [Hc1 _].
        apply H1 in H. apply soundness in H.
        unfold div_pi.
        eapply bound_ext with (N:= 2)(sigma:= inu n .: c .: (fun _ => c)).
        { repeat solve_bounds.
          eapply bounded_up; [apply Hψ|lia]. }
        { intros [|[]]; cbn; [reflexivity|reflexivity|lia]. }
        cbn in Hc1; apply Hc1.
        destruct (H D I' (fun _ => c)) as [d Hd].
        intros ??. apply (@sat_Qeq D I axioms psi H3 (fun _ : nat => c)).
        exists d. rewrite <-switch_up_num.
        eapply bound_ext with (N:=1). 3: apply Hd.
        eapply subst_bound. 1: eauto.
        intros [|[]] ?; solve_bounds.
        cbn. rewrite num_subst. apply closed_num.
        intros [|] ?; cbn. 1:easy. destruct n0; easy.
      + specialize (Hc n (fun _ => c)) as [_ Hc2].
        destruct (Dec_p) as [dec_p]; auto.
        apply dec_contraposition; [apply dec_p|].
        intros h [d Hd].
        specialize (H2 _ h). apply soundness in H2.
        eapply H2 with (rho := fun _ => i0); fold sat.
        intros ??; apply sat_Qeq. 1-2:eauto.
        setoid_rewrite switch_num. cbn in Hc2.
        eapply bound_ext with (N:= 1)(sigma:= inu n .: c .: (fun _ => c)).
        { now solve_bounds. }
        intros []; cbn; [reflexivity|lia].
        apply Hc2. exists d. split.
        { eapply bound_ext. apply Hψ. 2: apply Hd.
          intros [|[]]; cbn; [reflexivity|reflexivity|lia]. }
        destruct Hd as [_ [k Hk]]. exists k.
        now rewrite Hk.
  Qed.

  (*  We can now use the above coding lemma in combination with RT 
      to give a diagonal argument which shows that enumerable and  
      discrete PA models must potentially be standard.             
      The double negation can actually also be eliminated, and this
      is done in Variants.v, where the needed lemmas are shown.    
   *)

  Theorem Tennenbaum_diagonal :
    CT_Q -> MP -> Enumerable D -> Discrete D -> ~~ forall e, std e.
  Proof.
    intros ct mp enum eq notStd.
    specialize (dec_div enum eq) as [dec_div].
    specialize enum as [G HG].
    pose (g n := match G n with None => i0 | Some d => d end).
    pose (p n := ~ div_pi n (g n)).
    apply (@Coding_Dec p); auto.
    - intros e. apply MP_Dec_stable; auto.
      apply Discrete_sum in eq.
      destruct eq as [eq].
      constructor. intros n. apply eq.
    - unfold p. constructor. intros n.
      destruct (dec_div (Irred n, g n)) as [h|nh].
      + right. apply DN. now apply ψ_equiv.
      + left. intros ?. apply nh. eapply ψ_equiv; eauto.
    - intros [c' H]. destruct (HG c') as [c Hc].
      specialize (H c). revert H. 
      unfold p, g. rewrite Hc.
      tauto.
  Qed.

  (*  We can still establish the same result, with the weaker
      assumption of WCT_Q.
   *)
  Theorem Tennenbaum_diagonal' :
    WCT_Q -> MP -> Enumerable D -> Discrete D -> ~ exists e, ~std e.
  Proof.
    intros wrt%WCT_WRTs mp enum eq.
    specialize (dec_div enum eq) as [dec_div].
    specialize enum as [G HG].
    apply Discrete_sum in eq.
    pose (g n := match G n with None => i0 | Some d => d end).
    pose (p n := ~ div_pi n (g n)).
    enough (Dec p) as Dec_p.
    apply (DN_remove (wrt _ Dec_p)).
    intros [ϕ (b1 & _ & H1 & H2)] nonStd.
    unshelve refine (let H:= @Coding_nonStd_unary _ _ _ _ Hψ _ _ (∃ ϕ) _ in _); auto.
    - now apply nonStd_notStd.
    - intros e. apply MP_Dec_stable; auto.
      destruct eq as [eq]. constructor. intros n. apply eq.
    - unfold Coding.unary. now solve_bounds.
    - enough (~~False) by tauto.
      apply (DN_chaining H), DN.
      intros [cp Hcp]; clear H.
      destruct (HG cp) as [c Hc].
      specialize (Hcp c (fun _ => g c)) as [Hc1 Hc2].
      destruct Dec_p as [Dec_p], (Dec_p c) as [h|h].
      * specialize (H1 _ h). apply soundness in H1.
        apply h. unfold div_pi.
        eapply bound_ext with (N:= 2)(sigma:= inu c .: cp .: (fun _ => g c)).
        { repeat solve_bounds.
          eapply bounded_up; [apply Hψ|lia]. }
        { intros [|[]] ?; cbn; [reflexivity| |lia].
          unfold g. now rewrite Hc. }
        cbn in Hc1; apply Hc1.
        destruct (H1 D I' (fun _ => g c)) as [d Hd].
        intros ??. apply sat_Qeq; easy.
        exists d. rewrite <-switch_up_num.
        eapply bound_ext with (N:=1). 3: apply Hd.
        eapply subst_bound. 1: eauto.
        intros [|[]] ?; solve_bounds.
        cbn. rewrite num_subst. apply closed_num.
        intros [|] ?; cbn; eauto. destruct n; cbn; eauto. lia.
      * specialize (H2 _ h). apply soundness in H2.
        apply h. intros H'. eapply H2 with (rho := fun _ => i0); fold sat.
        intros ??; apply sat_Qeq; eauto.
        setoid_rewrite switch_num. cbn in Hc2.
        eapply bound_ext with (N:= 1)(sigma:= inu c .: cp .: (fun _ => g c)).
        { now solve_bounds. }
        intros []; cbn; [reflexivity|lia].
        apply Hc2. destruct H' as [d Hd].
        exists d. split.
        { eapply bound_ext. apply Hψ. 2: apply Hd.
          intros [|[]]; cbn; [reflexivity|reflexivity|lia]. }
        destruct Hd as [_ [k Hk]]. exists k.
        rewrite Hk; cbn. unfold g. now rewrite Hc.
    - unfold p. constructor. intros n.
      destruct (dec_div (Irred n, g n)) as [h|nh].
      + right. apply DN. now apply ψ_equiv.
      + left. intros ?. apply nh. eapply ψ_equiv; eauto.
  Qed.

End Model.