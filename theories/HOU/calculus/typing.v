Set Implicit Arguments.
From Stdlib Require Import List Lia.
From Undecidability.HOU Require Import std.std.
From Undecidability.HOU.calculus Require Import prelim terms syntax semantics.

(* * Simple Typing *)

Section Typing.
  
  Context {X: Const}.
  
  Definition ctx := list type.

  Implicit Types (s t: exp X) (n m: nat) (Gamma Delta Sigma: ctx)
           (x y: fin) (c d: X) (A B: type)
           (sigma tau: fin -> exp X) (delta xi: fin -> fin).
  
  


  Reserved Notation "Gamma ⊢ s : A" (at level 80, s at level 99).

  Inductive typing  Gamma : exp X -> type -> Prop :=
  | typingVar i A: nth Gamma i = Some A -> Gamma ⊢ var i : A
  | typingConst c: Gamma ⊢ const c : ctype X c
  | typingLam s A B: A :: Gamma ⊢ s : B -> Gamma ⊢ lambda s : A → B
  | typingApp s t A B: Gamma ⊢ s : A → B -> Gamma ⊢ t : A -> Gamma ⊢ s t : B
  where "Gamma ⊢ s : A" := (typing Gamma s A).

  Hint Constructors typing : core.

  Definition typingRen Delta delta Gamma :=
    forall x A, nth Gamma x = Some A -> nth Delta (delta x) = Some A.

  Notation "Delta ⊫ delta : Gamma" := (typingRen Delta delta Gamma) (at level 80, delta at level 99).

  Definition typingSubst Delta sigma Gamma :=
    forall x A, nth Gamma x = Some A -> Delta ⊢ sigma x : A.

  Notation "Delta ⊩ sigma : Gamma" := (typingSubst Delta sigma Gamma) (at level 80, sigma at level 99).

  Lemma typingSubst_cons Delta sigma s Gamma A:
    Delta ⊩ sigma : Gamma -> Delta ⊢ s : A -> Delta ⊩ s .: sigma : A :: Gamma.
  Proof.
    intros ??[|]; cbn; eauto; now intros ? [= ->].
  Qed.

  (* ** Preservation *)
  Section Preservation.
    Lemma preservation_under_renaming delta Gamma Delta s A:
      Gamma ⊢ s : A -> Delta ⊫ delta : Gamma -> Delta ⊢ ren_exp delta s : A.
    Proof.
      induction 1 in  delta, Delta |-*; intros H'; cbn [ren_exp]; eauto.
      econstructor; apply IHtyping.
      intros []; cbn; eauto. 
    Qed.

    Lemma preservation_under_substitution sigma Gamma Delta s A:
      Gamma ⊢ s : A -> Delta ⊩ sigma: Gamma -> Delta ⊢ sigma • s : A.
    Proof.
      induction 1 in sigma, Delta |-*; intros H'; cbn [subst_exp]; subst; eauto.
      econstructor; apply IHtyping; intros []; cbn; eauto.
      intros; eapply preservation_under_renaming; eauto.
      intros ?; eauto. 
    Qed.

    Lemma preservation_under_reduction s s' Gamma A:
      s > s' -> Gamma ⊢ s : A -> Gamma ⊢ s' : A.
    Proof.
      induction 1 in Gamma, A |-*; intros H1; invp @typing; eauto. 
      inv H3. eapply preservation_under_substitution; eauto.
      intros []; cbn; eauto.
      intros ? H; now injection H as ->. 
    Qed.

    Lemma preservation_under_steps s s' Gamma A:
      s >* s' -> Gamma ⊢ s : A -> Gamma ⊢ s' : A.
    Proof.
      induction 1 in Gamma, A |-*; eauto using preservation_under_reduction. 
    Qed.

  End Preservation.

  Lemma weakening_app Gamma Delta s A:
    Gamma ⊢ s : A -> Gamma ++ Delta ⊢ s : A.
  Proof.
    intros H; replace s with (ren id s) by now asimpl.
    eapply preservation_under_renaming; eauto.
    intros i B H'; unfold id.
    rewrite nth_error_app1; eauto.
    eapply nth_error_Some_lt; eauto.
  Qed.



  Lemma typing_variables Gamma s A:
    Gamma ⊢ s : A -> forall x, x ∈ vars s -> x ∈ dom Gamma.
  Proof.
    intros ? x H1 % vars_varof.
    induction H in x, H1 |-*; inv H1; eauto.
    - now domin H. 
    - specialize (IHtyping _ H2).
      eapply dom_lt_iff in IHtyping. 
      cbn in *. assert (x < length Gamma) by lia. auto.
  Qed.

End Typing.


Notation "Gamma ⊢ s : A" := (typing Gamma s A) (at level 80, s at level 99).
Notation "Delta ⊫ delta : Gamma" := (typingRen Delta delta Gamma) (at level 80, delta at level 99).
Notation "Delta ⊩ sigma : Gamma" := (typingSubst Delta sigma Gamma) (at level 80, sigma at level 99).



#[export] Hint Constructors typing : core.
#[export] Hint Resolve typing_variables : core.

#[export] Hint Resolve
     preservation_under_renaming
     preservation_under_substitution : core.
     
