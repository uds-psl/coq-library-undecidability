From Undecidability.FOL.Util Require Import Syntax Syntax_facts FullTarski FullTarski_facts FullDeduction_facts FullDeduction.
Require Import Undecidability.FOL.PA.
Require Import Lia List Vector.
Import Vector.VectorNotations.




Section ND.

  Variable p : peirce.


  Lemma numeral_subst_invariance : forall n rho, subst_term rho (num n) = num n.
  Proof.
    induction n.
    - reflexivity.
    - intros rho. cbn. now rewrite IHn.
  Qed.



  Fixpoint iter {X: Type} f n (x : X) :=
    match n with
      0 => x
    | S m => f (iter f m x)
    end.

  Fact iter_switch {X} f n x : f (@iter X f n x) = iter f n (f x).
  Proof. induction n; cbn; now try rewrite IHn. Qed.
    
  

  Lemma subst_up_var k x sigma : x < k -> (var x)`[iter up k sigma] = var x.
  Proof.
    induction k in x, sigma |-*.
    - now intros ?%PeanoNat.Nat.nlt_0_r.
    - intros H.
      destruct (Compare_dec.lt_eq_lt_dec x k) as [[| <-]|].
      + cbn [iter]. rewrite iter_switch. now apply IHk.
      + destruct x. reflexivity.
        change (iter _ _ _) with (up (iter up (S x) sigma)).
        change (var (S x)) with ((var x)`[↑]).
        rewrite up_term, IHk. reflexivity. constructor.
      + lia.
  Qed.
  
  
  Lemma subst_bounded_term t sigma k : bounded_t k t -> t`[iter up k sigma] = t.
  Proof.
    induction 1.
    - now apply subst_up_var.
    - cbn. f_equal.
      rewrite <-(Vector.map_id _ _ v) at 2.
      apply Vector.map_ext_in. auto.
  Qed.
  


  Lemma subst_bounded k phi sigma : bounded k phi -> phi[iter up k sigma] = phi.
  Proof.
    induction 1 in sigma |-*; cbn.
    - f_equal.
      rewrite <-(Vector.map_id _ _ v) at 2.
      apply Vector.map_ext_in.
      intros t Ht. apply subst_bounded_term. auto.
    - now rewrite IHbounded1, IHbounded2.
    - f_equal.
      change (up _) with (iter up (S n) sigma).
      apply IHbounded.
    - reflexivity.
  Qed.


  Definition exist_times n (phi : form) := iter (fun psi => ∃ psi) n phi.
  Definition forall_times n (phi : form) := iter (fun psi => ∀ psi) n phi.
  

  Lemma up_decompose sigma phi : phi[up (S >> sigma)][(sigma 0)..] = phi[sigma].
  Proof.
    rewrite subst_comp. apply subst_ext.
    intros [].
    - reflexivity.
    - apply subst_term_shift.
  Qed.
  

  
  Lemma subst_exist_prv {sigma N Gamma} phi :
    Gamma ⊢ phi[sigma] -> bounded N phi -> Gamma ⊢ exist_times N phi. 
  Proof.
    induction N in phi, sigma |-*; intros; cbn.
    - erewrite <-(subst_bounded 0); eassumption.
    - rewrite iter_switch. eapply (IHN (S >> sigma)).
      cbn. eapply (ExI (sigma 0)).
      now rewrite up_decompose.
      admit.
  Admitted.

   
  Lemma subst_forall_prv phi {N Gamma} :
    Gamma ⊢ (iter (fun psi => ∀ psi) N phi) -> bounded N phi -> forall sigma, Gamma ⊢ phi[sigma].
  Proof.
    induction N in phi |-*; intros ?? sigma; cbn in *.
    - change sigma with (iter up 0 sigma).
      now rewrite (subst_bounded 0).
    - specialize (IHN (∀ phi) ).
      rewrite <-up_decompose.
      apply AllE. apply IHN.
      now rewrite <-iter_switch.
      admit.
  Admitted.

End ND.


Section SEM.


  Context {D : Type}.
  Context {I : interp D}.

  Lemma bound_ext N phi rho sigma :
    bounded N phi -> (forall n, n < N -> rho n = sigma n) -> (rho ⊨ phi <-> sigma ⊨ phi).
  Proof.
  Admitted.
  

  Corollary sat_closed rho sigma phi :
    bounded 0 phi -> rho ⊨ phi <-> sigma ⊨ phi.
  Proof.
    intros H. eapply bound_ext. apply H. lia.
  Qed.

  
  Lemma subst_exist_sat rho phi N :
    rho ⊨ phi -> bounded N phi -> forall rho, rho ⊨ (exist_times N phi).  
  Proof.
    induction N in phi, rho |-*; intros.
    - cbn. eapply sat_closed; eassumption.
    - cbn -[sat]. rewrite iter_switch. apply (IHN (S >> rho)).
      exists (rho 0). eapply sat_ext. 2: apply H.
      now intros [].
  Admitted.
  

  Fact subst_exist_sat2 N : forall rho phi, rho ⊨ (exist_times N phi) -> (exists sigma, sigma ⊨ phi).
  Proof.
    induction N.
    - eauto.
    - intros rho phi [? H]. now apply IHN in H.
  Qed.
  

End SEM.






Definition ax_EQ := ((forall_times 1 ($0 == $0))::
                                                (forall_times 2 ($0 == $1 ~> $1 == $0))::
                                                (forall_times 3 ($0 == $1 ~> $1 == $2 ~> $0 == $2))::
                                                (forall_times 2 ($0 == $1 ~> σ $0 == σ $1))::
                                                (forall_times 4 ($0 == $1 ~> $2 == $3 ~> $0 ⊕ $2 == $1 ⊕ $3))::                    (forall_times 4 ($0 == $1 ~> $2 == $3 ~> $0 ⊗ $2 == $1 ⊗ $3))::List.nil)%list.


Definition ax_FA := (ax_add_zero::ax_add_rec::ax_mult_zero::ax_mult_rec::List.nil)%list.
Definition FA := (ax_FA ++ ax_EQ)%list.




Section FA_models.

  Variable D : Type.
  Variable I : interp D.
  
  Hypothesis ext_model : extensional I.
  Hypothesis FA_model : forall ax rho, List.In ax FA_facts.FA -> rho ⊨ ax.

  


End FA_models.


  

Section FA_prv.

  Variable p : peirce.
  
  Fixpoint join {X n} (v : t X n) (rho : nat -> X) :=
    match v with
    | Vector.nil _ => rho
    | Vector.cons _ x n w  => join w (x.:rho)
    end.

  Local Notation "v '∗' rho" := (join v rho) (at level 20).

  
  Variable Gamma : list form.
  Variable G : incl FA Gamma.


  Arguments Weak {_ _ _ _}, _.

  Lemma reflexivity t : Gamma ⊢ (t == t).
  Proof.
    apply (Weak FA).

    pose (sigma := [t] ∗ var ).
    change (FA ⊢ _) with (FA ⊢ ($0 == $0)[sigma]).
    
    eapply subst_forall_prv.
    apply Ctx. all : firstorder.
  Admitted.

  
  Lemma symmetry x y : Gamma ⊢ (x == y) -> Gamma ⊢ (y == x).
  Proof.
    apply IE. apply (Weak FA).

    pose (sigma := [y ; x] ∗ var ).
    change (FA ⊢ _) with (FA ⊢ ($0 == $1 ~> $1 == $0)[sigma]).
    
    eapply subst_forall_prv.
    apply Ctx. all : firstorder.
  Admitted.

  
  
  Lemma transitivity x y z :
    Gamma ⊢ (x == y) -> Gamma ⊢ (y == z) -> Gamma ⊢ (x == z).
  Proof.
    intros H. apply IE. revert H; apply IE.
    apply (Weak FA).

    pose (sigma := [z ; y ; x] ∗ var).
    change (FA ⊢ _) with (FA ⊢ ($0 == $1 ~> $1 == $2 ~> $0 == $2)[sigma]).
    
    eapply subst_forall_prv.
    apply Ctx. all : try firstorder.
  Admitted.
  

  Lemma eq_succ x y : Gamma ⊢ (x == y) -> Gamma ⊢ (σ x == σ y).
  Proof.
    apply IE. apply (Weak FA).

    pose (sigma := [y ; x] ∗ var ).
    change (FA ⊢ _) with (FA ⊢ ($0 == $1 ~> σ $0 == σ $1)[sigma]).

    eapply subst_forall_prv.
    apply Ctx. all : firstorder.
  Admitted.

  
  Lemma eq_add {x1 y1 x2 y2} :
    Gamma ⊢ (x1 == x2) -> Gamma ⊢ (y1 == y2) -> Gamma ⊢ (x1 ⊕ y1 == x2 ⊕ y2).
  Proof.
    intros H; apply IE. revert H; apply IE.
    apply (Weak FA).

    pose (sigma := [y2 ; y1 ; x2 ; x1] ∗ var).
    change (FA ⊢ _) with (FA ⊢ ($0 == $1 ~> $2 == $3 ~> $0 ⊕ $2 == $1 ⊕ $3)[sigma]). 

    eapply subst_forall_prv.
    apply Ctx. all: firstorder.
  Admitted.


  Lemma eq_mult {x1 y1 x2 y2} :
    Gamma ⊢ (x1 == x2) -> Gamma ⊢ (y1 == y2) -> Gamma ⊢ (x1 ⊗ y1 == x2 ⊗ y2).
  Proof.
    intros H; apply IE. revert H; apply IE.
    apply (Weak FA).
    
    pose (sigma := [y2 ; y1 ; x2 ; x1] ∗ var).
    change (FA ⊢ _) with (FA ⊢ ($0 == $1 ~> $2 == $3 ~> $0 ⊗ $2 == $1 ⊗ $3)[sigma]).
    
    eapply subst_forall_prv.
    apply Ctx. all: firstorder.
  Admitted.

  
  Lemma Add_rec x y : Gamma ⊢ ( (σ x) ⊕ y == σ (x ⊕ y) ).
  Proof.
    apply Weak with FA.

    pose (sigma := [y ; x] ∗ var).
    change (FA ⊢ _) with (FA ⊢ (σ $0 ⊕ $1 == σ ($0 ⊕ $1))[sigma]).

    eapply subst_forall_prv.
    apply Ctx. all : firstorder. 
  Admitted.
  
  
  Lemma num_add_homomorphism  x y : Gamma ⊢ ( num x ⊕ num y == num (x + y) ).
  Proof.
    induction x; cbn.
    - apply (@AllE _ _ _ _ _ _ (zero ⊕ $0 == $0) ).
      unfold FA. apply Ctx. firstorder.
    - eapply transitivity.
      apply Add_rec.
      now apply eq_succ.
  Qed.
  

  Lemma Mult_rec x y : Gamma ⊢ ( (σ x) ⊗ y == y ⊕ (x ⊗ y) ).
  Proof.
    apply Weak with FA.

    pose (sigma := [x ; y] ∗ var).
    change (FA ⊢ _) with (FA ⊢ ((σ $1) ⊗ $0 == $0 ⊕ ($1 ⊗ $0))[sigma]).

    eapply (@subst_forall_prv _ _ 2).
    apply Ctx. all : firstorder. 
  Admitted.

  
  Lemma num_mult_homomorphism (x y : nat) : Gamma ⊢ ( num x ⊗ num y == num (x * y) ).
  Proof.
    induction x; cbn.
    - apply (@AllE _ _ _ _ _ _ (zero ⊗ $0 == zero)).
      apply Ctx; firstorder.
    - eapply transitivity.
      apply Mult_rec.
      eapply transitivity.
      2: apply num_add_homomorphism.
      apply eq_add. apply reflexivity. apply IHx.
  Qed.
  
  
  Lemma add_nat_to_deduction x y z : x + y = z -> Gamma ⊢ (num x ⊕ num y == num z).
  Proof.
    intros <-. apply num_add_homomorphism.
  Abort.


  Lemma mult_nat_to_deduction x y z : x*y = z -> Gamma ⊢ (num x ⊗ num y == num z).
  Proof.
    intros <-. apply num_mult_homomorphism.
  Abort.
  

End FA_prv.  
