From Undecidability.FOL.Util Require Import Syntax Syntax_facts FullTarski FullTarski_facts FullDeduction_facts FullDeduction.
Require Import Undecidability.FOL.PA.
Require Import Lia List Vector.
Import Vector.VectorNotations.



  Lemma bounded_S_exists N phi : bounded (S N) phi <-> bounded N (∃ phi).
  Proof.
    split; intros H.
    - now constructor.
    - 
  Admitted.

  Lemma bounded_S_forall N phi : bounded (S N) phi <-> bounded N (∀ phi).
  Proof.
  Admitted.



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
      now apply bounded_S_exists.
  Qed.
   
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
      now apply bounded_S_forall.
  Qed.

End ND.


Section SEM.


  Context {D : Type}.
  Context {I : interp D}.

  
  Lemma bounded_eval_t n t sigma tau :
    (forall k, n > k -> sigma k = tau k) -> bounded_t n t -> eval sigma t = eval tau t.
  Proof.
    intros H. induction 1; cbn; auto.
    f_equal. now apply Vector.map_ext_in.
  Qed.
    
  Lemma bound_ext N phi rho sigma :
    bounded N phi -> (forall n, n < N -> rho n = sigma n) -> (rho ⊨ phi <-> sigma ⊨ phi).
  Proof.
    induction 1 in sigma, rho |- *; cbn; intros HN; try tauto.
    - enough (map (eval rho) v = map (eval sigma) v) as E. now setoid_rewrite E.
      apply Vector.map_ext_in. intros t Ht.
      eapply bounded_eval_t; try apply HN. now apply H.
    - destruct binop; now rewrite (IHbounded1 rho sigma), (IHbounded2 rho sigma).
    - destruct quantop.
      + split; intros Hd d; eapply IHbounded.
        all : try apply (Hd d); intros [] Hk; cbn; auto.
        symmetry. all: apply HN; lia.
      + split; intros [d Hd]; exists d; eapply IHbounded.
        all : try apply Hd; intros [] Hk; cbn; auto.
        symmetry. all: apply HN; lia.
  Qed.
  

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
      now apply bounded_S_exists.
  Qed.
  

  Fact subst_exist_sat2 N : forall rho phi, rho ⊨ (exist_times N phi) -> (exists sigma, sigma ⊨ phi).
  Proof.
    induction N.
    - eauto.
    - intros rho phi [? H]. now apply IHN in H.
  Qed.
  

End SEM.



Section FA_models.

  Variable D : Type.
  Variable I : interp D.
  
  Hypothesis ext_model : extensional I.
  Hypothesis FA_model : forall ax rho, List.In ax FA -> rho ⊨ ax.


  Fact eval_num sigma n : eval sigma (num n) = iμ n.
  Proof.
    induction n.
    - reflexivity.
    - cbn. now rewrite IHn.
  Qed.  

End FA_models.



Section StdModel.

  Definition interp_nat : interp nat.
  Proof.
    split.
    - destruct f; intros v.
      + exact 0.
      + exact (S (Vector.hd v) ).
      + exact (Vector.hd v + Vector.hd (Vector.tl v) ).
      + exact (Vector.hd v * Vector.hd (Vector.tl v) ).
    - destruct P. intros v.
      exact (Vector.hd v = Vector.hd (Vector.tl v) ).
  Defined.


  Lemma nat_is_FA_model : forall rho phi,  List.In phi FAeq -> sat interp_nat rho phi.
  Proof.
    intros rho phi. intros [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]; cbn; try congruence.
  Qed.


  Fact nat_eval_num (sigma : env nat) n : @eval _ _ _ interp_nat sigma (num n) = n.
  Proof.
    induction n.
    - reflexivity.
    - cbn. now rewrite IHn.
  Qed.

End StdModel.

  

Section FA_prv.

  Variable p : peirce.
  
  Fixpoint join {X n} (v : t X n) (rho : nat -> X) :=
    match v with
    | Vector.nil _ => rho
    | Vector.cons _ x n w  => join w (x.:rho)
    end.

  Local Notation "v '∗' rho" := (join v rho) (at level 20).

  
  Variable Gamma : list form.
  Variable G : incl FAeq Gamma.


  Arguments Weak {_ _ _ _}, _.

  Lemma reflexivity t : Gamma ⊢ (t == t).
  Proof.
    apply (Weak FAeq).

    pose (sigma := [t] ∗ var ).
    change (FAeq ⊢ _) with (FAeq ⊢ ($0 == $0)[sigma]).
    
    eapply (@subst_forall_prv _ _ 1).
    apply Ctx. all : firstorder.
  Admitted.

  
  Lemma symmetry x y : Gamma ⊢ (x == y) -> Gamma ⊢ (y == x).
  Proof.
    apply IE. apply (Weak FAeq).

    pose (sigma := [x ; y] ∗ var ).
    change (FAeq ⊢ _) with (FA ⊢ ($0 == $1 ~> $1 == $0)[sigma]).
    
    apply (@subst_forall_prv _ _ 2).
    apply Ctx. all : firstorder.
  Admitted.

  
  
  Lemma transitivity x y z :
    Gamma ⊢ (x == y) -> Gamma ⊢ (y == z) -> Gamma ⊢ (x == z).
  Proof.
    intros H. apply IE. revert H; apply IE.
    apply Weak with FAeq.

    pose (sigma := [x ; y ; z] ∗ var).
    change (FAeq ⊢ _) with (FA ⊢ ($0 == $1 ~> $1 == $2 ~> $0 == $2)[sigma]).
    
    apply (@subst_forall_prv _ _ 3).
    apply Ctx. all : try firstorder.
  Admitted.
  

  Lemma eq_succ x y : Gamma ⊢ (x == y) -> Gamma ⊢ (σ x == σ y).
  Proof.
    apply IE. apply Weak with FAeq.

    pose (sigma := [y ; x] ∗ var ).
    change (FAeq ⊢ _) with (FA ⊢ ($0 == $1 ~> σ $0 == σ $1)[sigma]).

    apply (@subst_forall_prv _ _ 2).
    apply Ctx. all : firstorder.
  Admitted.

  
  Lemma eq_add {x1 y1 x2 y2} :
    Gamma ⊢ (x1 == x2) -> Gamma ⊢ (y1 == y2) -> Gamma ⊢ (x1 ⊕ y1 == x2 ⊕ y2).
  Proof.
    intros H; apply IE. revert H; apply IE.
    apply Weak with FAeq.

    pose (sigma := [y2 ; y1 ; x2 ; x1] ∗ var).
    change (FAeq ⊢ _) with (FA ⊢ ($0 == $1 ~> $2 == $3 ~> $0 ⊕ $2 == $1 ⊕ $3)[sigma]).

    apply (@subst_forall_prv _ _ 4).
    apply Ctx. all: firstorder.
  Admitted.


  Lemma eq_mult {x1 y1 x2 y2} :
    Gamma ⊢ (x1 == x2) -> Gamma ⊢ (y1 == y2) -> Gamma ⊢ (x1 ⊗ y1 == x2 ⊗ y2).
  Proof.
    intros H; apply IE. revert H; apply IE.
    apply Weak with FAeq.
    
    pose (sigma := [y2 ; y1 ; x2 ; x1] ∗ var).
    change (FAeq ⊢ _) with (FA ⊢ ($0 == $1 ~> $2 == $3 ~> $0 ⊗ $2 == $1 ⊗ $3)[sigma]).
    
    apply (@subst_forall_prv _ _ 4).
    apply Ctx. all: firstorder.
  Admitted.

  
  Lemma Add_rec x y : Gamma ⊢ ( (σ x) ⊕ y == σ (x ⊕ y) ).
  Proof.
    apply Weak with FAeq.

    pose (sigma := [y ; x] ∗ var).
    change (FAeq ⊢ _) with (FAeq ⊢ (σ $0 ⊕ $1 == σ ($0 ⊕ $1))[sigma]).

    apply (@subst_forall_prv _ _ 2).
    apply Ctx. all : firstorder. 
  Admitted.
  
  
  Lemma num_add_homomorphism  x y : Gamma ⊢ ( num x ⊕ num y == num (x + y) ).
  Proof.
    induction x; cbn.
    - apply (@AllE _ _ _ _ _ _ (zero ⊕ $0 == $0) ).
      apply Weak with FAeq.
      apply Ctx;firstorder.
      assumption.
    - eapply transitivity.
      apply Add_rec.
      now apply eq_succ.
  Qed.
  

  Lemma Mult_rec x y : Gamma ⊢ ( (σ x) ⊗ y == y ⊕ (x ⊗ y) ).
  Proof.
    apply Weak with FAeq.

    pose (sigma := [x ; y] ∗ var).
    change (FAeq ⊢ _) with (FAeq ⊢ ((σ $1) ⊗ $0 == $0 ⊕ ($1 ⊗ $0))[sigma]).

    eapply (@subst_forall_prv _ _ 2).
    apply Ctx. all : firstorder.
  Admitted.

  
  Lemma num_mult_homomorphism (x y : nat) : Gamma ⊢ ( num x ⊗ num y == num (x * y) ).
  Proof.
    induction x; cbn.
    - apply (@AllE _ _ _ _ _ _ (zero ⊗ $0 == zero)).
      apply Weak with FAeq. apply Ctx; firstorder.
      assumption.
    - eapply transitivity.
      apply Mult_rec.
      eapply transitivity.
      2: apply num_add_homomorphism.
      apply eq_add. apply reflexivity. apply IHx.
  Qed.

End FA_prv.  

