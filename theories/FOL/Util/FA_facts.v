From Undecidability.FOL.Util Require Import Syntax Syntax_facts FullTarski FullTarski_facts FullDeduction_facts FullDeduction.
Require Import Undecidability.FOL.PA.
Require Import Lia List Vector.
Import Vector.VectorNotations.



Lemma bounded_S_exists N phi : bounded (S N) phi <-> bounded N (∃ phi).
Proof.
  split; intros H.
  - now constructor.
  - inversion H. apply inj_pair2_eq_dec' in H4 as ->; trivial.
    unfold Dec.dec. decide equality.
Qed.

Lemma bounded_S_forall N phi : bounded (S N) phi <-> bounded N (∀ phi).
Proof.
  split; intros H.
  - now constructor.
  - inversion H. apply inj_pair2_eq_dec' in H4 as ->; trivial.
    unfold Dec.dec. decide equality.
Qed.



Section ND.

  Variable p : peirce.


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



Section FA_prv.

  Variable p : peirce.

  Variable Gamma : list form.
  Variable G : incl FAeq Gamma.
  
  
  Fixpoint join {X n} (v : t X n) (rho : nat -> X) :=
    match v with
    | Vector.nil _ => rho
    | Vector.cons _ x n w  => join w (x.:rho)
    end.

  Local Notation "v '∗' rho" := (join v rho) (at level 20).
    
  Arguments Weak {_ _ _ _}, _.

  
  Lemma reflexivity t : Gamma ⊢ (t == t).
  Proof.
    apply (Weak FAeq).

    pose (sigma := [t] ∗ var ).
    change (FAeq ⊢ _) with (FAeq ⊢ ($0 == $0)[sigma]).
    
    eapply (@subst_forall_prv _ _ 1).
    apply Ctx. all : firstorder. constructor.
    repeat solve_bounds.
  Qed.

  
  Lemma symmetry x y : Gamma ⊢ (x == y) -> Gamma ⊢ (y == x).
  Proof.
    apply IE. apply (Weak FAeq).

    pose (sigma := [x ; y] ∗ var ).
    change (FAeq ⊢ _) with (FAeq ⊢ ($1 == $0 ~> $0 == $1)[sigma]).
    
    apply (@subst_forall_prv _ _ 2).
    apply Ctx. all : firstorder.
    repeat solve_bounds.
  Qed.

    
  Lemma transitivity x y z :
    Gamma ⊢ (x == y) -> Gamma ⊢ (y == z) -> Gamma ⊢ (x == z).
  Proof.
    intros H. apply IE. revert H; apply IE.
    apply Weak with FAeq.

    pose (sigma := [x ; y ; z] ∗ var).
    change (FAeq ⊢ _) with (FAeq ⊢ ($2 == $1 ~> $1 == $0 ~> $2 == $0)[sigma]).
    
    apply (@subst_forall_prv _ _ 3).
    apply Ctx. all : try firstorder.
    repeat solve_bounds.
  Qed.
  

  Lemma eq_succ x y : Gamma ⊢ (x == y) -> Gamma ⊢ (σ x == σ y).
  Proof.
    apply IE. apply Weak with FAeq.

    pose (sigma := [y ; x] ∗ var ).
    change (FAeq ⊢ _) with (FAeq ⊢ ($0 == $1 ~> σ $0 == σ $1)[sigma]).

    apply (@subst_forall_prv _ _ 2).
    apply Ctx. all : firstorder.
    repeat solve_bounds.
  Qed.

  
  Lemma eq_add {x1 y1 x2 y2} :
    Gamma ⊢ (x1 == x2) -> Gamma ⊢ (y1 == y2) -> Gamma ⊢ (x1 ⊕ y1 == x2 ⊕ y2).
  Proof.
    intros H; apply IE. revert H; apply IE.
    apply Weak with FAeq.

    pose (sigma := [y2 ; y1 ; x2 ; x1] ∗ var).
    change (FAeq ⊢ _) with (FAeq ⊢ ($0 == $1 ~> $2 == $3 ~> $0 ⊕ $2 == $1 ⊕ $3)[sigma]).

    apply (@subst_forall_prv _ _ 4).
    apply Ctx. all: firstorder.
    repeat solve_bounds.
  Qed.


  Lemma eq_mult {x1 y1 x2 y2} :
    Gamma ⊢ (x1 == x2) -> Gamma ⊢ (y1 == y2) -> Gamma ⊢ (x1 ⊗ y1 == x2 ⊗ y2).
  Proof.
    intros H; apply IE. revert H; apply IE.
    apply Weak with FAeq.
    
    pose (sigma := [y2 ; y1 ; x2 ; x1] ∗ var).
    change (FAeq ⊢ _) with (FAeq ⊢ ($0 == $1 ~> $2 == $3 ~> $0 ⊗ $2 == $1 ⊗ $3)[sigma]).
    
    apply (@subst_forall_prv _ _ 4).
    apply Ctx. all: firstorder.
    repeat solve_bounds.
  Qed.

  
  Lemma Add_rec x y : Gamma ⊢ ( (σ x) ⊕ y == σ (x ⊕ y) ).
  Proof.
    apply Weak with FAeq.

    pose (sigma := [y ; x] ∗ var).
    change (FAeq ⊢ _) with (FAeq ⊢ (σ $0 ⊕ $1 == σ ($0 ⊕ $1))[sigma]).

    apply (@subst_forall_prv _ _ 2).
    apply Ctx. all : firstorder.
    repeat solve_bounds.
  Qed.


  (* Defines numerals i.e. a corresponding term for every natural number *)
  Fixpoint num n :=  match n with
                       O => zero
                     | S x => σ (num x)
                     end.
  
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
    repeat solve_bounds.
  Qed.

  
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


Notation "x 'i=' y" := (i_atom (P:=Eq) [x ; y]) (at level 30) : PA_Notation.
Notation "'iO'" := (i_func (f:=Zero) []) (at level 2) : PA_Notation.
Notation "'iσ' d" := (i_func (f:=Succ) [d]) (at level 37) : PA_Notation.
Notation "x 'i⊕' y" := (i_func (f:=Plus) [x ; y]) (at level 39) : PA_Notation.
Notation "x 'i⊗' y" := (i_func (f:=Mult) [x ; y]) (at level 38) : PA_Notation.

                                                                        
Section FA_models.

  Variable D : Type.
  Variable I : interp D.

  Hypothesis ext_model : extensional I.
  Hypothesis FA_model : forall ax rho, List.In ax FA -> rho ⊨ ax.


  Fixpoint iμ k := match k with
                   | O => iO
                   | S n => iσ (iμ n)
                   end.
  
  
  Fact eval_num sigma n : eval sigma (num n) = iμ n.
  Proof.
    induction n.
    - reflexivity.
    - cbn. now rewrite IHn.
  Qed.  


  Lemma add_zero : forall d : D, iO i⊕ d = d.
  Proof.
    intros d.
    assert (List.In ax_add_zero FA) as H by firstorder.
    specialize (FA_model ax_add_zero (d.:(fun _ => iO)) H).
    cbn in FA_model. now apply ext_model.
  Qed.

  Lemma add_rec : forall n d : D, iσ n i⊕ d = iσ (n i⊕ d).
  Proof.
    intros n d.
    assert (List.In ax_add_rec FA) as H by firstorder.
    specialize (FA_model ax_add_rec (d.:(fun _ => iO))  H).
    cbn in FA_model. now apply ext_model. 
  Qed.

  Lemma mult_zero : forall d : D, iO i⊗ d = iO.
  Proof.
    intros d.
    assert (List.In ax_mult_zero FA) as H by firstorder.
    specialize (FA_model ax_mult_zero (d.:(fun _ => iO)) H).
    cbn in FA_model. now apply ext_model.
  Qed.

  Lemma mult_rec : forall n d : D, iσ d i⊗ n = n i⊕ d i⊗ n.
  Proof.
    intros n d.
    assert (List.In ax_mult_rec FA) as H by firstorder.
    specialize (FA_model ax_mult_rec (d.:(fun _ => iO)) H).
    cbn in FA_model. now apply ext_model.
  Qed.


  Corollary add_hom x y : iμ (x + y) = iμ x i⊕ iμ y.
  Proof.
    induction x.
    - now rewrite add_zero.
    - change (iσ iμ (x + y) = iσ iμ x i⊕ iμ y).
      now rewrite add_rec, IHx. 
  Qed.

  Corollary add_nat_to_model : forall x y z, x + y = z -> (iμ x i⊕ iμ y = iμ z).
  Proof.
    intros x y z H. now rewrite <- add_hom, H.
  Qed.

  Corollary mult_hom x y : iμ (x * y) = iμ x i⊗ iμ y.
  Proof.
    induction x.
    - now rewrite mult_zero.
    - change (iμ (y + x * y) = (iσ iμ x) i⊗ iμ y ).
      now rewrite add_hom, IHx, mult_rec.
  Qed.


  Corollary mult_nat_to_model : forall z x y, x * y = z -> (iμ x i⊗ iμ y = iμ z).
  Proof.
    intros x y z H. now rewrite <- mult_hom, H.
  Qed.


  
End FA_models.

Arguments iμ {_ _} _.



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

  
  Fact nat_extensional : extensional interp_nat.
  Proof.
    now intros x y. 
  Qed.

  
  Lemma nat_is_FA_model : forall rho phi,  List.In phi FAeq -> sat interp_nat rho phi.
  Proof.
    intros rho phi. intros H.
    repeat (destruct H as [<- | H]; auto).
    all: cbn; try congruence.
  Qed.

  
  Fact nat_eval_num (sigma : env nat) n : @eval _ _ _ interp_nat sigma (num n) = n.
  Proof.
    induction n.
    - reflexivity.
    - cbn. now rewrite IHn.
  Qed.


  Fact nat_induction phi : forall rho, sat interp_nat rho (ax_induction phi).
  Proof.
    intros rho H0 IH d. induction d; cbn in *.
    rewrite <-sat_single in H0. apply H0.
    apply IH in IHd. rewrite sat_comp in IHd.
    revert IHd. apply sat_ext. intros []; reflexivity.
  Qed.
    

  Fact nat_is_PAeq_model : forall ax rho, PAeq ax -> sat interp_nat rho ax.
  Proof.
    intros rho psi [].
    now apply nat_is_FA_model.
    all: cbn; try congruence.
    apply nat_induction.
 Qed.


  Fact nat_is_PA_model : forall ax rho, PA ax -> sat interp_nat rho ax.
  Proof.
    intros rho psi [].
    repeat (destruct H as [<- | H]; auto).
    all: cbn; try congruence.
    apply nat_induction.
  Qed.


  
End StdModel.

  


