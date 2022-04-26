From Undecidability.FOL.Util Require Import Syntax Syntax_facts FullTarski FullTarski_facts FullDeduction_facts FullDeduction.
Require Import Undecidability.FOL.PA.
Require Import Lia List Vector.
Import Vector.VectorNotations.

Set Default Proof Using "Type".

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
  Proof using G.
    apply (Weak FAeq).

    pose (sigma := [t] ∗ var ).
    change (FAeq ⊢ _) with (FAeq ⊢ ($0 == $0)[sigma]).
    
    eapply subst_forall_prv with 1.
    apply Ctx. all : firstorder. constructor.
    repeat solve_bounds.
  Qed.


  Lemma symmetry x y : Gamma ⊢ (x == y) -> Gamma ⊢ (y == x).
  Proof using G.
    apply IE. apply (Weak FAeq).

    pose (sigma := [x ; y] ∗ var ).
    change (FAeq ⊢ _) with (FAeq ⊢ ($1 == $0 ~> $0 == $1)[sigma]).
    
    eapply subst_forall_prv with 2.
    apply Ctx. all : firstorder.
    repeat solve_bounds.
  Qed.


  Lemma transitivity x y z :
    Gamma ⊢ (x == y) -> Gamma ⊢ (y == z) -> Gamma ⊢ (x == z).
  Proof using G.
    intros H. apply IE. revert H; apply IE.
    apply Weak with FAeq.

    pose (sigma := [x ; y ; z] ∗ var).
    change (FAeq ⊢ _) with (FAeq ⊢ ($2 == $1 ~> $1 == $0 ~> $2 == $0)[sigma]).
    
    eapply subst_forall_prv with 3.
    apply Ctx. all : try firstorder.
    repeat solve_bounds.
  Qed.


  Lemma eq_succ x y : Gamma ⊢ (x == y) -> Gamma ⊢ (σ x == σ y).
  Proof using G.
    apply IE. apply Weak with FAeq.

    pose (sigma := [y ; x] ∗ var ).
    change (FAeq ⊢ _) with (FAeq ⊢ ($0 == $1 ~> σ $0 == σ $1)[sigma]).

    eapply subst_forall_prv with 2.
    apply Ctx. all : firstorder.
    repeat solve_bounds.
  Qed.


  Lemma eq_add {x1 y1 x2 y2} :
    Gamma ⊢ (x1 == x2) -> Gamma ⊢ (y1 == y2) -> Gamma ⊢ (x1 ⊕ y1 == x2 ⊕ y2).
  Proof using G.
    intros H; apply IE. revert H; apply IE.
    apply Weak with FAeq.

    pose (sigma := [y2 ; y1 ; x2 ; x1] ∗ var).
    change (FAeq ⊢ _) with (FAeq ⊢ ($0 == $1 ~> $2 == $3 ~> $0 ⊕ $2 == $1 ⊕ $3)[sigma]).

    eapply subst_forall_prv with 4.
    apply Ctx. all: firstorder.
    repeat solve_bounds.
  Qed.


  Lemma eq_mult {x1 y1 x2 y2} :
    Gamma ⊢ (x1 == x2) -> Gamma ⊢ (y1 == y2) -> Gamma ⊢ (x1 ⊗ y1 == x2 ⊗ y2).
  Proof using G.
    intros H; apply IE. revert H; apply IE.
    apply Weak with FAeq.
    
    pose (sigma := [y2 ; y1 ; x2 ; x1] ∗ var).
    change (FAeq ⊢ _) with (FAeq ⊢ ($0 == $1 ~> $2 == $3 ~> $0 ⊗ $2 == $1 ⊗ $3)[sigma]).
    
    eapply subst_forall_prv with 4.
    apply Ctx. all: firstorder.
    repeat solve_bounds.
  Qed.


  Lemma Add_rec x y : Gamma ⊢ ( (σ x) ⊕ y == σ (x ⊕ y) ).
  Proof using G.
    apply Weak with FAeq.

    pose (sigma := [y ; x] ∗ var).
    change (FAeq ⊢ _) with (FAeq ⊢ (σ $0 ⊕ $1 == σ ($0 ⊕ $1))[sigma]).

    eapply subst_forall_prv with 2.
    apply Ctx. all : firstorder.
    repeat solve_bounds.
  Qed.


  (* Defines numerals i.e. a corresponding term for every natural number *)
  Fixpoint num n :=  match n with
                       O => zero
                     | S x => σ (num x)
                     end.
  
  Lemma num_add_homomorphism  x y : Gamma ⊢ ( num x ⊕ num y == num (x + y) ).
  Proof using G.
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
  Proof using G.
    apply Weak with FAeq.

    pose (sigma := [x ; y] ∗ var).
    change (FAeq ⊢ _) with (FAeq ⊢ ((σ $1) ⊗ $0 == $0 ⊕ ($1 ⊗ $0))[sigma]).

    eapply subst_forall_prv with 2.
    apply Ctx. all : firstorder.
    repeat solve_bounds.
  Qed.


  Lemma num_mult_homomorphism (x y : nat) : Gamma ⊢ ( num x ⊗ num y == num (x * y) ).
  Proof using G.
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
Notation "'iO'" := (i_func (Σ_funcs:=PA_funcs_signature) (f:=Zero) []) (at level 2) : PA_Notation.
Notation "'iσ' d" := (i_func (f:=Succ) [d]) (at level 37) : PA_Notation.
Notation "x 'i⊕' y" := (i_func (f:=Plus) [x ; y]) (at level 39) : PA_Notation.
Notation "x 'i⊗' y" := (i_func (f:=Mult) [x ; y]) (at level 38) : PA_Notation.

                                                                        
Section FA_models.

  Variable D : Type.
  Variable I : interp D.

  Hypothesis ext_model : extensional I.
  Hypothesis FA_model : forall ax rho, List.In ax FA -> rho ⊨ ax.

  (** # <a id="imu" /> #*)
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
  Proof using ext_model FA_model.
    intros d.
    assert (List.In ax_add_zero FA) as H by firstorder.
    specialize (FA_model ax_add_zero (d.:(fun _ => iO)) H).
    cbn in FA_model. now apply ext_model.
  Qed.

  Lemma add_rec : forall n d : D, iσ n i⊕ d = iσ (n i⊕ d).
  Proof using ext_model FA_model.
    intros n d.
    assert (List.In ax_add_rec FA) as H by firstorder.
    specialize (FA_model ax_add_rec (d.:(fun _ => iO))  H).
    cbn in FA_model. now apply ext_model. 
  Qed.

  Lemma mult_zero : forall d : D, iO i⊗ d = iO.
  Proof using ext_model FA_model.
    intros d.
    assert (List.In ax_mult_zero FA) as H by firstorder.
    specialize (FA_model ax_mult_zero (d.:(fun _ => iO)) H).
    cbn in FA_model. now apply ext_model.
  Qed.

  Lemma mult_rec : forall n d : D, iσ d i⊗ n = n i⊕ d i⊗ n.
  Proof using ext_model FA_model.
    intros n d.
    assert (List.In ax_mult_rec FA) as H by firstorder.
    specialize (FA_model ax_mult_rec (d.:(fun _ => iO)) H).
    cbn in FA_model. now apply ext_model.
  Qed.


  Corollary add_hom x y : iμ (x + y) = iμ x i⊕ iμ y.
  Proof using ext_model FA_model.
    induction x.
    - now rewrite add_zero.
    - change (iσ iμ (x + y) = iσ iμ x i⊕ iμ y).
      now rewrite add_rec, IHx. 
  Qed.

  Corollary add_nat_to_model : forall x y z, x + y = z -> (iμ x i⊕ iμ y = iμ z).
  Proof using ext_model FA_model.
    intros x y z H. now rewrite <- add_hom, H.
  Qed.

  Corollary mult_hom x y : iμ (x * y) = iμ x i⊗ iμ y.
  Proof using ext_model FA_model.
    induction x.
    - now rewrite mult_zero.
    - change (iμ (y + x * y) = (iσ iμ x) i⊗ iμ y ).
      now rewrite add_hom, IHx, mult_rec.
  Qed.


  Corollary mult_nat_to_model : forall z x y, x * y = z -> (iμ x i⊗ iμ y = iμ z).
  Proof using ext_model FA_model.
    intros x y z H. now rewrite <- mult_hom, H.
  Qed.



End FA_models.

Arguments iμ {_ _} _.


(** ** The standard model *)

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
    all: cbn; try congruence. inversion H.
  Qed.

  Lemma nat_is_Q_model : forall rho phi,  List.In phi Qeq -> sat interp_nat rho phi.
  Proof.
    intros rho phi. intros H.
    repeat (destruct H as [<- | H]; auto).
    all: cbn; try congruence.
    2: inversion H.
    induction d. now left.
    right. destruct IHd.
    exists 0. congruence.
    exists d. reflexivity.
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
    all: cbn; try congruence. inversion H.
    apply nat_induction.
  Qed.


End StdModel.
