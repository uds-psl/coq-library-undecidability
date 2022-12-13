From Undecidability.FOL Require Import Syntax.Facts Semantics.Tarski.FullFacts.
Require Import Undecidability.FOL.Arithmetics.FA.
Require Import Undecidability.FOL.Arithmetics.Signature.
Require Import Undecidability.FOL.Arithmetics.Problems.
Require Import Lia List Vector.
Import Vector.VectorNotations.

Set Default Proof Using "Type".

Local Set Implicit Arguments.
Local Unset Strict Implicit.

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
  Arguments FA_model _ _ _ : clear implicits.

  (* # <a id="imu" /> #*)
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


Section PA_to_Q.

  Variable D : Type.
  Variable I : interp D.
  Notation "⊨ phi" := (forall rho, rho ⊨ phi) (at level 21).
  Variable axioms : forall ax, PAeq ax -> ⊨ ax.

  Lemma sat_Qeq : (forall ax, List.In ax Qeq -> ⊨ ax).
  Proof using axioms.
    intros x [<- |[<- |[<- |[<- |[<- |[<- |[<- |[<- |[<- |[<- |[<- |[<- |[<- |[]]]]]]]]]]]]]].
    1-10: apply axioms; apply PAeq_FA; cbn; eauto 15; fail.
    - apply axioms. apply PAeq_discr.
    - apply axioms. apply PAeq_inj.
    - intros ρ d. unfold ax_cases. evar (phi : form).
      specialize (axioms (PAeq_induction phi)) as Hax. cbn in Hax. apply Hax.
      + cbn. left. specialize (@axioms (∀ $0 == $0)). unshelve eapply axioms. 1:easy.
        apply PAeq_FA; cbn; eauto 15.
      + intros dd _. cbn. right. exists dd.
        specialize (@axioms (∀ $0 == $0)). unshelve eapply axioms. 1:easy.
        apply PAeq_FA; cbn; eauto 15.
  Qed.

End PA_to_Q.


