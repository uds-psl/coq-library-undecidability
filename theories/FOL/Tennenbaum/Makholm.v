From Undecidability.Synthetic Require Import Definitions.
From Undecidability.FOL Require Import FullSyntax.
From Undecidability.FOL.Arithmetics Require Import Signature PA DeductionFacts.
From Undecidability.FOL.Syntax Require Import Theories.
From Undecidability.FOL.Tennenbaum Require Import Peano.
From Undecidability.FOL.Tennenbaum.Utils Require Import DN.
Require Import List Lia.
Import Vector.VectorNotations.
Require Import Setoid Morphisms.


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

  Definition iless x y := exists d : D, y i= iσ (x i⊕ d).
  Notation "x 'i⧀' y" := (iless x y) (at level 80).


  (* We assume that there is a binary formula which can be used for coding. *)

  Variable γ : form.
  Variable Hγ : bounded 2 γ.
  Definition obj_Coding := forall α, bounded 1 α -> PA ⊢TI ∀¬¬∃∀ $0 ⧀ $2 → α ↔ γ.
  Hypothesis coding : obj_Coding.

  (** * HA-inseparable formulas. *)

  Definition def_obj_Insep α β :=
    bounded 1 α /\ bounded 1 β /\
      ( PA ⊢TI ¬ ∃ α ∧ β ) /\
      (forall G,
          decidable G -> (forall n, Q ⊢I α[(num n)..] -> G n) ->
          (forall n, ~ (Q ⊢I β[(num n)..] /\ G n)) -> False).

  Hypothesis obj_Insep : exists α β, def_obj_Insep α β.

  (** * 
    We show a sliglty more general version of Makholm's statement. 
    This is then later instantiated for the case where γ is the 
    formula which expresses divisibility by prime numbers. 
  *)

  Definition gamma d n := forall ρ, (d .: ρ) ⊨ γ[(num n)..].

  Lemma num_lt_nonStd n d : 
    ~ std d -> inu I n i⧀ d.
  Proof.
  Admitted.

  Theorem Makholm :
    @nonStd D I -> ~~ exists d, ~ decidable (gamma d).
  Proof.
    destruct obj_Insep as (α & β & Ha1 & Hb1 & Disj & Insepa).
    intros [e Nstd_e].
    specialize (coding Ha1).
    eapply tsoundness with (rho:= (fun _ => e)) in coding.
    - cbn in coding. specialize (@coding e).
      DN.bind coding.
      specialize coding as [c Hc].
      assert (forall n : nat, (fun _ => inu I n) ⊨ α <-> (inu I n .: (fun _ => c)) ⊨ γ).
      + intros n. split.
        --  specialize (Hc (inu I n)) as [H _].
            rewrite extensional.
            apply num_lt_nonStd.
            intros X_n. destruct H as [d Hd].
          ++  eapply bound_ext; [eauto| |apply X_n].
              intros []; solve_bounds.
          ++  exists d. split. 2: apply Hd.
              eapply bound_ext; [apply Hψ| |apply Hd].
              intros [|[]]; solve_bounds.
        --  specialize (Hc (inu n)) as [_ H].
            now apply num_lt_nonStd.
            intros [d Hd].
            eapply bound_ext; [eauto| |apply H].
            { intros [|[]]; solve_bounds. }
            exists d. split. 2: apply Hd.
            eapply bound_ext; [apply Hψ| |apply Hd].
            intros [|[]]; solve_bounds.
      + apply DN. exists c. intros [Dec_Div_c]. clear Hc.
        apply (Insepa (fun n => (fun _ => inu n) ⊨ α)).
        -- constructor. intros n.
           destruct (Dec_Div_c (Irred n)) as [h|h]; auto.
           ++ left. apply H, ψ_equiv; auto.
           ++ right. intros nh%H. apply h.
              apply ψ_equiv in nh; auto.
        --  intros n Hn%soundness.
            eapply sat_ext with (xi:= inu n .: (fun _ : nat => inu n)).
            1 : intros []; reflexivity.
            rewrite <-switch_num. apply Hn.
            intros ??; apply axioms. now constructor.
        --  intros n [Hb X_n].
            eapply tsoundness with (rho:= (fun _ => e)) in Disj; auto.
            cbn in Disj. apply Disj.
            exists (inu n). split.
            ++  eapply bound_ext; [eauto| |apply X_n].
                intros []; reflexivity || lia.
            ++  apply soundness in Hb.
                rewrite <-switch_num. apply Hb.
                intros ??. apply axioms. now constructor.
    - intros ??. now apply axioms.
  Admitted.

End Arithmetic.