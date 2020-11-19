(** * Tarski Semantics *)

Require Export Undecidability.FOL.Util.Syntax.
Import ListAutomationNotations.
Require Import Vector.

Local Set Implicit Arguments.
Local Unset Strict Implicit.

(*** Fragment Syntax ***)

Inductive full_logic_binop : Type :=
(*| Conj : full_logic_binop
| Disj : full_logic_binop*)
| Impl : full_logic_binop.

Inductive full_logic_quant : Type :=
| All : full_logic_quant
(*| Ex : full_logic_quant*).

Instance full_operators : operators :=
{| binop := full_logic_binop ; quantop := full_logic_quant |}.

Notation "∀ Phi" := (quant All Phi) (at level 50).
(*Notation "∃ Phi" := (quant Ex Phi) (at level 50).
Notation "A ∧ B" := (bin Conj A B) (at level 41).
Notation "A ∨ B" := (bin Disj A B) (at level 42).*)
Notation "A '-->' B" := (bin Impl A B) (at level 43, right associativity).

Section fixb.

  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.
  Context {ff : falsity_flag}.
  
  Fixpoint impl (A : list form) phi :=
    match A with
    | [] => phi
    | psi :: A => bin Impl psi (impl A phi)
    end.

End fixb.



(*** Tarski Semantics ***)

Section Tarski.

  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.

  (** Semantic notions *)

  Section Semantics.

    Variable domain : Type.

    Class interp := B_I
      {
        i_f : forall f : syms, vec domain (ar_syms f) -> domain ;
        i_P : forall P : preds, vec domain (ar_preds P) -> Prop ;
      }.

    Definition env := nat -> domain.

    Context {I : interp}.

    Fixpoint eval (rho : env) (t : term) : domain :=
      match t with
      | var s => rho s
      | func f v => i_f (Vector.map (eval rho) v)
      end.

    Fixpoint sat {ff : falsity_flag} (rho : env) (phi : form) : Prop :=
      match phi with
      | atom P v => i_P (Vector.map (eval rho) v)
      | falsity => False
      | bin Impl phi psi => sat rho phi -> sat rho psi
      (*| bin Conj phi psi => sat rho phi /\ sat rho psi
      | bin Disj phi psi => sat rho phi \/ sat rho psi
      | quant Ex phi => exists d : domain, sat (d .: rho) phi*)
      | quant All phi => forall d : domain, sat (d .: rho) phi
      end.

  End Semantics.

  Notation "rho ⊨ phi" := (sat rho phi) (at level 20).
  
  Section Substs.
    
    Variable D : Type.
    Variable I : interp D.
        
    Lemma eval_ext rho xi t :
      (forall x, rho x = xi x) -> eval rho t = eval xi t.
    Proof.
      intros H. induction t; cbn.
      - now apply H.
      - f_equal. apply map_ext_in. now apply IH.
    Qed.

    Lemma eval_comp rho xi t :
      eval rho (subst_term xi t) = eval (xi >> eval rho) t.
    Proof.
      induction t; cbn.
      - reflexivity.
      - f_equal. rewrite map_map. apply map_ext_in, IH.
    Qed.

    Lemma sat_ext {ff : falsity_flag} rho xi phi :
      (forall x, rho x = xi x) -> rho ⊨ phi <-> xi ⊨ phi.
    Proof.
      induction phi in rho, xi |- *; cbn; intros H.
      - reflexivity.
      - erewrite map_ext; try reflexivity. intros t. now apply eval_ext.
      - specialize (IHphi1 rho xi). specialize (IHphi2 rho xi). destruct b0; intuition.
      - destruct q.
        + split; intros H' d; eapply IHphi; try apply (H' d). 1,2: intros []; cbn; intuition.
        (* + split; intros [d H']; exists d; eapply IHphi; try apply H'. all: intros []; cbn; intuition.*)
    Qed.

    Lemma sat_ext' {ff : falsity_flag} rho xi phi :
      (forall x, rho x = xi x) -> rho ⊨ phi -> xi ⊨ phi.
    Proof.
      intros Hext H. rewrite sat_ext. exact H.
      intros x. now rewrite (Hext x).
    Qed.

    Lemma sat_comp {ff : falsity_flag} rho xi phi :
      rho ⊨ (subst_form xi phi) <-> (xi >> eval rho) ⊨ phi.
    Proof.
      induction phi in rho, xi |- *; cbn.
      - reflexivity.
      - erewrite map_map, map_ext; try reflexivity. intros t. apply eval_comp.
      - specialize (IHphi1 rho xi). specialize (IHphi2 rho xi). destruct b0; intuition.
      - destruct q.
        + setoid_rewrite IHphi. split; intros H d; eapply sat_ext. 2, 4: apply (H d).
          all: intros []; cbn; trivial; now setoid_rewrite eval_comp.
        (* + setoid_rewrite IHphi. split; intros [d H]; exists d; eapply sat_ext. 2, 4: apply H.
          all: intros []; cbn; trivial; now setoid_rewrite eval_comp.*)
    Qed.

    Lemma sat_subst {ff : falsity_flag} rho sigma phi :
      (forall x, eval rho (sigma x) = rho x) -> rho ⊨ phi <-> rho ⊨ (subst_form sigma phi).
    Proof.
      intros H. rewrite sat_comp. apply sat_ext. intros x. now rewrite <- H.
    Qed.

    Lemma sat_single {ff : falsity_flag} (rho : nat -> D) (Phi : form) (t : term) :
      (eval rho t .: rho) ⊨ Phi <-> rho ⊨ subst_form (t..) Phi.
    Proof.
      rewrite sat_comp. apply sat_ext. now intros [].
    Qed.

    
  End Substs.

End Tarski.

Arguments sat {_ _ _ _ _} _ _, {_ _ _} _ {_} _ _.
Arguments interp {_ _} _, _ _ _.

Notation "p ⊨ phi" := (sat _ p phi) (at level 20).

Section Defs.

  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.
  Context {ff : falsity_flag}.

  Definition valid_ctx A phi := forall D (I : interp D) rho, (forall psi, psi el A -> rho ⊨ psi) -> rho ⊨ phi.
  Definition valid phi := forall D (I : interp D) rho, rho ⊨ phi.
  (*Definition valid_L A := forall D (I : interp D) rho, rho ⊫ A.*)
  Definition satis phi := exists D (I : interp D) rho, rho ⊨ phi.
  (*Definition fullsatis A := exists D (I : interp D) rho, rho ⊫ A.*)

End Defs.


(** Trivial Model *)

Section TM.

  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.

  Instance TM : interp unit :=
    {| i_f := fun _ _ => tt; i_P := fun _ _ => True; |}.

  Fact TM_sat (rho : nat -> unit) (phi : form falsity_off) :
    rho ⊨ phi.
  Proof.
    revert rho. remember falsity_off as ff. induction phi; cbn; trivial.
    - discriminate.
    - destruct b0; auto.
    - destruct q; firstorder.
  Qed.

End TM.




