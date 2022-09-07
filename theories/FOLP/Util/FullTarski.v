(* ** Definition of Tarski Semantics *)

From Undecidability.FOLP Require Export FullFOL.
Require Import Undecidability.Shared.ListAutomation.
Import ListAutomationHints.

(* *** Tarki Models **)

Section Tarski.
  Local Notation "x 'el' L" := (In x L) (at level 60).
  Context {Sigma : Signature}.

  (* **** Semantic notions *)

  Section Semantics.
    Variable domain : Type.

    Class interp := B_I
      {
        i_f : forall f : Funcs, Vector.t domain (fun_ar f) -> domain ;
        i_P : forall P : Preds, Vector.t domain (pred_ar P) -> Prop ;
      }.

    Definition env := nat -> domain.

    Context {I : interp }.
    Fixpoint eval (rho : env) (t : term) : domain :=
      match t with
      | var_term s => rho s
      | Func f v => i_f (Vector.map (eval rho) v)
      end.

    Fixpoint sat (rho : env) (phi : form) : Prop :=
      match phi with
      | Pred P v => i_P (Vector.map (eval rho) v)
      | Fal => False
      | Impl phi psi => sat rho phi -> sat rho psi
      | Conj phi psi => sat rho phi /\ sat rho psi
      | Disj phi psi => sat rho phi \/ sat rho psi
      | Ex phi => exists d : domain, sat (d .: rho) phi
      | All phi => forall d : domain, sat (d .: rho) phi
      end.

  End Semantics.

  Arguments sat  {_ _} _ _, _ _ _ _.

  Notation "rho ⊨ phi" := (sat rho phi) (at level 20).

  Fixpoint list_or (A : list form) : form :=
    match A with 
    | nil => ⊥
    | phi::A => phi ∨ list_or A
    end.

  Lemma list_or_spec A D (I : interp D) rho :
    rho ⊨ list_or A <-> exists phi, phi el A /\ rho ⊨ phi.
  Proof.
    induction A; cbn; split; auto.
    - firstorder.
    - intros [H|H].
      + exists a. tauto.
      + apply IHA in H as [phi[H1 H2]]. exists phi. tauto.
    - intros [phi [[->|H1] H]]; auto.
      right. apply IHA. now exists phi.
  Qed.

  Definition constraint := forall D, interp D -> Prop.
  Definition con_subs (C C' : constraint) := (forall D (I : interp D), C' D I -> C D I).
  Definition classical D (I : interp D) :=
    forall rho phi psi, rho ⊨ (((phi --> psi) --> phi) --> phi).

  Definition has_model (C : constraint) (T : theory) :=
    exists D (I : interp D) rho, (forall phi, phi ∈ T -> rho ⊨ phi) /\ C D I.
  Definition valid_T (C : constraint) (T : theory) (phi : form) :=
    forall D (I : interp D), C D I -> forall rho, (forall psi, psi ∈ T -> rho ⊨ psi) -> rho ⊨ phi.
  Definition valid_L (C : constraint) A phi :=
    forall D (I : interp D), C D I -> forall rho, (forall psi, psi el A -> rho ⊨ psi) -> rho ⊨ phi.

  Notation "T '⊫<' C '>' phi" := (valid_T C T phi) (at level 50).

  (*Lemma sat_and_iff D (I : interp D) rho phi psi :
    classical I -> sat rho phi /\ sat rho psi <-> sat rho (phi ∧ psi).
  Proof.
    cbn. repeat split. intuition. specialize (H rho phi ⊥). cbn in H. tauto. intuition. tauto. firstorder.
  Qed.*)

  (* **** Model relationships **)

  Lemma valid_T_subsumption (C C' : constraint) T phi :
    con_subs C C' -> valid_T C T phi -> valid_T C' T phi.
  Proof.
    firstorder.
  Qed.

  (* **** Substitution properties **)

  Section Substs.
    Variable D : Type.
    Variable I : interp D.

    Hint Unfold funcomp : core.

    Lemma eval_ext rho xi t :
      (forall x, rho x = xi x) -> eval rho t = eval xi t.
    Proof.
      intros H; induction t using strong_term_ind; comp; try congruence.
      f_equal. now apply vec_map_ext. 
    Qed.

    Lemma eval_comp rho xi t :
      eval rho (subst_term xi t) = eval (xi >> eval rho) t.
    Proof.
      induction t using strong_term_ind; comp; try congruence.
      f_equal. erewrite vec_comp. 2: reflexivity. now apply vec_map_ext.
    Qed.

    Lemma sat_ext rho xi phi :
      (forall x, rho x = xi x) -> rho ⊨ phi <-> xi ⊨ phi.
    Proof.
      induction phi in rho, xi |-*; intros Hext; comp.
      - tauto.
      - now rewrite (vec_ext (fun x => eval_ext x Hext)).
      - now erewrite IHphi1, IHphi2.
      - now erewrite IHphi1, IHphi2.
      - now erewrite IHphi1, IHphi2.
      - split; intros H' d; eapply (IHphi (d .: rho) (d .: xi) _), H'.
        Unshelve. all: (intros []; cbn; congruence).
      - split; intros [d H']; exists d; eapply (IHphi (d .: rho) (d .: xi) _), H'.
        Unshelve. all: (intros []; cbn; congruence).
    Qed.

    Lemma sat_comp rho xi phi :
      rho ⊨ (subst_form xi phi) <-> (xi >> eval rho) ⊨ phi.
    Proof.
      induction phi in rho, xi |-*; comp.
      - tauto.
      - erewrite vec_comp. 2: reflexivity. now rewrite (vec_ext (fun x => eval_comp rho xi x)).
      - now rewrite IHphi1, IHphi2.
      - now rewrite IHphi1, IHphi2.
      - now rewrite IHphi1, IHphi2.
      - setoid_rewrite IHphi. split; intros H d; eapply sat_ext. 2, 4: apply (H d).
        all: intros []; comp; rewrite? eval_comp; now comp.
      - setoid_rewrite IHphi. split; intros [d H]; exists d; eapply sat_ext. 2, 4: apply H.
        all: intros []; comp; rewrite? eval_comp; now comp.
    Qed.

    Lemma sat_subst rho sigma phi :
      (forall x, eval rho (sigma x) = rho x) -> rho ⊨ phi <-> rho ⊨ (subst_form sigma phi).
    Proof.
      intros Hsigma. rewrite sat_comp. apply sat_ext. now comp.
    Qed.
  End Substs.

End Tarski.

Arguments sat  {_ _ _} _ _, _ _ _ _ _.
Notation "rho ⊨ phi" := (sat rho phi) (at level 20).

Arguments valid_T {_} _ _ _.
Notation "T '⊫<' C '>' phi" := (valid_T C T phi) (at level 50).
