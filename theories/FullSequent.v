(* ** Full Intuitionistic First-Order Completeness *)

(* *** Full Intuitionistic Sequent Calculus *)

From Undecidability.FOLC Require Export FullFOL.

Section FullSequent.
  Context {Sigma : Signature}.

  Inductive fprv : list form -> form -> Prop :=
    (* Structural Rules *)
  | Ax A phi : fprv (phi :: A) phi
  | Contr A phi psi : fprv (phi :: phi :: A) psi -> fprv (phi :: A) psi
  | Weak A phi psi : fprv A psi -> fprv (phi :: A) psi
  | Perm A A' phi psi chi : fprv (A ++ psi :: phi :: A') chi -> fprv (A ++ phi :: psi :: A') chi
    (* Logical rules *)
  | Exp A phi : fprv A ⊥ -> fprv A phi
  | IL A phi psi chi : fprv A phi -> fprv (psi :: A) chi -> fprv (phi --> psi :: A) chi
  | IR A phi psi : fprv (phi :: A) psi -> fprv A (phi --> psi)
  | AL A phi psi chi : fprv (phi :: psi :: A) chi -> fprv (Conj phi psi :: A) chi
  | AR A phi psi : fprv A phi -> fprv A psi -> fprv A (Conj phi psi)
  | OL A phi psi chi : fprv (phi :: A) chi -> fprv (psi :: A) chi -> fprv (Disj phi psi :: A) chi
  | OR1 A phi psi : fprv A phi -> fprv A (Disj phi psi)
  | OR2 A phi psi : fprv A psi -> fprv A (Disj phi psi)
  | AllL A phi psi t : fprv (phi [t .: ids] :: A) psi -> fprv (∀ phi :: A) psi
  | AllR A phi : fprv (map (subst_form form_shift) A) phi -> fprv A (∀ phi)
  | ExL A phi psi : fprv (phi :: map (subst_form form_shift) A) (subst_form form_shift psi) -> fprv (∃ phi :: A) psi
  | ExR A phi t : fprv A (phi [t .: ids]) -> fprv A (∃ phi).
  Notation "A ⊢f phi" := (fprv A phi) (at level 30).

  Hint Constructors fprv.

  (* **** Context management and Weakening *)

  Lemma ctx_out A A' phi psi :
    (phi :: A ++ A') ⊢f psi -> (A ++ phi :: A') ⊢f psi.
  Proof.
    intros H. enough (H' : forall B B', rev B ++ B' = A -> (rev B ++ phi :: B' ++ A') ⊢f psi).
    { specialize (H' (rev A) nil). rewrite rev_involutive in H'. apply H', app_nil_r. }
    induction B; intros B' <-; cbn in *.
    - assumption.
    - rewrite <- app_assoc; cbn. apply Perm. apply (IHB (a :: B')). now rewrite <- app_assoc.
  Qed.

  Lemma ctx_in A A' phi psi :
    (A ++ phi :: A') ⊢f psi -> (phi :: A ++ A') ⊢f psi.
  Proof.
    intros H. enough (H' : forall B B', rev B' ++ B = A -> (rev B' ++ phi :: B ++ A') ⊢f psi).
    { now apply (H' A nil). }
    induction B; intros B' <-; cbn in *.
    - now rewrite <- (app_nil_r (rev B')).
    - apply Perm. specialize (IHB (a :: B')); cbn in *; repeat (rewrite <- app_assoc in IHB).
      now apply IHB.
  Qed.

  Lemma focus_el A phi psi :
    phi el A -> (phi :: A) ⊢f psi -> A ⊢f psi.
  Proof.
    intros (B & B' & ->) % in_split H. rewrite app_comm_cons in H.
    apply ctx_out, Contr. now apply ctx_in in H.
  Qed.

  Ltac focus t := refine (@focus_el _ t _ _ _); [eauto |].

  Lemma weaken A B phi :
    A ⊢f phi -> A <<= B -> B ⊢f phi.
  Proof.
    intros H; revert B; induction H; intros B H';
    lazymatch goal with
    | [ _ : (?f :: ?A) <<= ?B |- _ ] => focus f
    | _ => idtac
    end; eauto. 2,3,4,5,7: apply cons_incl in H'.
    - apply IHfprv. transitivity (A ++ phi :: psi :: A').
      intros a [? | [-> | [-> | ?]]] % in_app_or; apply in_or_app. all: eauto.
    - apply IL; [apply (IHfprv1 B) | apply (IHfprv2 (psi :: B))]; intuition.
    - apply AL, (IHfprv (phi :: psi :: B)). intuition.
    - apply OL; [apply (IHfprv1 (phi :: B)) | apply (IHfprv2 (psi :: B))]; intuition.
    - refine (AllL (IHfprv (phi [t..] :: B) _)). intuition.
    - apply ExL, (IHfprv (phi :: [p ⟨↑⟩ | p ∈ B])). now apply incl_shift, incl_map.
    - now apply AllR,IHfprv, incl_map.
  Qed.

  (* **** Renaming Weakening and Nameless Equivalence *)

  Theorem subst_Weak A phi xi :
    A ⊢f phi -> [phi[xi] | phi ∈ A] ⊢f phi[xi].
  Proof.
    induction 1 in xi |-*; comp; eauto using in_map.
    - specialize (IHfprv xi). rewrite map_app in *. cbn in *. now apply Perm.
    - apply AllL with (t := subst_term xi t); specialize (IHfprv xi); now asimpl in *.
    - apply AllR. setoid_rewrite map_map in IHfprv. erewrite map_map, map_ext.
      apply IHfprv. intros ?. comp. now apply ext_form.
   - apply ExL. specialize (IHfprv (var_term 0 .: (xi >> subst_term form_shift))). rewrite map_map in *.
     erewrite map_ext. comp. apply IHfprv. intros ?. comp. now apply ext_form.
  - apply ExR with (t := subst_term xi t); specialize (IHfprv xi); now asimpl in *.
  Qed.

  Definition cycle_shift n x :=
    if Dec (n = x) then var_term 0 else var_term (S x).

  Hint Unfold cycle_shift.

  Lemma cycle_shift_shift n phi :
    unused n phi -> phi[cycle_shift n] = phi[↑].
  Proof.
    intros H. apply (subst_unused_single H). intros m ?. unfold cycle_shift. now decide (n = m).
  Qed.

  Lemma cycle_shift_subject n phi :
    unused (S n) phi -> phi[(var_term n)..][cycle_shift n] = phi.
  Proof.
    intros H. asimpl. rewrite (@subst_unused_single _ _ ids _ _ H). 1: now asimpl.
    intros m H'; comp; decide (n = n); try congruence. destruct m; [reflexivity |].
      comp; decide (n = m); comp; congruence.
  Qed.

  Lemma nameless_equiv A phi n :
    unused_L n A -> unused (S n) phi -> ((A ⊢f phi[(var_term n)..]) <-> [phi[↑] | phi ∈ A] ⊢f phi).
  Proof.
    intros HL Hphi. split.
    - intros H % (subst_Weak (cycle_shift n)). rewrite cycle_shift_subject,
        (map_ext_in _ (subst_form form_shift)) in H. 1,3: assumption. intros ? ? % HL.
      now apply cycle_shift_shift.
    - intros H % (subst_Weak ((var_term n)..)). rewrite map_map in *. rewrite (map_ext _ id), map_id in H.
      assumption. now intuition comp.
  Qed.

  Lemma nameless_equiv' A psi phi n :
    unused_L n (phi :: A) -> unused (S n) psi ->
    ((psi[(var_term n)..] :: A) ⊢f phi) <-> ((psi :: [phi[↑] | phi ∈ A]) ⊢f phi[↑]).
  Proof.
    intros HL Hphi. split.
    - intros H % (subst_Weak (cycle_shift n)); cbn in *.
      rewrite (map_ext_in _ (subst_form form_shift)), cycle_shift_subject, cycle_shift_shift in H.
      1,3: assumption. apply HL; intuition.
      intros a Ha. specialize (HL a (or_intror Ha)). now rewrite cycle_shift_shift.
    - intros H % (subst_Weak ((var_term n)..)). cbn in *. rewrite map_map, (map_ext _ id), map_id in H.
      1: now asimpl in H. intros; now comp.
  Qed.

  (* **** Big Or Lemmas *)

  Fixpoint big_or (A : list form) : form :=
    match A with
    | cons phi A' => phi ∨ big_or A'
    | nil => ⊥
    end.
  Notation "⋁ A" := (big_or A) (at level 20).

  Lemma or_subst A rho :
    subst_form rho (⋁ A) = ⋁ (map (subst_form rho) A).
  Proof.
    induction A; cbn; asimpl; congruence.
  Qed.

  Lemma context_shift A phi n :
    unused_L (S n) A -> unused n phi ->
    (A ⊢f phi[↑]) <-> [ psi[(var_term n)..] | psi ∈ A] ⊢f phi.
  Proof.
    intros HL Hphi. split.
    - intros H % (subst_Weak ((var_term n)..)). comp. now asimpl in H.
    - intros H % (subst_Weak (cycle_shift n)). rewrite map_map in *.
      rewrite (map_ext_in _ id), map_id, cycle_shift_shift in H. 1-2: assumption.
      intros ? ? % HL. rewrite cycle_shift_subject; unfold id; tauto.
  Qed.

  Ltac use_free H := try intros ? ?; apply H; [omega | intuition].

  Lemma or_char A B phi :
    A ⊢f (⋁ B) -> (forall psi A', psi el B -> A' ⊢f psi -> A' ⊢f phi) -> A ⊢f phi.
  Proof.
    enough (H : forall a, A ⊢f a -> forall B, a = (⋁ B) -> forall phi, (forall psi A', psi el B -> A' ⊢f psi -> A' ⊢f phi) ->
              A ⊢f phi) by (intros H' H''; apply (H _ H' B eq_refl phi H'')). clear B phi.
    intros a; induction 1; intros B Heq goal Hgoal; try (destruct B; discriminate); subst; try eauto using fprv.
    - induction B; cbn.
      + apply Exp, Ax.
      + apply OL; [refine (Hgoal a _ _ (Ax _ _)) | apply IHB]; firstorder.
    - destruct B; [discriminate |]. injection Heq. intros _ ->. apply (Hgoal f A); intuition.
    - destruct B; [discriminate| injection Heq; intros -> ->]. apply (IHfprv B eq_refl goal). firstorder.
    - apply ExL. apply (IHfprv _ (or_subst B form_shift)). intros ? A' [psi [<- Hin]] % in_map_iff Hprv.
      destruct (find_unused_L (goal :: psi :: A')) as [x Hx].
      apply context_shift with (n := x) in Hprv; [| use_free Hx | use_free Hx ]. specialize (Hgoal _ _ Hin Hprv).
      now apply context_shift with (n := x) in Hgoal; [| use_free Hx | use_free Hx ].
  Qed.

  Lemma or_el A phi B :
    A ⊢f phi -> phi el B -> A ⊢f (⋁ B).
  Proof.
    intros Hprv Hel. induction B; destruct Hel; subst; cbn; eauto using fprv.
  Qed.

  Lemma or_weak A B B' :
    A ⊢f (⋁ B) -> B <<= B' -> A ⊢f (⋁ B').
  Proof.
    intros H Hsub. apply (or_char H). intros psi A' Hel Hpsi. apply or_el with (phi := psi); intuition.
  Qed.

  Lemma or_single A B phi :
    A ⊢f (⋁ B) -> (forall psi, psi el B -> psi = phi) -> A ⊢f phi.
  Proof.
    intros H H'. apply (or_char H). now intros psi A' -> % H'.
  Qed.
End FullSequent.

Notation "A ⊢f phi" := (fprv A phi) (at level 30).
Notation "⋁ A" := (big_or A) (at level 20).
Ltac use_free H := try intros ? ?; apply H; [omega | intuition].
