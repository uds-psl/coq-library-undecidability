(** ** Enumeration of formulas and ND *)

From Undecidability.FOLC Require Export FOL.

(* **** Helper machinery **)

Lemma flat_map_app {X Y} A B (f : X -> list Y) :
  flat_map f (A ++ B) = flat_map f A ++ flat_map f B.
Proof.
  induction A; cbn.
  - reflexivity.
  - now rewrite IHA, app_assoc.
Qed.

Lemma switch_map {X Y} (P : Y -> Prop) (f : X -> Y) A :
  (forall x, x el A -> P (f x)) -> forall y, y el (map f A) -> P y.
Proof.
  intros H y (x & <- & Hx) % in_map_iff. eauto.
Qed.

Fixpoint at_pos {X} n x (A : list X) :=
  match A with
  | nil => False
  | a :: A' =>
    match n with
    | O => a = x
    | S n' => at_pos n' x A'
    end
  end.

Lemma el_at_pos {X} x (A : list X) :
  x el A <-> exists n, at_pos n x A.
Proof.
  induction A.
  - split. intuition. intros [ [] [] ].
  - split.
    + intros [-> | H].
      * now exists 0.
      * apply IHA in H as [n H']. now exists (S n).
    + intros [ [] H].
      * now left.
      * right. apply IHA. now exists n.
Qed.

(* **** Unused variables in the enumeration *)

Section L_T_unused.
  Context {Sigma : Signature}.

  Hypothesis enum_Funcs : enumT Funcs.
  Hypothesis enum_Preds : enumT Preds.

  Lemma L_T_nat_le n m :
    n el L_T m -> n <= m.
  Proof.
    induction m.
    - intros []; now subst.
    - intros [ | [ | [] ] ] % in_app_or.
      + constructor. now apply IHm.
      + now subst.
  Qed.

  Lemma L_T_unused_t n m t :
    m <= n -> t el (L_T m) -> unused_term n t.
  Proof.
    revert n t. induction m; intros n t.
    - inversion 1; cbn; tauto.
    - intros H [ | [ | (A & H0 & (f & <- & Hf) % in_map_iff) % in_concat_iff ]] % in_app_or.
      * apply IHm. omega. assumption.
      * subst. constructor. omega.
      * revert H0. apply switch_map. intros v H'.  rewrite <- vecs_from_correct in H'. constructor.
        intros s Hs % H'. apply IHm. 1: omega. assumption.
  Qed.

  Lemma L_T_unused_v n m k (v : Vector.t term k) :
    m <= n -> v el (L_T m) -> (forall t, vec_in t v -> unused_term n t).
  Proof.
    induction m; intros Hnm.
    - intros [].
    - cbn. intros [ | H ] % in_app_or.
      + firstorder.
      + rewrite <- vecs_from_correct in H. intros t Ht. apply L_T_unused_t with m. all: omega + eauto.
  Qed.

  Lemma L_T_unused n m phi :
    m <= n -> phi el (L_T m) -> unused n phi.
  Proof.
    revert n phi. induction m; intros n phi.
    - intros ? [<- | []]. constructor.
    - intros H [ | [ | [ | [ (A & H0 & (P & <- & HP) % in_map_iff) % in_concat_iff | [] % in_app_or ] % in_app_or] % in_app_or]] % in_app_or;
        try (revert H0; apply switch_map).
      + apply IHm. omega. assumption.
      + subst. constructor.
      + contradiction H0.
      + intros v H'. constructor. intros. apply L_T_unused_v with m (pred_ar P) v. all: omega + eauto.
      + intros [phi1 phi2] [] % in_prod_iff. constructor.
        all: apply IHm; [omega | assumption].
      + intros psi H'. constructor. apply IHm. omega. assumption.
  Qed.
End L_T_unused.

(* **** Single value enumeration *)

Section Enumeration.
  Variable X : Type.
  Context {Henum : enumT X}.
  Context {Hdec : eq_dec X}.
  Hypothesis Hlen : forall n, | L_T n | > n.

  Definition plain_enum n : X := proj1_sig (@nthe_length X (L_T n) n (Hlen n)).

  Lemma L_T_sub n m :
    n <= m -> exists A, L_T m = L_T n ++ A.
  Proof.
    induction 1.
    - exists nil. now rewrite app_nil_r.
    - destruct IHle as [A HA]. destruct (cum_T m) as [B HB].
      exists (A ++ B). now rewrite HB, HA, app_assoc.
  Qed.

  Lemma L_T_sub_or n m :
    (exists A, L_T n = L_T m ++ A) \/ (exists A, L_T m = L_T n ++ A).
  Proof.
    destruct (Nat.le_ge_cases n m) as [Hl | Hl]; [right | left]; now apply L_T_sub.
  Qed.

  Lemma plain_enum_enumerates x :
    exists n, plain_enum n = x.
  Proof.
    destruct (el_T x) as [m H]. destruct (el_pos Hdec H) as [n H'].
    exists n. unfold plain_enum. destruct (nthe_length (Hlen n)) as [y H'']. cbn.
    apply pos_nthe in H'. destruct (L_T_sub_or n m) as [ [A HA] | [A HA] ].
    - rewrite HA in H''. apply (nthe_app_l A) in H'. congruence.
    - rewrite HA in H'. apply (nthe_app_l A) in H''. congruence.
  Qed.

  Lemma plain_enum_slow n :
    plain_enum n el L_T n.
  Proof.
    unfold plain_enum. destruct (nthe_length (Hlen n)) as [y H'']. cbn. now apply nth_error_In in H''.
  Qed.
End Enumeration.

(* **** Single step enumeration for formulas *)

Section L_T_Enumeration.
  Context {Sigma : Signature}.
  Context {HdF : eq_dec Funcs} {HdP : eq_dec Preds}.
  Context {HeF : enumT Funcs} {HeP : enumT Preds}.

  Lemma L_T_form_len n :
    | L_T form n | > n.
  Proof.
    induction n; cbn.
    - omega.
    - rewrite app_length. cbn. change (L_T n) with (L_form HeF HeP n) in IHn. omega.
  Qed.

  Definition form_enum n := plain_enum L_T_form_len n.

  Corollary form_enum_enumerates x :
    exists n, form_enum n = x.
  Proof. apply plain_enum_enumerates. intuition. Qed.

  Lemma form_enum_fresh n m :
    n <= m -> unused m (form_enum n).
  Proof.
    intros H. apply (@L_T_unused _ _ _ m n). exact H.
    apply plain_enum_slow.
  Qed.
End L_T_Enumeration.
