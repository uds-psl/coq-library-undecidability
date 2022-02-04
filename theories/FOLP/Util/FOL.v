(* ** Operations & Properties of FOL* *)

Require Import Undecidability.Shared.ListAutomation.
Import ListAutomationNotations.
From Coq Require Eqdep.
Require Import Arith Undecidability.Shared.Libs.PSL.Numbers List Setoid.
From Undecidability.Synthetic Require Export DecidabilityFacts EnumerabilityFacts ListEnumerabilityFacts ReducibilityFacts.
From Undecidability.FOLP Require Export Syntax unscoped.
Require Export Lia.

Set Default Proof Using "Type".

(* **** Notation *)

Notation "phi --> psi" := (Impl phi psi) (right associativity, at level 55).
Notation "∀ phi" := (All phi) (at level 56, right associativity).
Notation "⊥" := (Fal).
Notation "¬ phi" := (phi --> ⊥) (at level 20).
Notation "phi ∨ psi" := (¬ phi --> psi) (left associativity, at level 54).
Notation "phi ∧ psi" := (¬ (¬ phi ∨ ¬ psi)) (left associativity, at level 54).
Notation "∃ phi" := (¬ ∀ ¬ phi) (at level 56, right associativity).

Notation vector := Vector.t.
Import Vector.
Arguments nil {A}.
Arguments cons {A} _ {n}.

(* **** Tactics *)

Ltac capply H := eapply H; try eassumption.
Ltac comp := repeat (progress (cbn in *; autounfold in *; asimpl in *)).
#[export] Hint Unfold idsRen : core.

Ltac resolve_existT :=
  match goal with
     | [ H2 : existT _ _ _ = existT _ _ _ |- _ ] => rewrite (Eqdep.EqdepTheory.inj_pair2 _ _ _ _ _ H2) in *
  | _ => idtac
  end.

Ltac inv H :=
  inversion H; subst; repeat (progress resolve_existT).

Section FOL.
  Context {Sigma : Signature}.

  (* **** Subformula *)

  Inductive sf : form -> form -> Prop :=
  | SImplL phi psi : sf phi (phi --> psi)
  | SImplR phi psi : sf psi (phi --> psi)
  | SAll phi t : sf (phi [t .: ids]) (∀ phi).
  Hint Constructors sf : core.

  Lemma sf_acc phi rho :
    Acc sf (phi [rho]).
  Proof.
    revert rho; induction phi; intros rho; constructor; intros psi Hpsi; asimpl in *; inversion Hpsi;
      subst; asimpl in *; eauto.
  Qed.

  Lemma sf_well_founded :
    well_founded sf.
  Proof.
    intros phi. pose proof (sf_acc phi ids) as H. now asimpl in H.
  Qed.

  (* **** Formula size *)

  Fixpoint size (phi : form ) :=
    match phi with
    | Pred _ _ => 0
    | Fal => 0
    | Impl phi psi => S (size phi + size psi)
    | All phi => S (size phi)
    end.

  Lemma size_ind {X : Type} (f : X -> nat) (P : X -> Prop) :
    (forall x, (forall y, f y < f x -> P y) -> P x) -> forall x, P x.
  Proof.
    intros H x. apply H.
    induction (f x).
    - intros y. lia.
    - intros y. intros [] % le_lt_or_eq.
      + apply IHn; lia.
      + apply H. injection H0. now intros ->.
  Qed.

  Lemma subst_size rho phi :
    size (subst_form rho phi) = size phi.
  Proof.
    revert rho; induction phi; intros rho; cbn; asimpl; try congruence.
  Qed.

  Lemma form_ind_subst (P : form -> Prop) :
    P ⊥ -> (forall p v, P (Pred p v)) ->
    (forall phi psi, P phi -> P psi -> P (phi --> psi)) ->
    (forall phi, (forall t, P phi[t..]) -> P (∀ phi)) ->
    forall phi, P phi.
  Proof.
    intros H0 H1 H2 H3 phi.
    induction phi using (@size_induction _ size).
    destruct phi; trivial.
    - apply H2; apply H; cbn; lia.
    - apply H3. intros t. apply H.
      cbn. unfold subst1. rewrite subst_size. lia.
  Qed.

  (* **** Forall and Vector.t technology **)

  Inductive Forall (A : Type) (P : A -> Type) : forall n, vector A n -> Type :=
  | Forall_nil : Forall P (@Vector.nil A)
  | Forall_cons : forall n (x : A) (l : vector A n), P x -> Forall P l -> Forall P (@Vector.cons A x n l).

  Inductive vec_in (A : Type) (a : A) : forall n, vector A n -> Type :=
  | vec_inB n (v : vector A n) : vec_in a (cons a v)
  | vec_inS a' n (v :vector A n) : vec_in a v -> vec_in a (cons a' v).
  Hint Constructors vec_in : core.

  Lemma strong_term_ind' (p : term -> Type) :
    (forall x, p (var_term x)) -> (forall F v, (Forall p v) -> p (Func F v)) -> forall (t : term), p t.
  Proof.
    intros f1 f2. fix strong_term_ind' 1. destruct t as [n|F v].
    - apply f1.
    - apply f2. induction v.
      + econstructor.
      + econstructor. now eapply strong_term_ind'. eauto.
  Qed.  

  Lemma strong_term_ind (p : term -> Type) :
    (forall x, p (var_term x)) -> (forall F v, (forall t, vec_in t v -> p t) -> p (Func F v)) -> forall (t : term), p t.
  Proof.
    intros f1 f2. eapply strong_term_ind'.
    - apply f1.
    - intros. apply f2. intros t. induction 1; inv X; eauto.
  Qed.  
  
  (* **** Unused variable **)

  Inductive unused_term (n : nat) : term -> Prop :=
  | uft_var m : n <> m -> unused_term n (var_term m)
  | uft_Func F v : (forall t, vec_in t v -> unused_term n t) -> unused_term n (Func F v).

  Inductive unused (n : nat) : form -> Prop :=
  | uf_Fal : unused n Fal
  | uf_Pred P v : (forall t, vec_in t v -> unused_term n t) -> unused n (Pred P v)
  | uf_Impl phi psi : unused n phi -> unused n psi -> unused n (Impl phi psi)
  | uf_All phi : unused (S n) phi -> unused n (All phi).

  Definition unused_L n A := forall phi, List.In phi A -> unused n phi.
  Definition closed phi := forall n, unused n phi.

  Lemma vec_unused n (v : vector term n)  :
    (forall t, vec_in t v -> { n | forall m, n <= m -> unused_term m t }) ->
    { k | forall t, vec_in t v -> forall m, k <= m -> unused_term m t }.
  Proof.
    intros Hun. induction v in Hun |-*.
    - exists 0. intros n H. inv H.
    - destruct IHv as [k H]. 1: eauto. destruct (Hun h (vec_inB h v)) as [k' H'].
      exists (k + k'). intros t H2. inv H2; intros m Hm; [apply H' | apply H]; now try lia.
  Qed.

  Lemma find_unused_term t :
    { n | forall m, n <= m -> unused_term m t }.
  Proof.
    induction t using strong_term_ind.
    - exists (S x). intros m Hm. constructor. lia.
    - destruct (vec_unused X) as [k H]. exists k. eauto using unused_term.
  Qed.

  Lemma find_unused phi :
    { n | forall m, n <= m -> unused m phi }.
  Proof with eauto using unused.
    induction phi.
    - exists 0... 
    - destruct (@vec_unused _ t) as [k H]. 1: eauto using find_unused_term. exists k. eauto using unused.
    - destruct IHphi1, IHphi2. exists (x + x0). intros m Hm. constructor; [ apply u | apply u0 ]; lia.
    - destruct IHphi. exists x. intros m Hm. constructor. apply u. lia.
  Qed.

  Lemma find_unused_L A :
    { n | forall m, n <= m -> unused_L m A }.
  Proof.
    induction A.
    - exists 0. unfold unused_L. firstorder.
    - destruct IHA. destruct (find_unused a).
      exists (x + x0). intros m Hm. intros phi []; subst.
      + apply u0. lia.
      + apply u. lia. auto.
  Qed.

  Definition capture n phi := nat_rect _ phi (fun _ => All) n.

  Lemma capture_captures n m phi :
    (forall i, n <= i -> unused i phi) -> (forall i, n - m <= i -> unused i (capture m phi)).
  Proof.
    intros H. induction m; cbn; intros i Hi.
    - rewrite <- minus_n_O in *. intuition.
    - constructor. apply IHm. lia.
  Qed.

  Definition close phi := capture (proj1_sig (find_unused phi)) phi.

  Lemma close_closed phi :
    closed (close phi).
  Proof.
    intros n. unfold close. destruct (find_unused phi) as [m Hm]; cbn.
    apply (capture_captures Hm). lia.
  Qed.

  Fixpoint big_imp A phi :=
    match A with
    | List.nil => phi
    | a :: A' => a --> (big_imp A' phi)
    end.

  (* **** Substituting unused variables *)

  Definition shift_P P n :=
    match n with
    | O => False
    | S n' => P n'
    end.

  Lemma vec_map_ext X Y (f g : X -> Y) n (v : vector X n) :
    (forall x, vec_in x v -> f x = g x) -> map f v = map g v.
  Proof.
    intros Hext; induction v in Hext |-*; cbn.
    - reflexivity.
    - rewrite IHv, (Hext h). 1: reflexivity. all: eauto.
  Qed.

  Lemma subst_unused_term xi sigma P t :
    (forall x, dec (P x)) -> (forall m, ~ P m -> xi m = sigma m) -> (forall m, P m -> unused_term m t) ->
    subst_term xi t = subst_term sigma t.
  Proof.
    intros Hdec Hext Hunused. induction t using strong_term_ind; cbn; asimpl.
    - destruct (Hdec x) as [H % Hunused | H % Hext].
      + inversion H; subst; congruence.
      + congruence.
    - f_equal. apply vec_map_ext. intros t H'. apply (H t H'). intros n H2 % Hunused. inv H2. eauto.
  Qed.

  Lemma subst_unused_form xi sigma P phi :
    (forall x, dec (P x)) -> (forall m, ~ P m -> xi m = sigma m) -> (forall m, P m -> unused m phi) ->
    subst_form xi phi = subst_form sigma phi.
  Proof.
    induction phi in xi,sigma,P |-*; intros Hdec Hext Hunused; cbn; asimpl.
    - reflexivity.
    - f_equal. apply vec_map_ext. intros s H. apply (subst_unused_term Hdec Hext).
      intros m H' % Hunused. inv H'. eauto.
    - rewrite IHphi1 with (sigma := sigma) (P := P). rewrite IHphi2 with (sigma := sigma) (P := P).
      all: try tauto. all: intros m H % Hunused; now inversion H.
    - erewrite IHphi with (P := shift_P P). 1: reflexivity.
      + intros [| x]; [now right| now apply Hdec].
      + intros [| m]; [reflexivity|]. intros Heq % Hext; unfold ">>"; cbn; congruence.
      + intros [| m]; [destruct 1| ]. intros H % Hunused; now inversion H.
  Qed.

  Lemma subst_unused_single xi sigma n phi :
    unused n phi -> (forall m, n <> m -> xi m = sigma m) -> subst_form xi phi = subst_form sigma phi.
  Proof.
    intros Hext Hunused. apply subst_unused_form with (P := fun m => n = m). all: intuition.
    now subst.
  Qed.

  Lemma subst_unused_range xi sigma phi n :
    (forall m, n <= m -> unused m phi) -> (forall x, x < n -> xi x = sigma x) -> subst_form xi phi = subst_form sigma phi.
  Proof.
    intros Hle Hext. apply subst_unused_form with (P := fun x => n <= x); [apply le_dec| |assumption].
    intros ? ? % not_le; intuition.
  Qed.

  Lemma subst_unused_closed xi sigma phi :
    closed phi -> subst_form xi phi = subst_form sigma phi.
  Proof.
    intros Hcl. apply subst_unused_range with (n := 0); intuition. lia.
  Qed.

  Lemma subst_unused_closed' xi phi :
    closed phi -> subst_form xi phi = phi.
  Proof.
    intros Hcl. rewrite <- idSubst_form with (sigmaterm := ids).
    apply subst_unused_range with (n := 0). all: intuition; lia.
  Qed.

  Lemma vec_forall_map X Y (f : X -> Y) n (v : vector X n) (p : Y -> Type) :
    (forall x, vec_in x v -> p (f x)) -> forall y, vec_in y (map f v) -> p y.
  Proof.
    intros H y Hmap. induction v; cbn; inv Hmap; eauto.
  Qed.

  Lemma unused_after_subst_term t sigma y :
    (forall x, unused_term x t \/ unused_term y (sigma x)) -> unused_term y (subst_term sigma t).
  Proof.
    induction t using strong_term_ind; intros Hvars; asimpl.
    - destruct (Hvars x) as [H | H]; [inv H; congruence | assumption].
    - constructor. apply vec_forall_map. intros t H'. apply (H t H'). intros x. destruct (Hvars x). 2: tauto.
      left. inv H0. eauto.
  Qed.

  Lemma unused_after_subst phi sigma y :
    (forall x, unused x phi \/ unused_term y (sigma x)) -> unused y (subst_form sigma phi).
  Proof.
    intros Hvars. induction phi in Hvars, sigma, y |-*; asimpl; constructor.
    1: apply vec_forall_map; intros s H; apply unused_after_subst_term. 2: apply IHphi1. 3: apply IHphi2.
    1-3: intros x; destruct (Hvars x) as [H' | H']; [left; inv H'; eauto | tauto].
    apply IHphi. intros [].
    - right. cbn; constructor. congruence.
    - destruct (Hvars n). 1: left; now inv H. right. cbn. unfold ">>".
      apply unused_after_subst_term. intros x. decide (x = y).
      * subst. tauto.
      * right. constructor. unfold "↑". congruence.
  Qed.

  (* **** Theories *)

  Definition theory := form -> Prop.
  Definition contains phi (T : theory) := T phi.
  Definition contains_L (A : list form) (T : theory) := forall f, List.In f A -> contains f T.
  Definition subset_T (T1 T2 : theory) := forall (phi : form), contains phi T1 -> contains phi T2.
  Definition list_T A : theory := fun phi => List.In phi A.

  Infix "⊏" := contains_L (at level 20).
  Infix "⊑" := subset_T (at level 20).
  Infix "∈" := contains (at level 70).

  Hint Unfold contains : core.
  Hint Unfold contains_L : core.
  Hint Unfold subset_T : core.

  Global Instance subset_T_trans : Transitive subset_T.
  Proof.
    intros T1 T2 T3. intuition.
  Qed.

  Definition extend T (phi : form) := fun psi => T psi \/ psi = phi.
  Infix "⋄" := extend (at level 20).

  Definition closed_T (T : theory) := forall phi n, contains phi T -> unused n phi.
  Lemma closed_T_extend T phi :
    closed_T T -> closed phi -> closed_T (T ⋄ phi).
  Proof.
    intros ? ? ? ? []; subst; intuition.
  Qed.

  Section ContainsAutomation.
    Lemma contains_nil T :
      List.nil ⊏ T.
    Proof. firstorder. Qed.

    Lemma contains_cons a A T :
      a ∈ T -> A ⊏ T -> (a :: A) ⊏ T.
    Proof. intros ? ? ? []; subst; intuition. Qed.

    Lemma contains_cons2 a A T :
      (a :: A) ⊏ T -> A ⊏ T.
    Proof. firstorder. Qed.

    Lemma contains_app A B T :
      A ⊏ T -> B ⊏ T -> (A ++ B) ⊏ T.
    Proof. intros ? ? ? [] % in_app_or; intuition. Qed.

    Lemma contains_extend1 phi T :
      phi ∈ (T ⋄ phi).
    Proof. now right. Qed.

    Lemma contains_extend2 phi psi T :
      phi ∈ T -> phi ∈ (T ⋄ psi).
    Proof. intros ?. now left. Qed.

    Lemma contains_extend3 A T phi :
      A ⊏ T -> A ⊏ (T ⋄ phi).
    Proof.
      intros ? ? ?. left. firstorder.
    Qed.
  End ContainsAutomation.
End FOL.

Definition tmap {S1 S2 : Signature} (f : @form S1 -> @form S2) (T : @theory S1) : @theory S2 :=
  fun phi => exists psi, T psi /\ f psi = phi.

Lemma enum_tmap {S1 S2 : Signature} (f : @form S1 -> @form S2) (T : @theory S1) L :
  list_enumerator L T -> list_enumerator (L >> List.map f)  (tmap f T).
Proof.
  intros.
  - intros x; split.
    + intros (phi & [m Hin] % H & <-). exists m. apply in_map_iff. firstorder.
    + intros (m & (phi & <- & Hphi) % in_map_iff). firstorder.
Qed.

Lemma tmap_contains_L {S1 S2 : Signature} (f : @form S1 -> @form S2) T A :
  contains_L A (tmap f T) -> exists B, A = List.map f B /\ contains_L B T.
Proof.
  induction A.
  - intros. now exists List.nil.
  - intros H. destruct IHA as (B & -> & HB). 1: firstorder.
    destruct (H a (or_introl eq_refl)) as (b & Hb & <-).
    exists (b :: B). split. 1: auto. intros ? []; subst; auto.
Qed.

Local Hint Constructors vec_in : core.

Infix "⊏" := contains_L (at level 20).
Infix "⊑" := subset_T (at level 20).
Infix "∈" := contains (at level 70).
Infix "⋄" := extend (at level 20).

#[export] Hint Resolve contains_nil contains_cons contains_cons2 contains_app : contains_theory.
#[export] Hint Resolve contains_extend1 contains_extend2 contains_extend3 : contains_theory.
Ltac use_theory A := exists A; split; [eauto 15 with contains_theory|].

(* **** Enumerability *)


Fixpoint vecs_from X (A : list X) (n : nat) : list (vector X n) :=
  match n with
  | 0 => [Vector.nil]
  | S n => [ cons x v | (x,  v) ∈ (A × vecs_from A n) ]
  end.

Lemma list_prod_in X Y (x : X * Y) A B :
  x el (A × B) -> exists a b, x = (a , b) /\ a el A /\ b el B.
Proof.
  induction A; cbn.
  - intros [].
  - intros [H | H] % in_app_or. 2: firstorder.
    apply in_map_iff in H as (y & <- & Hel). exists a, y. tauto.
Qed.

Lemma vecs_from_correct X (A : list X) (n : nat) (v : vector X n) :
  (forall x, vec_in x v -> x el A) <-> v el vecs_from A n.
Proof.
  induction n; cbn.
  - split.
    + intros. left. now eapply Vector.case0.
    + intros [<- | []] x H. inv H.
  - split.
    + intros. revert H. apply (Vector.caseS' v). clear v.
      intros ? v H. in_collect (pair h v); destruct (IHn v). all: eauto using vec_in.
    + intros Hv. apply in_map_iff in Hv as ([h v'] & <- & (? & ? & [= <- <-] & ? & ?) % list_prod_in).
      intros x H. inv H; destruct (IHn v'); eauto.
Qed.

Lemma vec_forall_cml X (L : nat -> list X) n (v : vector X n) :
  cumulative L -> (forall x, vec_in x v -> exists m, x el L m) -> exists m, v el vecs_from (L m) n.
Proof.
  intros HL Hv. induction v; cbn.
  - exists 0. tauto.
  - destruct IHv as [m H], (Hv h) as [m' H']. 1-3: eauto using vec_in. exists (m + m').
    in_collect (pair h v). 1: apply (cum_ge' (n := m')); intuition lia.
    apply vecs_from_correct. rewrite <- vecs_from_correct in H. intros x Hx.
    apply (cum_ge' (n := m)). all: eauto. lia.
Qed.

Fixpoint L_vec X (L : nat -> list X) n m : list (vector X n) :=
  match m with
  | 0 => []
  | S m => L_vec L n m ++ vecs_from (cumul L m) n
  end.

#[global]
Instance enumT_vec X L_T {HX : list_enumerator__T L_T X} n : list_enumerator__T (L_vec L_T n) (vector X n).
Proof with try (eapply cum_ge'; eauto; lia).
  intros v. enough (exists m, forall x, vec_in x v -> x el cumul L_T m) as [m Hm].
  { exists (S m). cbn. in_app 2. now rewrite <- vecs_from_correct. }
  induction v.
  + exists 0. intros x H. inv H.
  + destruct (cumul_spec__T HX h) as [m Hm], IHv as [m' Hm']. exists (m + m').
    intros x Hx. inv Hx...
Defined.

Section Enumerability.
  Context {Sigma : Signature}.

  Variable e_F : nat -> list Funcs.
  Variable e_P : nat -> list Preds.

  Hypothesis enum_Funcs : list_enumerator__T e_F Funcs.
  Hypothesis enum_Preds : list_enumerator__T e_P Preds.

  Fixpoint L_term n : list term :=
    match n with
    | 0 => []
    | S n => L_term n ++ var_term n :: concat ([ [ Func F v | v ∈ vecs_from (L_term n) (fun_ar F) ] | F ∈ L_T n])
    end.

  Lemma L_term_cml :
    cumulative L_term.
  Proof.
    intros ?; cbn; eauto.
  Qed.

  Global Instance enumT_term : list_enumerator__T L_term term.
  Proof with try (eapply cum_ge'; eauto; lia).
    intros t. induction t using strong_term_ind.
    + exists (S x); cbn. now in_app 2.
    + apply vec_forall_cml in H as [m H]. 2: exact L_term_cml. destruct (cumul_spec__T enum_Funcs F) as [m' H'].
      exists (S (m + m')); cbn. in_app 3. eapply in_concat_iff. eexists. split. 2: in_collect F...
      apply in_map. rewrite <- vecs_from_correct in H |-*. intros x H''. specialize (H x H'')...
  Defined.

  Fixpoint L_form n : list form :=
    match n with
    | 0 => [Fal]
    | S n => L_form n
                   ++ [Fal]
                   ++ concat ([ [ Pred P v | v ∈ L_T (H := @enumT_vec _ _ _  _) n ] | P ∈ L_T n])
                   ++ [ phi1 --> phi2 | (phi1, phi2) ∈ (L_form n × L_form n) ]
                   ++ [ ∀ phi | phi ∈ L_form n ]
    end.

  Lemma L_form_cml :
    cumulative L_form.
  Proof.
    intros ?; cbn; eauto.
  Qed.

  Global Instance enumT_form : list_enumerator__T L_form form.
  Proof with (try eapply cum_ge'; eauto; lia).
    intros phi. induction phi.
    + exists 1. cbn; eauto.
    + destruct (el_T P) as [m Hm], (el_T t) as [m' Hm']. exists (S (m + m')); cbn.
      in_app 3. eapply in_concat_iff. eexists. split. 2: in_collect P... apply in_map...
    + destruct IHphi1 as [m1], IHphi2 as [m2]. exists (1 + m1 + m2). cbn.
      in_app 4. in_collect (pair phi1 phi2)...
    + destruct IHphi as [m]. exists (S m). cbn -[L_T].
      in_app 5. in_collect phi...
  Defined.
End Enumerability.

(* **** Equality deciders *)

Lemma dec_vec_in X n (v : vector X n) :
  (forall x, vec_in x v -> forall y, dec (x = y)) -> forall v', dec (v = v').
Proof with subst; try (now left + (right; intros[=]; resolve_existT; congruence)).
  intros Hv. induction v; intros v'.
  - pattern v'. apply Vector.case0...
  - apply (Vector.caseS' v'). clear v'. intros h0 v'.
    destruct (Hv h (vec_inB h v) h0)... destruct (IHv (fun x H => Hv x (vec_inS h0 H)) v')...
Qed.

#[global]
Instance dec_vec X {HX : eq_dec X} n : eq_dec (vector X n).
Proof.
  intros v. refine (dec_vec_in _).
Qed.

Section EqDec.
  Context {Sigma : Signature}.

  Hypothesis eq_dec_Funcs : eq_dec Funcs.
  Hypothesis eq_dec_Preds : eq_dec Preds.

  Global Instance dec_term : eq_dec term.
  Proof with subst; try (now left + (right; intros[=]; resolve_existT; congruence))
    using eq_dec_Funcs.
    intros t. induction t using strong_term_ind; intros []...
    - decide (x = n)...
    - decide (F = f)... destruct (dec_vec_in X t)...
  Qed.

  Global Instance dec_form : eq_dec form.
  Proof with subst; try (now left + (right; intros[=]; resolve_existT; congruence))
    using eq_dec_Preds eq_dec_Funcs.
    intros phi. induction phi; intros []...
    - decide (P = P0)... decide (t = t0)...
    - decide (phi1 = f)... decide (phi2 = f0)...
    - decide (phi = f)...
  Qed.
End EqDec.

(* **** Subterm relation *)

Section Subterm.
  Context {Sigma : Signature}.

  Definition form_shift n := var_term (S n).
  Notation "↑" := form_shift.

  Inductive subterm t : term -> Prop :=
  | stB : subterm t t
  | stF F v s : vec_in s v -> subterm t s -> subterm t (Func F v).

  Inductive subterm_form t : form -> Prop :=
  | stP P v s : vec_in s v -> subterm t s -> subterm_form t (Pred P v)
  | stIL phi psi : subterm_form t phi -> subterm_form t (phi --> psi)
  | stIR phi psi : subterm_form t psi -> subterm_form t (phi --> psi)
  | stA phi : subterm_form t[↑] phi -> subterm_form t (∀ phi).
End Subterm.

(* **** Signature extension *)

Section SigExt.
  Hint Unfold axioms.funcomp : core.

  Definition sig_ext (Sigma : Signature) : Signature :=
    match Sigma with
      B_S Funcs fun_ar Preds pred_ar =>
      B_S (Funcs + nat)
          (fun f => match f with inl f' => fun_ar f' | inr _ => 0 end)
          Preds
          pred_ar
    end.

  Global Instance dec_sig_ext_Funcs {Sigma : Signature} (H : eq_dec Funcs) : eq_dec (@Funcs (sig_ext Sigma)).
  Proof with subst; try (now left + (right; intros[=]; resolve_existT; congruence)).
    destruct Sigma. intros [] []...
    - decide (f = f0)...
    - decide (n = n0)...
  Qed.

  Global Instance dec_sig_ext_Preds {Sigma : Signature} (H : eq_dec Preds) : eq_dec (@Preds (sig_ext Sigma)).
  Proof with subst; try (now left + (right; intros[=]; resolve_existT; congruence)).
    destruct Sigma. exact H. 
  Qed.

  Global Instance enumT_sig_ext_Funcs {Sigma : Signature} {f} {H : list_enumerator__T f Funcs} : inf_list_enumerable__T (@Funcs (sig_ext Sigma)).
  Proof with (try eapply cum_ge'; eauto; lia).
    destruct Sigma. exists (fix f n := match n with 0 => List.map inl (L_T 0) | S n' => f n' ++ (inr n') :: List.map inl (L_T n') end).
    1: eauto. intros [f0|]. 2: exists (S n); in_app 2... destruct (el_T f0) as [m Hin]. exists (S m). in_app 3. in_collect f0...
  Qed.

  Global Instance enumT_sig_ext_Preds {Sigma : Signature} {f} {H : list_enumerator__T f Preds} : inf_list_enumerable__T (@Preds (sig_ext Sigma)).
  Proof.
    destruct Sigma. eexists. exact H.
  Qed.

  Fixpoint sig_lift_term' F F_ar P P_ar (t : @term (B_S F F_ar P P_ar)) :
    (@term (sig_ext (B_S F F_ar P P_ar))) :=
      match t with
      | var_term x => var_term x
      | Func f v => @Func (sig_ext (B_S F F_ar P P_ar)) (inl f) (map (fun x => sig_lift_term' x) v)
      end.

  Definition sig_lift_term {Sigma : Signature} : @term Sigma -> @term (sig_ext Sigma) :=
    match Sigma return @term Sigma -> @term (sig_ext Sigma) with
      B_S Funcs fun_ar Preds pred_ar as S => fun t => sig_lift_term' t
    end.
  Hint Unfold sig_lift_term : core.

  Fixpoint sig_lift' F F_ar P P_ar (phi : @form (B_S F F_ar P P_ar)) :
    (@form (sig_ext (B_S F F_ar P P_ar))) :=
      match phi with
      | Fal => Fal
      | Pred p v => @Pred (sig_ext (B_S F F_ar P P_ar)) p (map sig_lift_term v)
      | Impl phi psi => Impl (sig_lift' phi) (sig_lift' psi)
      | All phi => All (sig_lift' phi)
      end.

  Definition sig_lift {Sigma : Signature} : @form Sigma -> @form (sig_ext Sigma) :=
    match Sigma return @form Sigma -> @form (sig_ext Sigma) with
      B_S Funcs fun_ar Preds pred_ar as Sig => fun phi => sig_lift' phi
    end.
  Hint Unfold sig_lift : core.

  Lemma sig_lift_subst_term {Sigma : Signature} xi t :
    sig_lift_term (subst_term xi t) = subst_term (xi >> sig_lift_term) (sig_lift_term t).
  Proof.
    destruct Sigma. induction t using strong_term_ind; comp.
    - reflexivity.
    - f_equal. erewrite! vec_comp. 2,3: reflexivity. now apply vec_map_ext.
  Qed.

  Lemma sig_lift_subst {Sigma : Signature} xi phi :
    sig_lift (subst_form xi phi) = subst_form (xi >> sig_lift_term) (sig_lift phi).
  Proof.
    destruct Sigma. induction phi in xi |-*; comp; try congruence.
    - f_equal. erewrite! vec_comp. 2,3: reflexivity. apply vec_map_ext. intros x.
      specialize (sig_lift_subst_term xi x) as ?. now comp.
    - f_equal. rewrite IHphi. comp. apply ext_form. intros []. 1: reflexivity.
      comp. unfold ">>". specialize (sig_lift_subst_term (fun x => var_term (shift x)) (xi n)) as H.
      comp. now rewrite H.
  Qed.

  Fixpoint fin_minus (n m : nat) : (n < m) + {x | x = n - m} :=
    match n, m with
    | n', 0 => inr (exist (fun x => x = n' - 0) n' eq_refl)
    | 0, S m' => inl (le_n_S 0 m' (Nat.le_0_l m'))
    | S n', S m' =>
      match fin_minus n' m' with
      | inr (exist _ x H) => inr (exist _ x H)
      | inl H => inl (le_n_S (S n') m' H)
      end
    end.

  Definition vsubs {Sigma : Signature} (n m : nat) (v : vector term n) (x : nat) : term :=
    match fin_minus x n with
    | inl i => nth_order v i
    | inr (exist _ y _) => var_term (y + m)
    end.
  Hint Unfold vsubs : core.

  Lemma up_term_term_vsubs {Sigma : Signature }n (v : vector term n) i x :
    up_term_term (vsubs i v) x = vsubs (S i) (cons (var_term 0) (map (subst_term (vsubs 1 nil)) v)) x.
  Proof.
    destruct x; comp. 1: reflexivity. destruct (fin_minus x n); comp.
    - rewrite nth_map with (p2 := Fin.of_nat_lt l). 2: apply Fin.of_nat_ext. apply ext_term. intros y.
      destruct (fin_minus y 0). 1: lia. destruct s; subst. unfold ">>", shift. f_equal; lia.
    - destruct s. comp. now rewrite <- (plus_n_Sm x0 i).
  Qed.

  Fixpoint sig_drop_term' F F_ar P P_ar (n : nat) (t : @term (sig_ext (B_S F F_ar P P_ar))) :
    @term (B_S F F_ar P P_ar) :=
    match t with
    | var_term x => var_term x
    | Func (inl f') v => @Func (B_S F F_ar P P_ar) f' (map (fun x => sig_drop_term' n x) v)
    | Func (inr y) _ => var_term (n + y)
    end.

  Definition sig_drop_term {Sigma : Signature} (n : nat) : @term (sig_ext Sigma) -> @term Sigma :=
    match Sigma return @term (sig_ext Sigma) -> @term Sigma with
      B_S Funcs fun_ar Preds pred_ar as S => sig_drop_term' n
    end.
  Hint Unfold sig_drop_term : core.

  Fixpoint sig_drop' F F_ar P P_ar (n : nat) (phi : @form (sig_ext (B_S F F_ar P P_ar))) :
    @form (B_S F F_ar P P_ar) :=
      match phi with
      | Fal => Fal
      | Pred p v => @Pred (B_S F F_ar P P_ar) p (map (sig_drop_term n) v)
      | Impl phi psi => Impl (sig_drop' n phi) (sig_drop' n psi)
      | All phi => All (sig_drop' (S n) phi)
      end.

  Definition sig_drop {Sigma : Signature} (n : nat) : @form (sig_ext Sigma) -> @form Sigma :=
    match Sigma return @form (sig_ext Sigma) -> @form Sigma with
      B_S Funcs fun_ar Preds pred_ar as Sig => sig_drop' n
    end.
  Hint Unfold sig_drop : core.

  Lemma nth_order_map X Y (f : X -> Y) n (v : vector X n) i (H : i < n) :
    nth_order (map f v) H = f (nth_order v H).
  Proof.
    now apply nth_map.
  Qed.

  Lemma sig_drop_subst_term' f f_ar P P_ar t n m i (v : vector (@term (sig_ext (B_S f f_ar P P_ar))) m) :
    sig_drop_term' (n + i) (t [vsubs i v]) = (sig_drop_term' (n + m) t)[vsubs i (map (sig_drop_term' (n + i)) v)].
  Proof.
    induction t using strong_term_ind; comp.
    - destruct (fin_minus x m); comp; [now rewrite nth_order_map | now destruct s].
    - destruct F; comp. 2: destruct (fin_minus (n + m + n0) m); [| destruct s; subst; f_equal]; lia.
      f_equal. erewrite! vec_comp. 2,3 : reflexivity. apply vec_map_ext. intros t Ht. now apply H.
  Qed.

  Lemma sig_drop_subst' f f_ar P P_ar phi n m i (v : vector (@term (sig_ext (B_S f f_ar P P_ar))) m) :
    sig_drop' (n + i) (subst_form (vsubs i v) phi) = subst_form (vsubs i (map (sig_drop_term' (n + i)) v)) (sig_drop' (n + m) phi).
  Proof.
    induction phi in i, m, v |-*. 1,2,3: comp.
    - reflexivity.
    - f_equal. erewrite! vec_comp. 2,3 : reflexivity. apply vec_ext. intros s. now apply sig_drop_subst_term'.
    - now rewrite IHphi1, IHphi2.
    - cbn. f_equal. erewrite ext_form with (s := phi). 2: apply up_term_term_vsubs.
      erewrite ext_form with (s := (sig_drop' (S (n + m)) phi)). 2: apply up_term_term_vsubs.
      specialize (IHphi (S m) (S i) (cons (var_term 0) (map (subst_term (vsubs 1 nil)) v))).
      replace (S (n + i)) with (n + S i) by lia. rewrite IHphi.
      replace (n + S m) with (S (n + m)) by lia. apply ext_form. intros []. 1: reflexivity.
      cbn. unfold vsubs at 1 3. cbn. destruct (fin_minus n0 m); cbn. 2: now destruct s.
      f_equal. erewrite! vec_comp. 2,3: reflexivity. apply vec_ext. intros t. unfold axioms.funcomp.
      replace (n + S i) with (n + i + 1) by lia. replace (n + i) with (n + i + 0) at 2 by lia.
      change nil with (map (@sig_drop_term' f f_ar P P_ar (n + i + 1)) nil) at 2.
      apply sig_drop_subst_term' with (v := nil) (m := 0) (i := 1) (n := n + i) (t := t).
  Qed.

  Definition ext_c' f f_ar P P_ar (n : nat) : term := @Func (sig_ext (B_S f f_ar P P_ar)) (inr n) Vector.nil.
  Definition ext_c {Sigma : Signature} (n : nat) : @term (sig_ext Sigma) :=
    match Sigma with
      B_S f f_ar P P_ar => ext_c' f_ar P_ar n
    end.

  Definition pref {Sigma : Signature} (n : nat) (rho : nat -> term) (x : nat) : term :=
    match fin_minus x n with
    | inl i => var_term x
    | inr (exist _ y _) => rho y
    end.
  Definition raise {Sigma : Signature} (n : nat) (x : nat) : term := var_term (n + x).

  Hint Unfold ext_c' pref raise : core.

  Lemma up_term_term_pref_ext_c' f (f_ar : f -> nat) P (P_ar : P -> nat) n x :
    up_term_term (pref n (ext_c' f_ar P_ar)) x = pref (S n) (ext_c' f_ar P_ar) x.
  Proof.
    destruct x. 1: reflexivity. comp. destruct (fin_minus x n). 1: now comp; unfold ">>", shift.
    destruct s. now comp.
  Qed.

  Lemma up_term_term_pref_raise {Sigma : Signature} n m x :
    up_term_term (pref n (raise m)) x = pref (S n) (raise (S m)) x.
  Proof.
    destruct x. 1: reflexivity. comp. destruct (fin_minus x n). 1: now comp; unfold ">>", shift.
    destruct s. unfold ">>", shift; now comp.
  Qed.

  Lemma lift_drop_inverse_term' f f_ar P P_ar n (t : @term (B_S f f_ar P P_ar)) :
    sig_drop_term' n (sig_lift_term' t)[pref n (ext_c' f_ar P_ar)] = t[pref n (@raise (B_S f f_ar P P_ar) n)].
  Proof.
    induction t using strong_term_ind; cbn.
    - comp. destruct (fin_minus x n). 1: reflexivity. now destruct s.
    - f_equal. erewrite! vec_comp. 2,3: reflexivity. apply vec_map_ext. intros t Ht. now apply H.
  Qed.

  Lemma lift_drop_inverse' f f_ar P P_ar n (phi : @form (B_S f f_ar P P_ar)) :
    sig_drop' n (subst_form (pref n (ext_c' f_ar P_ar)) (sig_lift' phi)) = subst_form (pref n (@raise (B_S f f_ar P P_ar) n)) phi.
  Proof.
    induction phi in n |-*. 1,2,3: comp.
    - reflexivity.
    - f_equal. erewrite! vec_comp. 2,3: reflexivity. apply vec_ext, lift_drop_inverse_term'.
    - now rewrite IHphi1, IHphi2.
    - cbn. f_equal. erewrite ext_form with (s := phi). 2: apply up_term_term_pref_raise.
      erewrite ext_form with (s := (sig_lift' phi)). 2: apply up_term_term_pref_ext_c'.
      apply IHphi.
  Qed.

  Lemma lift_drop_inverse {Sigma : Signature} phi :
    sig_drop 0 (subst_form ext_c (sig_lift phi)) = phi.
  Proof.
    destruct Sigma. erewrite ext_form with (s := sig_lift phi) (tauterm := @pref (sig_ext (B_S Funcs fun_ar Preds pred_ar)) 0 (ext_c' fun_ar pred_ar)).
    1: comp; rewrite lift_drop_inverse'; apply idSubst_form; now intros [].
    intros x. comp. destruct (fin_minus x 0). 1: lia. destruct s; subst. now replace (x - 0) with x by lia.
  Qed.

  Lemma ext_c'_unused_term f f_ar P P_ar (n : nat) (t : @term (sig_ext (B_S f f_ar P P_ar))) m :
    n <= m -> @unused_term (sig_ext (B_S f f_ar P P_ar)) m t[pref n (ext_c' f_ar P_ar)].
  Proof.
    intros Hm; induction t using strong_term_ind; comp.
    - destruct (fin_minus x n); comp. 1: constructor; lia.
      destruct s. constructor. intros ?. inversion 1.
    - constructor. apply vec_forall_map, H. 
  Qed.

  Lemma ext_c'_unused f f_ar P P_ar (n : nat) (phi : @form (sig_ext (B_S f f_ar P P_ar))) m :
    n <= m -> @unused (sig_ext (B_S f f_ar P P_ar)) m phi[pref n (ext_c' f_ar P_ar)].
  Proof.
    intros Hm; induction phi in n, m, Hm |-*. 1,2,3 : comp; constructor; auto.
    - apply vec_forall_map. intros. capply ext_c'_unused_term.
    - cbn. auto_unfold. erewrite ext_form with (s := phi). 2: apply up_term_term_pref_ext_c'.
      constructor. apply IHphi. lia.
  Qed.

  Lemma lift_ext_c_closes {Sigma : Signature} phi :
    @closed (sig_ext Sigma) (sig_lift phi)[ext_c].
  Proof.
    destruct Sigma. unfold ext_c. intros n. auto_unfold; erewrite ext_form. apply ext_c'_unused with (n := 0) (m := n).
    1: lia. now intros [].
  Qed.

  Lemma lift_ext_c_closes_T {Sigma : Signature} (T : theory) :
    @closed_T (sig_ext Sigma) (tmap (fun psi => (sig_lift psi)[@ext_c Sigma]) T).
  Proof.
    intros ? n [phi [_ <-]]. apply lift_ext_c_closes.
  Qed.
End SigExt.

Notation "↑" := form_shift.
Notation "A ⟹ phi" := (big_imp A phi) (at level 60, right associativity).
