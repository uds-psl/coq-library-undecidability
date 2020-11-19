(** * Natural Deduction *)

From Undecidability Require Export FOL.Util.Tarski.
Import ListAutomationNotations.
Local Set Implicit Arguments.



Require Import List.
Notation "x 'el' A" := (In x A) (at level 70).
Notation "A '<<=' B" := (incl A B) (at level 70).

Ltac comp := repeat (progress (cbn in *; autounfold in *)).

Inductive peirce := class | intu.
Existing Class peirce.

Section ND_def.

  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.

  Reserved Notation "A ⊢ phi" (at level 61).
  
  (** ** Definition *)

  Implicit Type p : peirce.
  Implicit Type ff : falsity_flag.

  Inductive prv : forall (ff : falsity_flag) (p : peirce), list form -> form -> Prop :=
  | II {ff} {p} A phi psi : phi::A ⊢ psi -> A ⊢ phi --> psi
  | IE {ff} {p} A phi psi : A ⊢ phi --> psi -> A ⊢ phi -> A ⊢ psi
  | AllI {ff} {p} A phi : map (subst_form ↑) A ⊢ phi -> A ⊢ ∀ phi
  | AllE {ff} {p} A t phi : A ⊢ ∀ phi -> A ⊢ phi [t..]
  (*| ExI {p} A t phi : A ⊢ phi[t..] -> A ⊢ ∃ phi
  | ExE {p} A phi psi : A ⊢ ∃ phi -> phi::(map (subst_form ↑) A) ⊢ psi[↑] -> A ⊢ psi*)
  | Exp {p} A phi : prv p A falsity -> prv p A phi
  | Ctx {ff} {p} A phi : phi el A -> A ⊢ phi
  (*| CI {p} A phi psi : A ⊢ phi -> A ⊢ psi -> A ⊢ phi ∧ psi
  | CE1 {p} A phi psi : A ⊢ phi ∧ psi -> A ⊢ phi
  | CE2 {p} A phi psi : A ⊢ phi ∧ psi -> A ⊢ psi
  | DI1 {p} A phi psi : A ⊢ phi -> A ⊢ phi ∨ psi
  | DI2 {p} A phi psi : A ⊢ psi -> A ⊢ phi ∨ psi
  | DE {p} A phi psi theta : A ⊢ phi ∨ psi -> phi::A ⊢ theta -> psi::A ⊢ theta -> A ⊢ theta*)
  | Pc {ff} A phi psi : prv class A (((phi --> psi) --> phi) --> phi)
  where "A ⊢ phi" := (prv _ A phi).

  Arguments prv {_} _ _.

  Context {ff : falsity_flag}.
  Context {p : peirce}.

  Theorem Weak A B phi :
    A ⊢ phi -> A <<= B -> B ⊢ phi.
  Proof.
    intros H. revert B.
    induction H; intros B HB; try unshelve (solve [econstructor; intuition]); try now econstructor.
  Qed.
    
End ND_def.


Hint Constructors prv : core.

Arguments prv {_ _ _ _} _ _.
Notation "A ⊢ phi" := (prv A phi) (at level 30).
Notation "A ⊢C phi" := (@prv _ _ _ class A phi) (at level 30).
Notation "A ⊢I phi" := (@prv _ _ _ intu A phi) (at level 30).

Section Soundness.

  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.

  Lemma soundness {ff : falsity_flag} A phi :
    A ⊢I phi -> valid_ctx A phi.
  Proof.
    remember intu as p.
    induction 1; intros D I rho HA; comp.
    - intros Hphi. apply IHprv; trivial. intros ? []; subst. assumption. now apply HA.
    - now apply IHprv1, IHprv2.
    - intros d. apply IHprv; trivial. intros psi [psi'[<- H' % HA]] % in_map_iff.
      eapply sat_comp. now comp.
    - eapply sat_comp, sat_ext. 2: apply (IHprv Heqp D I rho HA (eval rho t)). now intros [].
    (* - exists (eval rho t). cbn. specialize (IHprv Heqp D I rho HA).
      apply sat_comp in IHprv. eapply sat_ext; try apply IHprv. now intros [].
    - edestruct IHprv1 as [d HD]; eauto.
      assert (H' : forall psi, phi = psi \/ psi el map (subst_form ↑) A -> (d.:rho) ⊨ psi).
      + intros P [<-|[psi'[<- H' % HA]] % in_map_iff]; trivial. apply sat_comp. apply H'.
      + specialize (IHprv2 Heqp D I (d.:rho) H'). apply sat_comp in IHprv2. apply IHprv2. *)
    - apply (IHprv Heqp) in HA. firstorder.
    - firstorder.
    (* - firstorder.
    - firstorder. now apply H0.
    - firstorder. now apply H0.
    - firstorder.
    - firstorder.
    - edestruct IHprv1; eauto.
      + apply IHprv2; trivial. intros xi [<-|HX]; auto.
      + apply IHprv3; trivial. intros xi [<-|HX]; auto. *)
    - discriminate.
  Qed.

  Lemma soundness' {ff : falsity_flag} phi :
    [] ⊢I phi -> valid phi.
  Proof.
    intros H % soundness. firstorder.
  Qed.

End Soundness.



(** ** Generalised Induction *)
(*
Fixpoint size {b} (phi : form b) :=
  match phi with
  | Pr _ _ | Q | Fal => 1
  | Impl phi1 phi2 => 1 + size phi1 + size phi2
  | All n phi => 1 + size phi
  end.

Lemma size_subst {b : logic} x t phi :
  size (subst x t phi) = size phi.
Proof.
  induction phi; cbn; try congruence; decs.
Qed.

Lemma size_induction_dep L (X : L -> Type) (f : forall l, X l -> nat) (p : forall l, X l -> Type) :
  (forall l x, (forall l' y, f l' y < f l x -> p l' y) -> p l x) -> 
  forall l x, p l x.
Proof. 
  intros IH l x. apply IH. intros l'.
  assert (G: forall n l' y, f l' y < n -> p l' y).
  { intros n. induction n; intros l'' y.
    - intros B. exfalso. lia.
    - intros B. apply IH. intros ll z C. eapply IHn. lia. }
  apply G.
Qed.

Lemma size_induction X (f : X -> nat) (p : X -> Prop) :
  (forall x, (forall y, f y < f x -> p y) -> p x) -> 
  forall x, p x.
Proof. 
  intros IH x. apply IH. 
  assert (G: forall n y, f y < n -> p y).
  { intros n. induction n.
    - intros y B. exfalso. lia.
    - intros y B. apply IH. intros z C. apply IHn. lia. }
  apply G.
Qed.

Lemma form_ind_subst :
forall P : forall f : logic, form f -> Prop,
(forall (b : logic) (t t0 : term), P b (Pr t t0)) ->
(forall b : logic, P b Q) ->
P full ⊥ ->
(forall (b : logic) (f2 : form b), P b f2 -> forall f3 : form b, P b f3 -> P b (f2 --> f3)) ->
(forall (b : logic) (n : var) (f4 : form b), (forall x, P b (subst n x f4)) -> P b (∀ n; f4)) -> forall (f5 : logic) (f6 : form f5), P f5 f6.
Proof.
  intros. eapply size_induction_dep with (f := @size). intros b x IH. destruct x; eauto.
  - eapply H2; eapply IH; cbn; lia.
  - eapply H3. intros. eapply IH. rewrite size_subst. cbn. lia.
Qed.

Lemma form_logic_ind_subst :
forall P : form frag -> Prop,
(forall t t0 : term, P (Pr t t0)) ->
P Q ->
(forall f3 : form frag, P f3 -> forall f4 : form frag, P f4 -> P (f3 --> f4)) ->
(forall (n : var) (f6 : form frag), (forall x, P (subst n x f6)) -> P (∀ n; f6)) -> forall f8 : form frag, P f8.
Proof.
  intros. remember frag as b.  revert Heqb. pattern f8. eapply size_induction with (f := @size b). intros x IH E. destruct x; eauto.
  - inv E.
  - eapply H1; eapply IH; cbn; eauto; lia.
  - eapply H2. intros. eapply IH. rewrite size_subst. cbn. lia. eauto.
Qed.

(** ** Enumerability *)

Lemma dec_fresh y A : dec (fresh y A).
Proof.
  induction A; try decide (y = a); try destruct IHA; subst; firstorder.
Qed.

Lemma incl_dec X (A B : list X) `{eq_dec X} : dec (A <<= B).
Proof.
  pose proof (forallb_forall (fun a => list_in_dec _ a B _) A).
  destruct (forallb (fun a : X => list_in_dec _ a B H) A).
  - left. intros ? ?. eapply H0 in H1. destruct list_in_dec; now inv H1. reflexivity.
  - right. intros ?. enough (false = true) by congruence. eapply H0.
    intros. destruct list_in_dec; cbn. reflexivity. exfalso; eauto.
Qed.

Fixpoint L_ded {b} {s : nd} (A : list (form b)) (n : nat) : list (form b) :=
  match n with
  | 0 => A
  | S n => L_ded A n
                ++ concat [ [ phi1 --> phi2 | phi2 ∈ L_ded (phi1 :: A) n ] | phi1 ∈ L_T (form b) n]
                ++ [ phi2 | (phi1,phi2) ∈ (L_ded A n × L_T (form b) n) , (phi1 --> phi2 el L_ded A n) ]
                ++ [ ∀ x; phi | (phi, x, y) ∈ (L_T (form b) n × L_T var n × L_T var n) ,
                               fresh y (consts phi ++ consts_l A) /\ subst x (P y) phi el L_ded A n ]
                ++ [ subst x t phi | (phi, x, t) ∈ (L_T (form b) n × L_T var n × L_T term n),
                                    vars_t t = [] /\ ∀ x; phi el L_ded A n]
                ++ match b with frag => fun _ => [] | full => fun A =>
                 match s with
                   | intu => [ phi | phi ∈ L_T (form full) n, Fal el L_ded A n ]
                   | class => [ phi | phi ∈ L_T (form full) n, (¬¬ phi) el L_ded A n ]
                   end end A
  end.

Opaque in_dec.
(* Opaque enumT_nat. *)

Hint Constructors prv : core.

Lemma enum_prv b s A : list_enumerator (L_ded A) (@prv s b A) .
Proof with try (eapply cum_ge'; eauto; lia).
  intros phi; split.
  - induction 1; try congruence; subst.
    + now exists 0.
    + destruct IHprv as [m1]; eauto. destruct (el_T phi1) as [m2].
      exists (1 + m1 + m2). cbn. in_app 2.
      eapply in_concat_iff. eexists. split.
      2:in_collect phi1...
      in_collect phi2...
    + destruct IHprv1 as [m1], IHprv2 as [m2], (el_T phi2) as [m3]; eauto.
      exists (1 + m1 + m2 + m3).
      cbn. in_app 3. in_collect (phi1, phi2)...
    + destruct (el_T x) as [m1], (el_T y) as [m2],
               (el_T phi) as [m3], IHprv as [m4]; eauto.
      exists (1 + m1 + m2 + m3 + m4). cbn -[L_T]. in_app 4.
      in_collect (phi, x, y)...
    + destruct (el_T x) as [m1], (el_T t) as [m2],
               (el_T phi) as [m3], IHprv as [m4]; eauto.
      exists (1 + m1 + m2 + m3 + m4). cbn. in_app 5.
      in_collect (phi, x, t)...
    + destruct IHprv as [m1], (el_T phi) as [m2]; eauto.
      exists (1 + m1 + m2). cbn. in_app 9.
      in_collect phi...
    + destruct IHprv as [m1], (el_T phi) as [m2], (el_T true) as [m3]; eauto.
      exists (1 + m1 + m2 + m3). cbn. in_app 9.
      in_collect phi...
  - intros [m]. revert A phi H; induction m; intros; cbn in *.
     + eauto.
     + inv_collect; eauto.
       destruct b, s; inv_collect; eauto.
Qed.

Lemma enumerable_min_prv : enumerable (prv_min []).
Proof.
  eapply list_enumerable_enumerable. eexists. eapply enum_prv.
Qed.
Lemma enumerable_intu_prv : enumerable (prv_intu []).
Proof.
  eapply list_enumerable_enumerable. eexists. eapply enum_prv.
Qed.
Lemma enumerable_class_prv : enumerable (prv_class []).
Proof.
  eapply list_enumerable_enumerable. eexists. eapply enum_prv.
Qed.*)
