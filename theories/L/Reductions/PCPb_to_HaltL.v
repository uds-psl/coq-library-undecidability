From Undecidability.Synthetic Require Import Definitions DecidabilityFacts EnumerabilityFacts ListEnumerabilityFacts.
From Undecidability Require Export PCP.PCP.
From Undecidability.Shared Require Export ListAutomation.
Require Import Lia Arith.
Import ListAutomationNotations.

From Undecidability.L Require Import LProd List_eqb LBool LNat LOptions Lists List_basics List_extra List_fold.

Definition blist_eqb :=
  list_eqb Bool.eqb.

Lemma blist_eqb_spec : forall l1 l2, l1 = l2 <-> blist_eqb l1 l2 = true.
Proof.
  intros l1 l2. unfold blist_eqb.
  destruct (list_eqb_spec Bool.eqb_spec l1 l2); firstorder congruence.
Qed.

Instance comp_eqb_list : computable blist_eqb.
Proof.
  unfold blist_eqb. extract.
Defined.

Definition stack_eqb :=
  list_eqb (prod_eqb (list_eqb Bool.eqb) (list_eqb Bool.eqb)).

Instance computable_stack_eqb : computable stack_eqb.
Proof.
  unfold stack_eqb. extract.
Qed.

Lemma stack_eqb_spec : forall l1 l2, l1 = l2 <-> stack_eqb l1 l2 = true.
Proof.
  intros l1 l2. unfold stack_eqb.
  destruct (list_eqb_spec (prod_eqb_spec (list_eqb_spec Bool.eqb_spec) (list_eqb_spec Bool.eqb_spec)) l1 l2); firstorder congruence.
Qed.

Instance computable_bool_enum : computable bool_enum.
Proof.
  extract.
Qed.

From Undecidability Require Import embed_nat.

Definition of_list_enum {X} (f : nat -> list X) := (fun n : nat => let (n0, m) := unembed n in nth_error (f n0) m).

Definition unembed' := (fix F (k : nat) := 
  match k with 0 => (0,0) | S n => match fst (F n) with 0 => (S (snd (F n)), 0) | S x => (x, S (snd (F n))) end end).

Instance unembed_computable : computable unembed.
Proof.
  eapply computableExt with (x := unembed'). 2:extract.
  intros n. cbn. induction n; cbn.
  - reflexivity.
  - fold (unembed n). rewrite IHn. now destruct (unembed n).
Qed.

Instance computable_of_list_enum {X} `{registered X} :
  computable (@of_list_enum X).
Proof.
  extract.
Qed.

Definition to_list_enum {X} (f : nat -> option X) := 
  (fun n : nat => match f n with
   | Some x => [x]
   | None => []
   end) .

Instance computable_to_list_enum {X} `{registered X} :
  computable (@to_list_enum X).
Proof.
  extract.
Qed.

Instance computable_to_cumul {X} `{registered X} :
  computable (@to_cumul X).
Proof.
  extract.
Qed.
(* 
Instance computable_list_prod {X} `{registered X} {Y} `{registered Y} :
  computable (@list_prod X Y).
Proof.
  unfold list_prod.
  extract.
  unfold L_list. cbn. *)

Definition cons' {X} : X * list X -> list X := fun '(pair x L0) => cons x L0.

Instance computable_cons' {X} `{registered X} :
  computable (@cons' X).
Proof.
  extract.
Qed.

Instance computable_L_list {X} `{registered X} :
  computable (@L_list X).
Proof.
  change (computable (fun (L : forall _ : nat, list X) =>
  fix L_list (n : nat) : list (list X) :=
    match n with
    | O => cons nil nil
    | S n0 =>
      Datatypes.app (L_list n0)
          (map cons'
             (list_prod (to_cumul L n0) (L_list n0)))
    end)). extract.
Qed.

Instance computable_prod_enum {X} `{registered X} {Y} `{registered Y} :
  computable (@prod_enum X Y).
Proof.
  extract.
Qed.

Definition stack_enum n := 
  of_list_enum (L_list (to_list_enum (prod_enum (of_list_enum (L_list (to_list_enum bool_enum))) (of_list_enum (L_list (to_list_enum bool_enum)))))) n.

Instance computable_stack_enum : computable stack_enum.
Proof.
  extract.
Qed.

Lemma stack_enum_spec :
  enumerator__T stack_enum (PCP.stack bool).
Proof.
  eauto.
Qed.

From Undecidability Require Import PCP.

Fixpoint tau1' (A : list (list bool * list bool)) : list bool :=
  match A with
  | [] => @nil bool
  | (x,y) :: A0 => x ++ tau1' A0
  end.

Instance computable_tau1' :
  computable tau1'.
Proof.
  extract.
Qed.

Instance computable_tau1 : computable (@tau1 bool).
Proof.
  eapply computableExt with (x := tau1'). 2:exact _.
  intros n. cbn. induction n as [ | [] ]; cbn; congruence.
Qed.

Fixpoint tau2' (A : list (list bool * list bool)) : list bool :=
  match A with
  | [] => @nil bool
  | (x,y) :: A0 => y ++ tau2' A0
  end.

Lemma  tau1'_spec A : tau1' A = tau1 A. 
Proof.
  induction A as [ | []]; cbn; congruence.
Qed.

Lemma  tau2'_spec A : tau2' A = tau2 A. 
Proof.
  induction A as [ | []]; cbn; congruence.
Qed.

Instance computable_tau2' :
  computable tau2'.
Proof.
  extract.
Qed.

Instance computable_tau2 : computable (@tau2 bool).
Proof.
  eapply computableExt with (x := tau2'). 2:exact _.
  intros n. cbn. induction n as [ | [] ]; cbn; congruence.
Qed.

Definition my_inb (P : stack bool) :=
  (list_in_decb ((prod_eqb (list_eqb Bool.eqb) (list_eqb Bool.eqb))) P).

Instance computable_myinb :
  computable my_inb.
Proof.
  extract.
Qed.

Fixpoint subsetb A P :=
  match A with
  | nil => true
  | a :: A => my_inb P a && subsetb A P
  end.

Lemma subsetb_spec A P :
  subsetb A P = forallb (my_inb P) A.
Proof.
  induction A; cbn; congruence.
Qed.

Instance computable_subsetb :
  computable subsetb.
Proof.
  extract.
Qed.

Opaque blist_eqb subsetb.

Definition sdec_PCPb := (fun (P : PCP.stack bool) n => match stack_enum n with Some [] | None => false | Some A => andb (subsetb A P) (blist_eqb (tau1' A) (tau2' A)) end).

Instance computable_sdec_PCPb :
  computable sdec_PCPb.
Proof.
  extract.
Qed.

Transparent subsetb.

Lemma semi_decidable_PCPb :
  semi_decider sdec_PCPb PCPb.
Proof.
  intros P. unfold sdec_PCPb. split.
  - intros (A & H1 & H2 & H3). 
    destruct (stack_enum_spec A) as [nA HnA]. exists nA. rewrite HnA.
    destruct A as [ | c A]; try congruence.
    eapply andb_true_intro. split.
    + rewrite subsetb_spec. eapply forallb_forall. intros ? H % H1. unfold my_inb.
      eapply list_in_decb_iff. 2: eassumption.
      intros a b. destruct (prod_eqb_spec (list_eqb_spec Bool.eqb_spec) (list_eqb_spec Bool.eqb_spec) a b); firstorder congruence.
    + eapply blist_eqb_spec. now rewrite tau1'_spec, tau2'_spec.
  - intros [n Hn]. destruct stack_enum as [A | ] eqn:E; try congruence.
    exists A.
    destruct A; try congruence.
    eapply Bool.andb_true_iff in Hn as [H1 H2].
    rewrite subsetb_spec in H1. rewrite tau1'_spec, tau2'_spec in H2. unfold my_inb in H1.
    rewrite forallb_forall in H1. eapply blist_eqb_spec in H2. 
    repeat eapply conj; try congruence.
    intros ? ? % H1. eapply list_in_decb_iff. 2: eassumption.
    intros a_ b_. destruct (prod_eqb_spec (list_eqb_spec Bool.eqb_spec) (list_eqb_spec Bool.eqb_spec) a_ b_); firstorder congruence.
Qed.

From Undecidability.L Require Import Synthetic.

Theorem reduction_PCPb_HaltL :
  PCPb ⪯ HaltL.
Proof.
  eapply L_recognisable_HaltL.
  exists sdec_PCPb. split.
  - econstructor. exact _.
  - eapply semi_decidable_PCPb.
Qed.
