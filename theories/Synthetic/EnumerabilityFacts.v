From Undecidability.Synthetic Require Import DecidabilityFacts SemiDecidabilityFacts.
From Undecidability.Shared Require Import embed_nat.

Local Notation "'if!' x 'is' p 'then' a 'else' b" := (match x with p => a | _ => b end) (at level 0, p pattern).

Lemma enumerable_semi_decidable {X} {p : X -> Prop} :
  discrete X -> enumerable p -> semi_decidable p.
Proof.
  unfold enumerable, enumerator.
  intros [d Hd] [f Hf].
  exists (fun x n => if! f n is Some y then d (x,y) else false).
  intros x. rewrite Hf. split.
  - intros [n Hn]. exists n.
    rewrite Hn. now eapply Hd.
  - intros [n Hn]. exists n.
    destruct (f n); inversion Hn.
    eapply Hd in Hn. now subst.
Qed.

Definition enumerator__T' X f := forall x : X, exists n : nat, f n = Some x.
Notation enumerator__T f X := (enumerator__T' X f).
Definition enumerable__T X := exists f : nat -> option X, enumerator__T f X.

Lemma semi_decidable_enumerable {X} {p : X -> Prop} :
  enumerable__T X -> semi_decidable p -> enumerable p.
Proof.
  unfold semi_decidable, semi_decider.
  intros [e He] [f Hf].
  exists (fun p => let (n, m) := unembed p in
           if! e n is Some x then if f x m then Some x else None else None).
  intros x. rewrite Hf. split.
  - intros [n Hn]. destruct (He x) as [m Hm].
    exists (embed (m,n)). now rewrite embedP, Hm, Hn.
  - intros [mn Hmn]. destruct (unembed mn) as (m, n).
    destruct (e m) as [x'|]; try congruence.
    destruct (f x' n) eqn:E; inversion Hmn. subst.
    exists n. exact E.
Qed.

Theorem dec_count_enum {X} {p : X -> Prop} :
  decidable p -> enumerable__T X -> enumerable p.
Proof.
  intros ? % decidable_semi_decidable ?.
  now eapply semi_decidable_enumerable.
Qed.

Theorem dec_count_enum' X (p : X -> Prop) :
  decidable p -> enumerable__T X -> enumerable (fun x => ~ p x).
Proof.
  intros ? % dec_compl ?. eapply dec_count_enum; eauto.
Qed.

Lemma enumerable_enumerable_T X :
  enumerable (fun _ : X => True) <-> enumerable__T X.
Proof.
  split.
  - intros [e He]. exists e. intros x. now eapply He.
  - intros [c Hc]. exists c. intros x. split; eauto.
Qed.

(* Type enumerability facts  *)

Definition nat_enum (n : nat) := Some n.
Lemma enumerator__T_nat :
  enumerator__T nat_enum nat.
Proof.
  intros n. cbv. eauto.
Qed.

Definition unit_enum (n : nat) := Some tt.
Lemma enumerator__T_unit :
  enumerator__T unit_enum unit.
Proof.
  intros []. cbv. now exists 0.
Qed. 

Definition bool_enum (n : nat) := Some (if! n is 0 then true else false).
Lemma enumerator__T_bool :
  enumerator__T bool_enum bool.
Proof.
  intros []. cbv.
  - now exists 0.
  - now exists 1.
Qed.

Definition prod_enum {X Y} (f1 : nat -> option X) (f2 : nat -> option Y) n : option (X * Y) :=
  let (n, m) := unembed n in
  if! (f1 n, f2 m) is (Some x, Some y) then Some (x, y) else None.
Lemma enumerator__T_prod {X Y} f1 f2 :
  enumerator__T f1 X -> enumerator__T f2 Y ->
  enumerator__T (prod_enum f1 f2) (X * Y).
Proof.
  intros H1 H2 (x, y).
  destruct (H1 x) as [n1 Hn1], (H2 y) as [n2 Hn2].
  exists (embed (n1, n2)). unfold prod_enum.
  now rewrite embedP, Hn1, Hn2.
Qed.

Definition option_enum {X} (f : nat -> option X) n :=
  match n with 0 => Some None | S n => Some (f n) end.
Lemma enumerator__T_option {X} f :
  enumerator__T f X -> enumerator__T (option_enum f) (option X).
Proof.
  intros H [x | ].
  - destruct (H x) as [n Hn]. exists (S n). cbn. now rewrite Hn.
  - exists 0. reflexivity.
Qed.

Existing Class enumerator__T'.
(* Existing Class enumerable__T. *)

Lemma enumerator_enumerable {X} {f} :
  enumerator__T f X -> enumerable__T X.
Proof.
  intros H. exists f. eapply H.
Qed.
#[export] Hint Resolve enumerator_enumerable : core.

Global Existing Instance enumerator__T_prod.
#[global]
Existing Instance enumerator__T_option.
#[global]
Existing Instance enumerator__T_bool.
#[global]
Existing Instance enumerator__T_nat.
