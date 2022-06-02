From Undecidability.Synthetic Require Import DecidabilityFacts SemiDecidabilityFacts.
Require Cantor.
Require Import Undecidability.Shared.Libs.PSL.FiniteTypes.FinTypesDef.

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

Lemma semi_decider_enumerator {X} {p : X -> Prop} {e f} :
  enumerator__T e X -> semi_decider f p -> {g | enumerator g p}.
Proof.
  unfold semi_decider. intros He Hf.
  exists (fun p => let (n, m) := Cantor.of_nat p in
           if! e n is Some x then if f x m then Some x else None else None).
  intros x. rewrite Hf. split.
  - intros [n Hn]. destruct (He x) as [m Hm].
    exists (Cantor.to_nat (m,n)). now rewrite Cantor.cancel_of_to, Hm, Hn.
  - intros [mn Hmn]. destruct (Cantor.of_nat mn) as (m, n).
    destruct (e m) as [x'|]; try congruence.
    destruct (f x' n) eqn:E; inversion Hmn. subst.
    exists n. exact E.
Qed.

Lemma semi_decidable_enumerable {X} {p : X -> Prop} :
  enumerable__T X -> semi_decidable p -> enumerable p.
Proof.
  intros [e He] [f Hf].
  destruct (semi_decider_enumerator He Hf) as [g Hg].
  now exists g.
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

Definition False_enum (n : nat) : option False := None.
Lemma enumerator__T_False :
  enumerator__T False_enum False.
Proof.
  intros [].
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
  let (n, m) := Cantor.of_nat n in
  if! (f1 n, f2 m) is (Some x, Some y) then Some (x, y) else None.
Lemma enumerator__T_prod {X Y} f1 f2 :
  enumerator__T f1 X -> enumerator__T f2 Y ->
  enumerator__T (prod_enum f1 f2) (X * Y).
Proof.
  intros H1 H2 (x, y).
  destruct (H1 x) as [n1 Hn1], (H2 y) as [n2 Hn2].
  exists (Cantor.to_nat (n1, n2)). unfold prod_enum.
  now rewrite Cantor.cancel_of_to, Hn1, Hn2.
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

Definition sigT_enum {X: Type} {P : X -> Type}
  (f : nat -> option X) (fP : forall x, nat -> option (P x)) (n : nat) : 
    option {x : X & P x} :=
  let (nx, nP) := Cantor.of_nat n in
  match f nx with
  | Some x =>
    match fP x nP with
    | Some y => Some (existT P x y)
    | _ => None
    end
  | None => None
  end.
Lemma enumerator__T_sigT {X: Type} {P : X -> Type} f fP :
  enumerator__T f X -> (forall x, enumerator__T (fP x) (P x)) ->
  enumerator__T (sigT_enum f fP) {x : X & P x}.
Proof.
  intros Hf HfP [x HPx].
  destruct (Hf x) as [nx Hnx].
  destruct (HfP x (HPx)) as [nP HnP].
  exists (Cantor.to_nat (nx, nP)).
  unfold sigT_enum.
  now rewrite !Cantor.cancel_of_to, Hnx, HnP.
Qed.

Definition sigT2_enum {X: Type} {P : X -> Type} {Q : X -> Type}
  (f : nat -> option X) (fP : forall x, nat -> option (P x)) (fQ : forall x, nat -> option (Q x)) (n : nat) : 
    option {x : X & P x & Q x} :=
  let (nx, m) := Cantor.of_nat n in
  let (nP, nQ) := Cantor.of_nat m in
  match f nx with
  | Some x =>
    match fP x nP, fQ x nQ with
    | Some y, Some z => Some (existT2 P Q x y z)
    | _, _ => None
    end
  | None => None
  end.
Lemma enumerator__T_sigT2 {X: Type} {P : X -> Type} {Q : X -> Type} f fP fQ :
  enumerator__T f X -> (forall x, enumerator__T (fP x) (P x)) -> (forall x, enumerator__T (fQ x) (Q x)) ->
  enumerator__T (sigT2_enum f fP fQ) {x : X & P x & Q x}.
Proof.
  intros Hf HfP HfQ [x HPx HQx].
  destruct (Hf x) as [nx Hnx].
  destruct (HfP x (HPx)) as [nP HnP].
  destruct (HfQ x (HQx)) as [nQ HnQ].
  exists (Cantor.to_nat (nx, Cantor.to_nat (nP, nQ))).
  unfold sigT2_enum.
  now rewrite !Cantor.cancel_of_to, Hnx, HnP, HnQ.
Qed.

Require Import List.

Definition finType_enum {X: finType} (n : nat) : option X :=
  nth_error (@enum _ (class X)) n.
Lemma enumerator__T_finType {X: finType} :
  enumerator__T finType_enum X.
Proof.
  intros x.
  assert (H := (@enum_ok _ (class X)) x).
  unfold finType_enum. induction enum as [|y L IH].
  - easy.
  - cbn in H. destruct (Dec (x = y)) as [->|H'].
    + now exists 0.
    + destruct (IH H) as [n Hn]. now exists (S n).
Qed.

Fixpoint all_fins (n : nat) : list (Fin.t n) :=
  match n with
  | 0 => nil
  | S n => Fin.F1 :: map Fin.FS (all_fins n)
  end.

Definition Fin_enum {k: nat} (n : nat) : option (Fin.t k) :=
  nth_error (all_fins k) n.
Lemma enumerator__T_Fin {k: nat} :
  enumerator__T Fin_enum (Fin.t k).
Proof.
  intros t. exists (proj1_sig (Fin.to_nat t)).
  unfold Fin_enum. induction t as [n|n t IH].
  { reflexivity. }
  cbn. destruct (Fin.to_nat t) as [t' H']. cbn in *.
  now rewrite nth_error_map, IH.
Qed.

Opaque Cantor.to_nat Cantor.of_nat.

Fixpoint Vector_enum {X: Type} {k: nat} (f : nat -> option X) (n : nat) : option (Vector.t X k) :=
  match k return option (Vector.t X k) with
  | 0 => Some (@Vector.nil X)
  | S k' => 
    let (nx, m) := Cantor.of_nat n in
    match f nx with
    | Some x =>
      match (@Vector_enum X k' f m) with
      | Some v => Some (@Vector.cons X x k' v)
      | _ => None
      end
    | None => None
    end
  end.
Lemma enumerator__T_Vector {X: Type} {k: nat} (f : nat -> option X) :
  enumerator__T f X -> enumerator__T (Vector_enum f) (Vector.t X k).
Proof.
  intros Hf. induction k as [|k IH].
  { intros t. pattern t. apply (Vector.case0). now exists 0. }
  intros t. rewrite (Vector.eta t).
  destruct (Hf (VectorDef.hd t)) as [nx Hnx].
  destruct (IH (VectorDef.tl t)) as [m Hm].
  exists (Cantor.to_nat (nx, m)).
  cbn. now rewrite Cantor.cancel_of_to, Hnx, Hm.
Qed.

Existing Class enumerator__T'.
(* Existing Class enumerable__T. *)

Lemma enumerator_enumerable {X} {f} :
  enumerator__T f X -> enumerable__T X.
Proof.
  intros H. exists f. eapply H.
Qed.
#[export] Hint Resolve enumerator_enumerable : core.

#[global] Existing Instance enumerator__T_prod.
#[global] Existing Instance enumerator__T_option.
#[global] Existing Instance enumerator__T_bool.
#[global] Existing Instance enumerator__T_False.
#[global] Existing Instance enumerator__T_unit.
#[global] Existing Instance enumerator__T_nat.
#[global] Existing Instance enumerator__T_sigT.
#[global] Existing Instance enumerator__T_sigT2.
#[global] Existing Instance enumerator__T_finType.
#[global] Existing Instance enumerator__T_finType.
#[global] Existing Instance enumerator__T_Fin.
#[global] Existing Instance enumerator__T_Vector.
