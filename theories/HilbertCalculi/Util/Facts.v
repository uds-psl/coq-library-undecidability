(* 
  Autor(s):
    Andrej Dudenhefner (1) 
  Affiliation(s):
    (1) Saarland University, Saarbrücken, Germany
*)

Require Import List Lia.
Import ListNotations.
Require Import ssreflect ssrbool ssrfun. 

Set Default Proof Using "Type".

Section Facts.

(* induction principle wrt. a decreasing measure f *)
(* example: elim /(measure_ind length) : l. *)
Lemma measure_ind {X : Type} (f : X -> nat) (P : X -> Prop) : 
  (forall x, (forall y, f y < f x -> P y) -> P x) -> forall (x : X), P x.
Proof.
  apply : well_founded_ind.
  apply : Wf_nat.well_founded_lt_compat. move => *. by eassumption.
Qed.
Arguments measure_ind {X}.

End Facts.

Section ForallNorm.

Variable T : Type.
Variable P : T -> Prop.

Lemma Forall_nilP : Forall P [] <-> True.
Proof. by constructor. Qed.

Lemma Forall_consP {a A} : Forall P (a :: A) <-> P a /\ Forall P A.
Proof.
  constructor. 
    move=> H. by inversion H.
  move=> [? ?]. by constructor.
Qed.

Lemma Forall_singletonP {a} : Forall P [a] <-> P a.
Proof. rewrite Forall_consP Forall_nilP. by tauto. Qed.

Lemma Forall_appP {A B}: Forall P (A ++ B) <-> Forall P A /\ Forall P B.
Proof.
  elim: A.
    constructor; by [|case].
  move=> ? ? IH /=. rewrite ? Forall_consP ? IH.
  by tauto.
Qed.

(* usage rewrite ? Forall_norm *)
Definition Forall_norm := (@Forall_appP, @Forall_singletonP, @Forall_consP, @Forall_nilP).

End ForallNorm.

(* any list is empty or has a last element *)
Lemma nil_or_ex_last {T: Type} (A: list T) : A = [] \/ exists B a, A = B ++ [a].
Proof.
  elim: A; first by left.
  move=> a A. case.
  - move=> ->. right. by exists [], a.
  - move=> [B [b ->]]. right. by exists (a :: B), b.
Qed.

(* induction wrt the last element of a list *)
Lemma list_last_ind (X: Type) (P : list X -> Prop) : 
  P [] ->
  (forall a A, P A -> P (A ++ [a])) ->
  forall (A : list X), P A.
Proof.
  move=> H1 H2. elim /(measure_ind (@length X)).
  move=> A IH. case: (nil_or_ex_last A); first by move=> ->.
  move=> [B [a ?]]. subst A. apply: H2. apply: IH.
  rewrite app_length /length. by lia.
Qed.

Arguments list_last_ind [X].

Lemma incl_consP {X: Type} {a: X} {A B} : incl (a :: A) B <-> (In a B /\ incl A B).
Proof. by rewrite /incl -?Forall_forall ?Forall_norm. Qed.
