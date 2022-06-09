Set Implicit Arguments.

Class Dec (P: Prop) := dec: {P} + {~P}.
Arguments dec _ {_}.

Class Dec1 {X} (p: X -> Prop) := dec1: forall x, Dec (p x).
Arguments dec1 {_} _ {_}.

Class Dec2 {X Y} (p: X -> Y -> Prop) :=  dec2: forall x, Dec1 (p x).
Arguments dec2 {_} {_} _ {_}.


#[global]
Instance dec_conj P Q: Dec P -> Dec Q -> Dec (P /\ Q).
Proof.
  intros [p|np] [q|nq]; firstorder.
Qed.

#[global]
Instance dec_disj P Q: Dec P -> Dec Q -> Dec (P \/ Q).
Proof.
  intros [p|np] [q|nq]; firstorder.
Qed.

#[global]
Instance dec_imp P Q: Dec P -> Dec Q -> Dec (P -> Q).
Proof.
  intros [p|np] [q|nq]; firstorder.
Qed.

#[global]
Instance dec_iff P Q: Dec P -> Dec Q -> Dec (P <-> Q).
Proof.
  intros; unfold iff; typeclasses eauto. 
Qed.

#[global]
Instance dec_neg P: Dec P -> Dec (~ P).
Proof.
  intros [p|np]; firstorder.
Qed.

Lemma iff_dec P Q: Q <-> P -> Dec P -> Dec Q.
Proof. firstorder. Qed.


#[global]
Instance dec1_dec X P (x: X): Dec1 P -> (Dec (P x)).
Proof. intros H; apply H. Qed.

#[global]
Instance dec1_conj X (P: X -> Prop) (Q: X -> Prop): Dec1 P -> Dec1 Q -> Dec1 (fun x => P x /\ Q x).
Proof.
  intros Hp Hq x; typeclasses eauto.
Qed.

#[global]
Instance dec1_disj X (P: X -> Prop) (Q: X -> Prop): Dec1 P -> Dec1 Q -> Dec1 (fun x => P x \/ Q x).
Proof.
  intros Hp Hq x; typeclasses eauto.
Qed.

#[global]
Instance dec1_imp X (P: X -> Prop) (Q: X -> Prop): Dec1 P -> Dec1 Q -> Dec1 (fun x => P x -> Q x).
Proof.
  intros Hp Hq x; typeclasses eauto.
Qed.

#[global]
Instance dec1_iff X (P: X -> Prop) (Q: X -> Prop): Dec1 P -> Dec1 Q -> Dec1 (fun x => P x <-> Q x).
Proof.
  intros Hp Hq x; typeclasses eauto.
Qed.

#[global]
Instance dec1_neg X (P: X -> Prop): Dec1 P ->  Dec1 (fun x => ~ P x).
Proof.
  intros Hq x; typeclasses eauto.
Qed.


#[global]
Instance dec2_dec1 X Y (P: X -> Y -> Prop)  x: Dec2 P -> Dec1 (P x).
Proof. intros H; apply H. Qed.

#[global]
Instance dec2_dec1' X Y (P: X -> Y -> Prop) y: Dec2 P -> Dec1 (fun x => P x y).
Proof. intros H x; apply H. Qed.


#[global]
Instance dec2_conj X Y (P: X -> Y -> Prop) (Q: X -> Y -> Prop): Dec2 P -> Dec2 Q -> Dec2 (fun x y => P x y /\ Q x y).
Proof.
  intros Hp Hq x; typeclasses eauto.
Qed.

#[global]
Instance dec2_disj X Y (P: X -> Y -> Prop) (Q: X -> Y -> Prop): Dec2 P -> Dec2 Q -> Dec2 (fun x y => P x y \/ Q x y).
Proof.
  intros Hp Hq x; typeclasses eauto.
Qed.

#[global]
Instance dec2_imp X Y (P: X -> Y -> Prop) (Q: X -> Y -> Prop): Dec2 P -> Dec2 Q -> Dec2 (fun x y => P x y -> Q x y).
Proof.
  intros Hp Hq x; typeclasses eauto.
Qed.

#[global]
Instance dec2_iff X Y (P: X -> Y -> Prop) (Q: X -> Y -> Prop): Dec2 P -> Dec2 Q -> Dec2 (fun x y => P x y <-> Q x y).
Proof.
  intros Hp Hq x; typeclasses eauto.
Qed.

#[global]
Instance dec2_neg X Y (P: X -> Y -> Prop): Dec2 P ->  Dec2 (fun x y => ~ P x y).
Proof.
  intros Hq x; typeclasses eauto.
Qed.



Section DecBool.
  Definition decb P {D: Dec P} := if dec P then true else false.
  Arguments decb _ {_}.

  Definition decb1 {X: Type} (Q: X -> Prop) {D: Dec1 Q} x := decb (Q x).
  Arguments decb1 {_} _ {_} _.

  Definition decb2 {X Y: Type} (R: X -> Y -> Prop) {D: Dec2 R} x := decb1 (R x).
  Arguments decb2 {_} {_} _ {_} _.

  Lemma dec_decb (P: Prop) {D: Dec P}: P -> decb P = true.
  Proof.
    unfold decb; destruct (dec P); intuition; discriminate.
  Qed.

  Lemma decb_dec (P: Prop) {D: Dec P}: decb P = true -> P.
  Proof.
    unfold decb; destruct (dec P); intuition; discriminate.
  Qed.

End DecBool.

#[export] Hint Resolve dec_decb : core.
Arguments decb _ {_}.
Arguments decb1 {_} _ {_} _.
Arguments decb2 {_} {_} _ {_} _.

(* Discreteness *)

Class Dis (X: Type) := eq_dec: Dec2 (@eq X). 

Notation "a == b" := (eq_dec a b) (at level 60).

#[global]
Instance dis_dec X (D: Dis X): Dec2 (@eq X).
Proof. firstorder. Qed.

#[global]
Instance discrete_False: Dis False.
Proof.
  unfold Dis, Dec2, Dec1, Dec; decide equality.
Qed.

#[global]
Instance discrete_unit: Dis unit.
Proof.
  unfold Dis, Dec2, Dec1, Dec; decide equality.
Qed.

#[global]
Instance discrete_nat: Dis nat.
Proof.
   unfold Dis, Dec2, Dec1, Dec; decide equality.
Qed.


#[global]
Instance discrete_bool: Dis bool.
Proof.
  unfold Dis, Dec2, Dec1, Dec; decide equality.
Qed.

#[global]
Instance discrete_option (X: Type) {D: Dis X}: Dis (option X).
Proof.
  unfold Dis, Dec2, Dec1, Dec; decide equality.
  eapply eq_dec.
Qed.

#[global]
Instance discrete_sum (X Y: Type) {D1: Dis X} {D2: Dis Y}: Dis (X + Y).
Proof.
  unfold Dis, Dec2, Dec1, Dec; decide equality.
  all: eapply eq_dec. 
Qed.

#[global]
Instance discrete_prod (X Y: Type) {D1: Dis X} {D2: Dis Y}: Dis (X * Y).
Proof.
  unfold Dis, Dec2, Dec1, Dec; decide equality.
  all: eapply eq_dec.
Qed.

#[global]
Instance discrete_list (X: Type) {D: Dis X}: Dis (list X).
Proof.
  unfold Dis, Dec2, Dec1, Dec; decide equality.
  eapply eq_dec.
Qed.



Require Import List Arith Lia.

#[global]
Instance In_dec (X: Type) {D: Dis X}: Dec2 (@In X).
Proof.
  intros ??; eapply in_dec, eq_dec.
Qed.

Definition dec_in {X: Type} {D: Dis X} (x: X) (A: list X) :=
  dec2 (@In X) x A.  

Notation "x 'el' A" := (dec_in x A) (at level 60).

#[global]
Instance lt_dec : Dec2 lt.
Proof.
  intros ??; eapply lt_dec.
Qed.

#[global]
Instance le_dec : Dec2 le.
Proof.
  intros ??; eapply le_dec.
Qed.

#[global]
Instance gt_dec : Dec2 gt.
Proof.
  intros ??; eapply lt_dec.
Qed.

#[global]
Instance ge_dec : Dec2 ge.
Proof.
  intros ??; eapply le_dec.
Qed.

#[global]
Instance dec_all Y (P: Y -> Prop) (D: Dec1 P):
  Dec1 (fun A => forall x, In x A -> P x).
Proof.
  intros A. eapply iff_dec; [symmetry; eapply Forall_forall|].
  unfold Dec; eapply Forall_dec; eauto.
Qed.
