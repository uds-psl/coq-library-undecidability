Require Export ILL.Prelim.Prelim.

(** * Post Corresepondence Problem *)

Definition reduces X Y (p : X -> Prop) (q : Y -> Prop) := exists f : X -> Y, forall x, p x <-> q (f x).
Notation "p ⪯ q" := (reduces p q) (at level 50).

Lemma reduces_transitive X Y Z (p : X -> Prop) (q : Y -> Prop) (r : Z -> Prop) :
  p ⪯ q -> q ⪯ r -> p ⪯ r.
Proof.
  intros [f ?] [g ?]. exists (fun x => g (f x)). firstorder.
Qed.

Definition symbol := nat.
Definition string X := list X.
Definition card X : Type := string X * string X.
Definition stack X := list (card X).
Definition SRS := stack nat.
Definition BSRS := stack bool.

Notation "x / y" := (x,y).

(** ** Post correspondence problem over natural numbers *)

Fixpoint tau1 (X : Type) (A : stack X) : string X :=
  match A with
  | [] => []
  | (x / y) :: A => x ++ tau1 A
  end.

Fixpoint tau2 X (A : stack X) : string X :=
  match A with
  | [] => []
  | (x / y) :: A => y ++ tau2 A
  end.

Definition PCP P := exists A : SRS, A <<= P /\ A <> [] /\ tau1 A = tau2 A.


(** ** Binary Post correspondence problem *)

Definition BPCP P := exists A : BSRS, A <<= P /\ A <> [] /\ tau1 A = tau2 A.

(** ** Binary Post correspondence problem with indices *)

Section itau.

  Variable P : BSRS.

  Fixpoint itau1 (A : list nat) : string bool :=
    match A with
      | [] => []
      | i :: A => fst (nth i P ( [] / [] )) ++ itau1 A
  end.

  Fixpoint itau2 (A : list nat) : string bool :=
    match A with
      | [] => []
      | i :: A => snd (nth i P ( [] / [] )) ++ itau2 A
    end.

  Fact itau1_app A B : itau1 (A++B) = itau1 A ++ itau1 B.
  Proof. induction A; simpl; auto; rewrite app_ass; simpl; f_equal; auto. Qed.

   Fact itau2_app A B : itau2 (A++B) = itau2 A ++ itau2 B.
  Proof. induction A; simpl; auto; rewrite app_ass; simpl; f_equal; auto. Qed.

End itau.

Definition iBPCP (P : BSRS) :=
  exists A : list nat, (forall a, a el A -> a < length P) /\ A <> [] /\ itau1 P A = itau2 P A.
