From Undecidability.Shared.Libs.PSL Require Import FinTypes.

(* * Definition of prod as finType *)
Lemma ProdCount (T1 T2: eqType) (A: list T1) (B: list T2) (a:T1) (b:T2)  :
  count (list_prod A B) (a,b) =  count A a * count B b .
Proof.
  induction A.
  - reflexivity.
  - cbn. rewrite <- countSplit. decide (a = a0) as [E | E].
    + cbn. f_equal. subst a0. apply countMap. eauto.
    + rewrite <- plus_O_n. f_equal. now apply countMapZero. eauto.
Qed.

Lemma prod_enum_ok (T1 T2: finType) (x: T1 * T2):
  count (list_prod (elem T1) (elem T2)) x = 1.
Proof.
  destruct x as [x y]. rewrite ProdCount. unfold elem.
  now repeat rewrite enum_ok.
Qed.

#[global]
Instance finTypeC_Prod (F1 F2: finType) : finTypeC (EqType (F1 * F2)).
Proof.
  econstructor.  apply prod_enum_ok.
Defined.

(* * Definition of option as finType *)

(* Wrapping elements in "Some" does not change the number of occurences in a list *)
Lemma SomeElement (X: eqType) (A: list X) x:
  count (toOptionList A) (Some x) = count A x .
Proof.
  unfold toOptionList. simpl. dec; try congruence.
  induction A.
  + tauto.  
  + simpl. dec; congruence.
Qed.

(* A list produced by toOptionList contains None exactly once *)
Lemma NoneElement (X: eqType) (A: list X) :
  count (toOptionList A) None = 1.
Proof.
  unfold toOptionList. simpl. dec; try congruence. f_equal.
  induction A.
  - reflexivity.
  - simpl; dec; congruence.    
Qed.

Lemma option_enum_ok (T: finType) x :
  count (toOptionList (elem T)) x = 1.
Proof.
  destruct x.
  + rewrite SomeElement. apply enum_ok.
  + apply NoneElement.
Qed.

#[global]
Instance  finTypeC_Option(F: finType): finTypeC (EqType (option F)).
Proof.
  eapply FinTypeC.  apply option_enum_ok.
Defined.

(* * Definition of sum as finType *)

(* The sum of two nats can only be 1 if one of them is 1 and the other one is 0 *)
Lemma proveOne m n: m = 1 /\ n = 0 \/ n = 1 /\ m = 0 -> m + n = 1.
Proof.
  lia.
Qed.


(* toSumlist1 does not change the number of occurences of an existing element in the list *)
Lemma toSumList1_count (X: eqType) (x: X) (Y: eqType) (A: list X) :
  count (toSumList1 Y A) (inl x) =  count A x .
Proof.
  induction A; simpl; dec; congruence.  
Qed.

(* toSumlist2 odes not change the numbe of occurences of an existing element in the list *)
Lemma toSumList2_count (X Y: eqType) (y: Y) (A: list Y):
  count (toSumList2 X A) (inr y) = count A y.
Proof.
  induction A; simpl; dec; congruence.  
Qed.

(* to sumList1 does not produce inr proofs *)
Lemma toSumList1_missing (X Y: eqType) (y: Y) (A: list X):
  count (toSumList1 Y A ) (inr y) = 0.                           
Proof.
  induction A; dec; firstorder.
Qed.

(* toSumlist2 does not produce inl proofs *)
Lemma toSumList2_missing (X Y: eqType) (x: X) (A: list Y):
  count (toSumList2 X A ) (inl x) = 0.                           
Proof.
  induction A; dec; firstorder.
Qed.

Lemma sum_enum_ok (X: finType) (Y: finType) x :
  count (toSumList1 Y (elem X) ++ toSumList2 X (elem Y)) x = 1.
Proof.
  rewrite <- countSplit. apply proveOne. destruct x.
  - left. split; cbn.
    + rewrite toSumList1_count. apply enum_ok.
    + apply toSumList2_missing.
  - right. split; cbn.
    + rewrite toSumList2_count. apply enum_ok.
    + apply toSumList1_missing.
Qed.

(* Instance declaration for sum types for  the type class *)
#[global]
Instance finTypeC_sum (X Y: finType) : finTypeC (EqType ( X + Y)).
Proof.
  eapply FinTypeC. apply sum_enum_ok.
Defined.

(* Some hints to make the typeclass inference work *)

#[export] Hint Extern 4 (finTypeC (EqType (_ * _))) => eapply finTypeC_Prod : typeclass_instances.
#[export] Hint Extern 4 (finTypeC (EqType (_ + _))) => eapply finTypeC_sum : typeclass_instances.
#[export] Hint Extern 4 (finTypeC (EqType (option _))) => eapply finTypeC_Option : typeclass_instances.
