From Undecidability.Shared.Libs.PSL Require Import BasicDefinitions.
From Undecidability.Shared.Libs.PSL Require Import FiniteTypes.FinTypes.
From Undecidability.Shared.Libs.PSL Require Import Vectors.Vectors.
From Undecidability.Shared.Libs.PSL Require Import Vectors.VectorDupfree.
Import VectorNotations2.
From Undecidability.Shared.Libs.PSL Require Import FiniteTypes.Cardinality.

Definition Fin_initVect (n : nat) : Vector.t (Fin.t n) n :=
  tabulate (fun i : Fin.t n => i).

Lemma Fin_initVect_dupfree n :
  dupfree (Fin_initVect n).
Proof.
  unfold Fin_initVect.
  eapply dupfree_tabulate_injective.
  firstorder.
Qed.

Lemma Fin_initVect_full n k :
  Vector.In k (Fin_initVect n).
Proof.
  unfold Fin_initVect.
  apply in_tabulate. eauto.
Qed.

Definition Fin_initVect_nth (n : nat) (k : Fin.t n) :
  Vector.nth (Fin_initVect n) k = k.
Proof. unfold Fin_initVect. apply nth_tabulate. Qed.

Import VecToListCoercion.

Instance Fin_finTypeC n : finTypeC (EqType (Fin.t n)).
Proof.
  constructor 1 with (enum := Fin_initVect n).
  intros x. cbn in x.
  eapply dupfreeCount.
  - eapply tolist_dupfree. apply Fin_initVect_dupfree.
  - eapply tolist_In. apply Fin_initVect_full.
Defined.

Hint Extern 4 (finTypeC (EqType (Fin.t _))) => eapply Fin_finTypeC : typeclass_instances.

Lemma Fin_cardinality n : Cardinality (finType_CS (Fin.t n)) = n.
Proof.
  unfold Cardinality, elem, enum. cbn. unfold Fin_initVect. now rewrite vector_to_list_length. 
Qed.

(* Function that produces a list of all Vectors of length n over A *)
Fixpoint Vector_pow {X: Type} (A: list X) n {struct n} : list (Vector.t X n) :=
  match n with
  | 0 => [Vector.nil _]
  | S n => concat (map (fun a => map (fun v => a:::v) (Vector_pow A n) ) A)
  end.

Instance Vector_finTypeC (A:finType) n: finTypeC (EqType (Vector.t A n)).
Proof.
  exists (undup ((Vector_pow (elem A) n))). cbn in *.
  intros v. eapply dupfreeCount.
  - eapply dupfree_undup.
  - rewrite undup_id_equi. induction v; cbn.
    + eauto.
    + eapply in_concat_iff. eexists; split.
      2:eapply in_map_iff. 2:eexists.
      2:split. 2:reflexivity.
      eapply in_map_iff. eauto.
      eapply elem_spec.
Defined.
      
Hint Extern 4 (finTypeC (EqType (Vector.t _ _))) => eapply Vector_finTypeC : typeclass_instances.


Lemma ProdCount (T1 T2: eqType) (A: list T1) (B: list T2) (a:T1) (b:T2)  :
  BasicDefinitions.count (prodLists A B) (a,b) =  BasicDefinitions.count A a * BasicDefinitions.count B b .
Proof.
  induction A.
  - reflexivity.
  - cbn. rewrite <- countSplit. decide (a = a0) as [E | E].
    + cbn. f_equal. subst a0. apply countMap. eauto.
    + rewrite <- plus_O_n. f_equal. now apply countMapZero. eauto.
Qed.

Lemma prod_enum_ok (T1 T2: finType) (x: T1 * T2):
  BasicDefinitions.count (prodLists (elem T1) (elem T2)) x = 1.
Proof.
  destruct x as [x y]. rewrite ProdCount. unfold elem.
  now repeat rewrite enum_ok.
Qed.

Instance finTypeC_Prod (F1 F2: finType) : finTypeC (EqType (F1 * F2)).
Proof.
  econstructor.  apply prod_enum_ok.
Defined.
