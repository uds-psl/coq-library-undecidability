From Undecidability.Shared.Libs.PSL Require Import BasicDefinitions.
From Undecidability.Shared.Libs.PSL Require Import FiniteTypes.FinTypes.
From Undecidability.Shared.Libs.PSL Require Import Vectors.Vectors.
From Undecidability.Shared.Libs.PSL Require Import Vectors.VectorDupfree.
Import VectorNotations2.

Import VecToListCoercion.

#[global]
Instance Fin_finTypeC n : finTypeC (EqType (Fin.t n)).
Proof.
  constructor 1 with (enum := tabulate (fun i : Fin.t n => i)).
  cbn. intros x. eapply dupfreeCount.
  - eapply tolist_dupfree. now eapply dupfree_tabulate_injective.
  - eapply Vector.to_list_In. apply in_tabulate. now eexists.
Defined.

(* Function that produces a list of all Vectors of length n over A *)
Fixpoint Vector_pow {X: Type} (A: list X) n {struct n} : list (Vector.t X n) :=
  match n with
  | 0 => [Vector.nil _]
  | S n => concat (map (fun a => map (fun v => a:::v) (Vector_pow A n) ) A)
  end.

#[global]
Instance Vector_finTypeC (A:finType) n: finTypeC (EqType (Vector.t A n)).
Proof.
  exists (undup ((Vector_pow (elem A) n))). cbn in *.
  intros v. eapply dupfreeCount.
  - eapply NoDup_nodup.
  - apply nodup_In. induction v; cbn.
    + eauto.
    + eapply in_concat. eexists; split.
      eapply in_map_iff. eexists.
      split. reflexivity.
      2:eapply in_map_iff. 2:eauto.
      eapply elem_spec.
Defined.
      
#[export] Hint Extern 4 (finTypeC (EqType (Vector.t _ _))) => eapply Vector_finTypeC : typeclass_instances.
