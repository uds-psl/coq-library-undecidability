Require Import PslBase.FiniteTypes.FinTypes PslBase.Vectors.Vectors.
Require Import Vector List.

Require Import Undecidability.TM.Util.TM_facts.

From Undecidability Require Import ProgrammingTools WriteValue Copy ListTM  JumpTargetTM WriteValue.
From Undecidability.TM.L Require Import Alphabets LookupTM.
From Undecidability.L.AbstractMachines.FlatPro Require Import LM_heap_def LM_heap_correct.
From Undecidability Require Import L.L TM.TM.
Require Import List.
Import ListNotations.


Import VectorNotations.

Require Import Equations.Prop.DepElim.


Module UnfoldHeap.
Section Fix.

  Variable Σ : finType.

  Variable retr_closures : Retract (sigList sigHClos) Σ.
  Variable retr_heap : Retract sigHeap Σ.

  Axiom retr_closures_REMOVE : Retract (sigList sigHClos) Σ.

  (** Retracts *)
  (* Closures *)
  Local Definition retr_clos : Retract sigHClos Σ := ComposeRetract retr_closures _.

  (* Closure addresses *)

  Definition retr_pro_clos : Retract sigPro sigHClos := _.
  Local Definition retr_pro : Retract sigPro Σ := ComposeRetract retr_clos retr_pro_clos.
  Local Definition retr_tok : Retract sigCom Σ := ComposeRetract retr_pro _.

  Local Definition retr_nat_clos_ad : Retract sigNat sigHClos := Retract_sigPair_X _ (Retract_id _).
  Local Definition retr_nat_step_clos_ad : Retract sigNat Σ := ComposeRetract retr_clos retr_nat_clos_ad.

  Local Definition retr_nat_clos_var : Retract sigNat sigHClos := Retract_sigPair_Y _ _.
  Local Definition retr_nat_step_clos_var : Retract sigNat Σ := ComposeRetract retr_clos retr_nat_clos_var.

  (** Instance of the [Lookup] and [JumpTarget] machine *)
  Local Definition Step_Lookup := Lookup retr_clos retr_heap.

    Variable n : nat.

    Variable i_g : Fin.t n.
    Variable i_H : Fin.t n.
    Variable o_t : Fin.t n.

    Definition M : pTM (Σ) ^+ unit n. Admitted.

    Theorem Realises :
    Realise M (fun t '(r, t') =>
                        forall g, forall H : Heap, 
                            t[@i_g] ≃(retr_closures_REMOVE) [g]%list (*TODO: change to clos?*) ->
                            t[@i_H] ≃ H ->
                            exists t,
                            reprC H g t /\
                            t'[@o_t] ≃(retr_pro) compile t).
    
    Admitted.

End Fix.
End UnfoldHeap.