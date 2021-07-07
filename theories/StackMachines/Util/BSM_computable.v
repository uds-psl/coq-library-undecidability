From Undecidability Require Import BSM BSM_sss.

From Coq Require Import List Vector.
Import ListNotations Vector.VectorNotations.

Definition BSM_computable {k} (R : Vector.t nat k -> nat -> Prop) := 
  exists n : nat, exists i : nat, exists P : list (bsm_instr (1 + k + n)),
    forall v : Vector.t nat k,
      (forall m, R v m <->
         exists c v', BSM.eval (1 + k + n) (i, P) (i, (@List.nil bool :: Vector.map (fun n => List.repeat true n) v) ++ Vector.const (@List.nil bool) n) (c, List.repeat true m :: v'))
    /\ (forall c v', BSM.eval (1 + k + n) (i, P) (i, (@List.nil bool :: Vector.map (fun n => List.repeat true n) v) ++ Vector.const (@List.nil bool) n) (c, v') -> exists m v'', v' = List.repeat true m :: v'').    

Lemma BSM_computable_iff {k} (R : Vector.t nat k -> nat -> Prop) :
  BSM_computable R ->
  exists n : nat, exists i : nat, exists P : list (bsm_instr (1 + k + n)),
    (forall v : Vector.t nat k,forall m, R v m -> exists c v', BSM.eval (1 + k + n) (i, P) (i, (@List.nil bool :: Vector.map (fun n => List.repeat true n) v) ++ Vector.const (@List.nil bool) n) (c, List.repeat true m :: v'))
    /\ (forall v, sss.sss_terminates (@bsm_sss _) (i, P) (i, (@List.nil bool :: Vector.map (fun n => List.repeat true n) v) ++ Vector.const (@List.nil bool) n) -> exists m, R v m).
Proof.
  intros (n & i & P & H). exists n, i, P. split.
  - intros v m ? % H; eauto.
  - intros v [(c, v') H1].
    pose proof (H2 := H1). eapply eval_iff in H2 as (m & v'' & H2) % H.
    subst. eapply eval_iff in H1. eexists. eapply H. eexists. eexists. eapply H1.
Qed.

    
    
    
