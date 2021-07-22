From Undecidability Require Import BSM BSM_sss bsm_defs.


From Coq Require Import List Vector.
Import ListNotations Vector.VectorNotations.

Definition BSM_computable {k} (R : Vector.t nat k -> nat -> Prop) := 
  exists n : nat, exists i : nat, exists P : list (bsm_instr (1 + k + n)),
    forall v : Vector.t nat k,
      (forall m, R v m <->
         exists c v', BSM.eval (1 + k + n) (i, P) (i, (@List.nil bool :: Vector.map (fun n => List.repeat true n) v) ++ Vector.const (@List.nil bool) n) (c, List.repeat true m :: v'))
    /\ (forall c v', BSM.eval (1 + k + n) (i, P) (i, (@List.nil bool :: Vector.map (fun n => List.repeat true n) v) ++ Vector.const (@List.nil bool) n) (c, v') -> exists m v'', v' = List.repeat true m :: v'').    

Lemma BSM_computable_iff {k} (R : Vector.t nat k -> nat -> Prop) :
  BSM_computable R <->
  exists n : nat, exists i : nat, exists P : list (bsm_instr (1 + k + n)),
    (forall v : Vector.t nat k,forall m, R v m -> exists c v', BSM.eval (1 + k + n) (i, P) (i, (@List.nil bool :: Vector.map (fun n => List.repeat true n) v) ++ Vector.const (@List.nil bool) n) (c, List.repeat true m :: v'))
    /\ (forall v, sss.sss_terminates (@bsm_sss _) (i, P) (i, (@List.nil bool :: Vector.map (fun n => List.repeat true n) v) ++ Vector.const (@List.nil bool) n) -> exists m, R v m).
Proof.
  split.
  - intros (n & i & P & H). exists n, i, P. split.
    + intros v m ? % H; eauto.
    + intros v [(c, v') H1].
      pose proof (H2 := H1). eapply eval_iff in H2 as (m & v'' & H2) % H.
      subst. eapply eval_iff in H1. eexists. eapply H. eexists. eexists. eapply H1.
  - intros (n & i & P & H1 & H2).
    exists n, i, P. intros v. split.
    + intros m. split.
      * intros (c & v' & Hvm) % H1. fold plus in *. exists c, v'. eapply Hvm.
      * intros (c & v' & Hvm % eval_iff). fold plus in *.
        edestruct H2 as [m' H'].
        -- eexists. eassumption.
        -- enough (m' = m) as -> by assumption.
           eapply H1 in H' as (c' & v'' & H' % eval_iff).
           destruct Hvm as [Hvm1 Hvm2].
           eapply sss.sss_compute_fun in Hvm1. 5: eapply H'. 3: eapply H'. 3: eapply Hvm2.
           2: eapply bsm_sss_fun. 
           inversion Hvm1. eapply (f_equal (@length bool)) in H3.
           now rewrite !repeat_length in H3.
    + intros c v' H % eval_iff. edestruct H2 as [m Hm]. { eexists. eauto. }
      eapply H1 in Hm as (c' & v'' & [Hm1 Hm2] % eval_iff). fold plus in *. exists m, v''.
      eapply sss.sss_compute_fun in Hm1. 5: eapply H. 3: eapply H. 3: eapply Hm2.
      2: eapply bsm_sss_fun. 
      inversion Hm1. congruence.
Qed.

    
    
    
