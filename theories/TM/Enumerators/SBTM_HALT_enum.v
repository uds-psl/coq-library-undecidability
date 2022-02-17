From Undecidability.Synthetic Require Import Definitions EnumerabilityFacts.
From Undecidability.Synthetic Require ListEnumerabilityFacts.

Require Import Undecidability.TM.SBTM.
Import SBTMNotations.

(* semi-decider for SBTM_HALT *)
Lemma SBTM_HALT_semi_decision : { f : { M : SBTM & config M } -> nat -> bool | semi_decider f SBTM_HALT }.
Proof.
  exists (fun '(existT _ M x) k => match steps M k x with | Some _ => false | None => true end).
  intros [M x]. split.
  + intros [k Hk]. exists k. now rewrite Hk.
  + intros [k Hk]. exists k.
    now destruct (steps M k x) as [?|].
Qed.

Definition SBTM_to_sigT (M : SBTM) := existT 
  (fun n => Vector.t (option (Fin.t n * _ * _) * option (Fin.t n * _ * _)) n) (num_states M) (trans M).
Definition SBTM_of_sigT := fun '(existT _ n t) => @Build_SBTM n t.

Lemma direction_enumeration : { e | enumerator__T e direction}.
Proof.
  exists (fun n => match n with 0 => Some go_left | _ => Some go_right end).
  now intros []; [exists 0|exists 1].
Qed.

Lemma SBTM_enumeration : { e : nat -> option SBTM | enumerator__T e SBTM }.
Proof.
  assert {f | enumerator__T f {n : nat & Vector.t
    (option (Fin.t n * bool * direction) *
    option (Fin.t n * bool * direction)) n}} as [f Hf].
  { eexists.
    eapply enumerator__T_sigT.
    - apply enumerator__T_nat.
    - intros x. apply enumerator__T_Vector.
      apply enumerator__T_prod.
      + apply enumerator__T_option.
        apply enumerator__T_prod; [apply enumerator__T_prod|].
        * apply enumerator__T_Fin.
        * apply enumerator__T_bool.
        * apply (proj2_sig direction_enumeration).
      + apply enumerator__T_option.
        apply enumerator__T_prod; [apply enumerator__T_prod|].
        * apply enumerator__T_Fin.
        * apply enumerator__T_bool.
        * apply (proj2_sig direction_enumeration). }
  exists (fun n => ssrfun.omap SBTM_of_sigT (f n)).
  intros M.
  destruct (Hf (SBTM_to_sigT M)) as [n Hn].
  exists n. rewrite Hn. now destruct M.
Qed.

Lemma config_enumeration (M : SBTM) : { e : nat -> option (config M) | enumerator__T e (config M) }.
Proof.
  eexists. apply enumerator__T_prod.
  + apply enumerator__T_Fin.
  + apply enumerator__T_prod; [apply enumerator__T_prod|].
    * eapply ListEnumerabilityFacts.enumerator__T_to_list.
      eapply ListEnumerabilityFacts.enumerator__T_list.
      eapply ListEnumerabilityFacts.enumerator__T_of_list.
      apply enumerator__T_bool.
    * apply enumerator__T_bool.
    * eapply ListEnumerabilityFacts.enumerator__T_to_list.
      eapply ListEnumerabilityFacts.enumerator__T_list.
      eapply ListEnumerabilityFacts.enumerator__T_of_list.
      apply enumerator__T_bool.
Qed.

Lemma SBTM_HALT_INSTANCE_enumeration : { e | enumerator__T e {M : SBTM & config M }}.
Proof.
  eexists.
  apply enumerator__T_sigT.
  - apply (proj2_sig SBTM_enumeration).
  - intros M. apply (proj2_sig (config_enumeration M)).
Qed.

(* enumerator for SBTM_HALT *)
Lemma SBTM_HALT_enumeration : { e : nat -> option { M : SBTM & config M } | enumerator e SBTM_HALT }.
Proof.
  exact (semi_decider_enumerator 
    (proj2_sig SBTM_HALT_INSTANCE_enumeration)
    (proj2_sig SBTM_HALT_semi_decision)).
Qed.

Definition SBTM_HALT_enumerator := proj1_sig SBTM_HALT_enumeration.

Lemma SBTM_HALT_enumerator_spec : enumerator SBTM_HALT_enumerator SBTM_HALT.
Proof. exact (proj2_sig SBTM_HALT_enumeration). Qed.
