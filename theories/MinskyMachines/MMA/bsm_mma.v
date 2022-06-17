(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List Arith Lia.

From Undecidability.Shared.Libs.DLW 
  Require Import utils list_bool pos vec sss compiler_correction.

From Undecidability.StackMachines.BSM
  Require Import bsm_defs.

From Undecidability.MinskyMachines.MMA
  Require Import mma_defs mma_utils_bsm.

Set Implicit Arguments.
Set Default Goal Selector "!".

(* ** BSM(n) reduces to MMA(1+n) *)

Tactic Notation "rew" "length" := autorewrite with length_db.

#[local] Notation "e #> x" := (vec_pos e x).
#[local] Notation "e [ v / x ]" := (vec_change e x v).

#[local] Notation "I '/BSM/' s -1> t" := (bsm_sss I s t) (at level 70, no associativity).
#[local] Notation "P '/MMA/' s -+> t" := (sss_progress (@mma_sss _) P s t) (at level 70, no associativity).

Section bsm_mma_compiler.

  Ltac dest x y := destruct (pos_eq_dec x y) as [ | ]; [ subst x | ]; rew vec.

  Variables (m : nat).

  (** We consider BSM with m stacks and build a compiler to MMA with n:=1+m registers. 
      Each stack i : pos m is encoded in registers 1+i : pos (1+m) using stack_enc.
      The (globally) zero valued register pos0 is used for internal computations *)

  (* The registers of the MMA *)

  Let n := 1+m.
  Let zero :  pos n := pos0.
  Let reg : pos m -> pos n := @pos_nxt _.
   
  Local Fact Hrz  : forall p, reg p <> zero.  Proof. discriminate. Qed.
  Local Fact Hreg : forall p q, reg p = reg q -> p = q.
  Proof. intros ? ? H; apply pos_nxt_inj, H. Qed.

  Hint Resolve Hrz Hreg : core.

  (* The encoding of BSM states *)

  Let bsm_state_equiv (v : vec _ m) (w : vec _ n) := 
            w#>zero = 0
         /\ forall p, w#>(reg p) = stack_enc (v#>p).

  Infix "⋈" := bsm_state_equiv (at level 70, no associativity).

  (* The compiler from the generic one: we only need to
     explain how to simulate each individual instruction *)

  Section compiler.

    Implicit Type ρ : bsm_instr m.

    Local Definition bsm_instr_compile lnk i ρ :=
      match ρ with
        | PUSH s Zero => mma_push_Zero (reg s) zero (lnk i)
        | PUSH s One  => mma_push_One  (reg s) zero (lnk i)
        | POP  s j k  => mma_pop (reg s) zero (lnk i) (lnk j) (lnk (1+i)) (lnk k)
      end.

    Local Definition bsm_instr_compile_length ρ :=
      match ρ with 
        | PUSH _ Zero => 10
        | PUSH _ One  => 11
        | POP  _ _ _  => 19
      end.

    Local Fact bsm_instr_compile_length_eq lnk i ρ : 
          length (bsm_instr_compile lnk i ρ) = bsm_instr_compile_length ρ.
    Proof. destruct ρ as [ | ? [] ]; simpl; auto. Qed.

    (* This main soundness lemma per simulated instruction *)

    Local Lemma bsm_instr_compile_sound : 
        instruction_compiler_sound bsm_instr_compile 
                                   (@bsm_sss _) 
                                   (@mma_sss _) 
                                   bsm_state_equiv.
    Proof.
      intros lnk ρ i1 v1 i2 v2 w1 H; revert H w1.
      change v1 with (snd (i1,v1)) at 2.
      change i1 with (fst (i1,v1)) at 2 3 4 6 7 8.
      change v2 with (snd (i2,v2)) at 2.
      change i2 with (fst (i2,v2)) at 2.
      generalize (i1,v1) (i2,v2); clear i1 v1 i2 v2.
      induction 1 as    [ i p j k v Hv
                        | i p j k v ll Hll 
                        | i p j k v ll Hll
                        | i p [] v
                        ]; simpl; intros w1 H0 H; generalize H; intros (H1 & H2).

      + exists w1; split; auto.
        apply mma_pop_void_progress; auto.
        rewrite H2, Hv; auto.

      + exists (w1[(stack_enc ll)/reg p]); repeat split; auto; rew vec.
        * apply mma_pop_Zero_progress; auto.
          rewrite H2, Hll; auto.
        * intros q; dest p q; rew vec.
          assert (reg p <> reg q); rew vec.
    
      + exists (w1[(stack_enc ll)/reg p]); repeat split; auto; rew vec.
        * apply mma_pop_One_progress; auto.
          rewrite H2, Hll; auto.
        * intros q; dest p q.
          assert (reg p <> reg q); rew vec.
   
      + exists (w1[(stack_enc (One::v#>p))/reg p]); repeat split; auto; rew vec.
        * rewrite H0; apply mma_push_One_progress; auto.
        * intros q; dest p q.
          assert (reg p <> reg q); rew vec.

      + exists (w1[(stack_enc (Zero::v#>p))/reg p]); repeat split; auto; rew vec.
        * rewrite H0; apply mma_push_Zero_progress; auto.
        * intros q; dest p q.
          assert (reg p <> reg q); rew vec.
    Qed.

    Hint Resolve bsm_instr_compile_length_eq
                 bsm_instr_compile_sound : core.

    Theorem bsm_mma_compiler : compiler_t (@bsm_sss _) (@mma_sss _) bsm_state_equiv.
    Proof.
      apply generic_compiler 
        with (icomp := bsm_instr_compile)
             (ilen := bsm_instr_compile_length); auto.
      + apply bsm_sss_total'.
      + apply mma_sss_fun.
    Qed.

  End compiler.

End bsm_mma_compiler.

Check bsm_mma_compiler.

