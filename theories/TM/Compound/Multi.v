From Undecidability Require Import TM.Util.Prelim.
From Undecidability Require Import TM.Util.TM_facts.
From Undecidability Require Import TM.Basic.Mono.
From Undecidability Require Import TM.Combinators.Combinators.

From Undecidability Require Import TM.Compound.TMTac.

(* * Simple compound multi-tape Machines *)


(* ** Nop *)

(* The n-tape Machine that does nothing *)
Section Nop.
  Variable sig : finType.
  Variable n : nat.

  Definition NopTM : TM sig n :=
    {|
      trans := fun '(q, s) => (q, Vector.const (None, Nmove) n);
      start := tt;
      halt _ := true;
    |}.

  Definition Nop : pTM sig unit n := (NopTM; fun _ => tt).

  Definition Nop_Rel : pRel sig unit n :=
    ignoreParam (fun t t' => t' = t).

  Lemma Nop_Sem : Nop ⊨c(0) Nop_Rel.
  Proof.
    intros t. cbn. unfold initc; cbn. eexists (mk_mconfig _ _); cbn; eauto.
  Qed.

End Nop.

Arguments Nop_Rel {sig n} x y/.
Arguments Nop {sig n}.
Arguments Nop : simpl never.

#[export] Hint Extern 1 (Nop ⊨ _) => eapply RealiseIn_Realise; eapply Nop_Sem : TMdb.
#[export] Hint Extern 1 (Nop ⊨c(_) _) => eapply Nop_Sem : TMdb.
#[export] Hint Extern 1 (projT1 (Nop) ↓ _) => eapply RealiseIn_TerminatesIn; apply Nop_Sem : TMdb.
