From Undecidability Require Import TM.Code.ProgrammingTools.
From Undecidability Require Import TM.Code.CaseNat.

(* Minus x y computes x - y and returns whether x >= y (e.g., if the subtraction did not need to truncate) *)

Definition Subtract_Rel : pRel (sigNat^+) bool 2 :=
    fun tin '(b, tout) =>
    forall (x y : nat),  
        tin [@Fin0] ≃ x
        -> tin [@Fin1] ≃ y
        -> tout [@Fin0] ≃ x - y
        /\ isVoid tout [@Fin1]
        /\ b = (y <=? x).

Definition Subtract :pTM (sigNat^+) bool 2:=
    While (
        If(CaseNat @ [|Fin1|])
          (If (CaseNat @ [|Fin0|])
              (Return Nop None)
              (Return (Reset _ @ [|Fin1|]) (Some false)) )
          (Return (Reset _ @ [|Fin1|]) (Some true))  
    ).


Lemma Subtract_Realise : Subtract ⊨ Subtract_Rel.
Proof.
  eapply Realise_monotone.
  {
    unfold Subtract. TM_Correct. all: (try (notypeclasses refine (@Reset_Realise _ _ _ _ _);shelve)).
  }
  {
    apply WhileInduction.
    - intros tin b tout [(t0_&Hif1&[Hif2|[t1_ Hif2]]) |?] x y;TMSimp;[ | ].
      + modpon H. modpon H2. destruct y. easy. destruct x. 2:easy.
        modpon H1. rewrite Nat.sub_0_l. cbn ["<=?"]. repeat split. contains_ext. isVoid_mono.
      + modpon H. destruct y. 2:easy.
        modpon H1. rewrite Nat.sub_0_r. cbn ["<=?"]. repeat split. contains_ext. isVoid_mono.
    - intros tin tmid tout b [(t0_&Hif1&[Hif2|[t1_ Hif2]]) |?] H' x y;TMSimp;[].
      modpon H. modpon H1. destruct x,y;try contradiction;[].
      modpon H'. rewrite Nat.sub_succ. cbn ["<=?"]. easy.
  } 
Qed.
