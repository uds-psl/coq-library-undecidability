From Undecidability.L Require Import Tactics.LTactics.
Require Import Numbers.BinNums.

From Undecidability.L.Datatypes Require Import LNat LBool LBinNums.
(** *** Subtraction of binary Numbers *)

Run TemplateProgram (tmGenEncode "mask_enc" Pos.mask).
Hint Resolve mask_enc_correct : Lrewrite.
  
Section pos_sub.

  Import Pos.

  Fixpoint sub_maskC (c:bool) (x y : positive) {struct y} : mask :=
    (if negb c then 
      match x with
      | p~1 => match y with
              | q~1 => double_mask (sub_maskC false p q)
              | q~0 => succ_double_mask (sub_maskC false p q)
              | 1 => IsPos p~0
              end
      | p~0 => match y with
              | q~1 => succ_double_mask (sub_maskC true p q)
              | q~0 => double_mask (sub_maskC false p q)
              | 1 => IsPos (pred_double p)
              end
      | 1 => match y with
            | 1 => IsNul
            | _ => IsNeg
            end
      end
    else
      match x with
      | p~1 => match y with
              | q~1 => succ_double_mask (sub_maskC true p q)
              | q~0 => double_mask (sub_maskC false p q)
              | 1 => IsPos (pred_double p)
              end
      | p~0 => match y with
              | q~1 => double_mask (sub_maskC true p q)
              | q~0 => succ_double_mask (sub_maskC true p q)
              | 1 => double_pred_mask p
              end
      | 1 => IsNeg
      end)%positive.

  Lemma sub_maskC_ext_eq : extEq sub_maskC (fun b => if b then sub_mask_carry else sub_mask).
  Proof.
    intros b x y. induction x in b,y|-*;destruct b,y;cbn;try rewrite !IHx. all:reflexivity.
  Qed.

  Global Instance termT_isPos : computableTime' IsPos (fun x _ => (1,tt)).
  extract constructor. solverec.
  Qed.

  
  Global Instance termT_Pos_double_mask: computableTime' double_mask (fun x _ => (8,tt)).
  extract. solverec.
  Qed.

  Global Instance termT_Pos_succ_double_mask: computableTime' succ_double_mask (fun x _ => (8,tt)).
  extract. solverec.
  Qed.

  Global Instance termT_Pos_pred_double: computableTime' pred_double (fun x _ => (size_nat x * 12 + 9,tt)).
  extract. solverec.
  Qed.
  
  Global Instance termT_Pos_double_pred_mask: computableTime' double_pred_mask (fun x _ => (size_nat x * 12 + 5,tt)).
  extract. solverec.
  Qed.

  Global Instance termT_Pos_pred : computableTime' pred (fun x _ => (size_nat x * 12 + 3,tt)).
  extract. solverec.
  Qed.

  Global Instance termT_Pos_predN : computableTime' pred_N (fun x _ => (size_nat x * 12 + 4,tt)).
  extract. solverec.
  Qed.
  
  Global Instance termT_Pos_sub_maskC: computableTime' sub_maskC (fun b _ => (5%nat,fun x _ => (1%nat,fun y _ => (size_nat x*32,tt)))).
  extract. solverec.
  Qed.

  Global Instance termT_Pos_sub_mask: computableTime' sub_mask (fun x _ => (7%nat,fun y _ => (size_nat x*32,tt))).
  eapply computableTimeExt with (x:= fun x => sub_maskC false x).
  -repeat intro. hnf. eapply sub_maskC_ext_eq.
  -extract. solverec.
  Qed.

  Global Instance termT_Pos_sub: computableTime' Pos.sub (fun x _ => (1%nat,fun y _ => (size_nat x*32 + 13,tt))).
  Proof.
    extract. solverec.
  Qed.

End pos_sub.


Instance termT_N_sub: computableTime' N.sub (fun x _ => (1,fun y _ => (N.size_nat x*32 + 22 ,tt))).
extract. solverec.
Qed.

Instance termT_N_pred: computableTime' N.pred (fun x _ => (N.size_nat x*12 + 9 ,tt)).
extract. solverec.
Qed.
