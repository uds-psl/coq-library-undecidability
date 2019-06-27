From Undecidability.L Require Import Tactics.LTactics.
Require Import Numbers.BinNums.

From Undecidability.L.Datatypes Require Import LNat LBool LBinNums.

(** *** Addition of binary numbers *)
Section pos_add.
  Import Pos.

  Fixpoint addC (c:bool) (x : positive) {struct x}: positive -> positive:=
    (if c then  
       match x with
       | p~1 => fun y => match y with
                     | q~1 => (addC true p q)~1
                     | q~0 => (addC true p q)~0
                     | 1 => (succ p)~1
                     end
       | p~0 => fun y => match y with
                     | q~1 => (addC true p q)~0
                     | q~0 => (addC false p q)~1
                     | 1 => (succ p)~0
                     end
       | 1 => fun y => match y with
                   | q~1 => (succ q)~1
                   | q~0 => (succ q)~0
                   | 1 => 3
                   end
       end
     else
       match x with
       | p~1 => fun y => match y with
                     | q~1 => (addC true p q)~0
                     | q~0 => (addC false p q)~1
                     | 1 => (succ p)~0
                     end
       | p~0 => fun y => match y with
                     | q~1 => (addC false p q)~1
                     | q~0 => (addC false p q)~0
                     | 1 => p~1
                     end
       | 1 => fun y => match y with
                   | q~1 => (succ q)~0
                   | q~0 => q~1
                   | 1 => 2
                   end
       end)%positive.

  Lemma addC_ext_eq : extEq addC (fun b => if b then add_carry else add).
  Proof.
    intros b x y. induction x in b,y|-*;destruct b,y;cbn;try rewrite !IHx. all:reflexivity.
  Qed.

  Global Instance termT_Pos_addC: computableTime' addC (fun b _ => (5%nat,fun x _ => (11%nat,fun y _ => (12*(size_nat x + size_nat y),tt)))).
  extract. solverec.
  Qed.

  Global Instance termT_Pos_add: computableTime' Pos.add (fun x _ => (17%nat,fun y _ => (12*(size_nat x + size_nat y),tt))).
  Proof.
    eapply computableTimeExt with (x:= (fun x => addC false x)).
    -hnf;repeat intro;eapply addC_ext_eq.
    -extract. solverec.
  Qed.

End pos_add.

Instance termT_N_add: computableTime' N.add (fun x _ => (1,fun y _ => (12*(N.size_nat x + N.size_nat y) + 27 ,tt))).
extract. solverec.
Qed.
