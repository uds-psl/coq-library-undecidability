From Undecidability.L Require Import LTactics Datatypes.Lists Datatypes.LNat Datatypes.LBool.
From Undecidability.TM Require TM.

From Undecidability.TM Require Import TM_facts SizeBounds.

From Undecidability.L.Complexity  Require Import UpToCNary.

From Undecidability.L.AbstractMachines Require Import FlatPro.Programs.
     
Unset Printing Coercions.  

From Undecidability.TM.L Require Alphabets.

From Coq Require Import Lia Ring Arith.

From Undecidability Require Import TM.Code.List.Concat_Repeat.

Definition enc_bool_perElem (b:bool) := [lamT;lamT;varT 0;lamT; lamT; varT (if b then 1 else 0); retT; retT;appT].
Definition enc_bool_nil := [lamT; lamT; varT 1; retT; retT].
Definition enc_bool_closing :=  [appT; retT; retT].

Lemma enc_bool_explicit (bs : list bool):
  compile (enc bs) = flat_map enc_bool_perElem bs ++ enc_bool_nil ++ concat (repeat enc_bool_closing (length bs)).
Proof.
  repeat unfold enc;cbn.
  induction bs as [ | b bs]. reflexivity.
  cbn - [concat repeat]. rewrite IHbs. replace (S (| bs |)) with (|bs|+1) by nia.
  destruct b;cbn - [concat repeat]. all:repeat (autorewrite with list; cbn - [concat repeat]). all:repeat f_equal.
  all:rewrite repeat_add_app,concat_app. all:easy.
Qed.

Lemma enc_boollist_helper bs :
 flat_map enc_bool_perElem bs ++ enc_bool_nil
 = [lamT;lamT;varT (match bs with [] => 1 | _ => 0 end)]++ skipn 3 (flat_map enc_bool_perElem bs ++ enc_bool_nil).
 Proof.
   destruct bs;reflexivity.
 Qed.

Lemma enc_bool_perElem_size :( fun b => Code.size (enc_bool_perElem b)) <=c (fun _ => 1).
Proof.
  eexists. intros []. all:cbv - [mult]. now rewrite Nat.mul_1_r. easy.
Qed.

Lemma boollist_size :( fun (bs:list bool) => Code.size bs) <=c (fun bs => length bs + 1).
Proof.
  eexists. intros bs. rewrite size_list. erewrite (MoreBase.sumn_map_le_pointwise (f2:=fun _ => _)).
  2:{ intros [] ?;cbv. all:reflexivity. } setoid_rewrite MoreList.sumn_map_c. instantiate (1:=2). nia.
Qed.

Arguments enc_bool_perElem : simpl never.
Arguments enc_bool_nil : simpl never.
Arguments enc_bool_closing : simpl never.