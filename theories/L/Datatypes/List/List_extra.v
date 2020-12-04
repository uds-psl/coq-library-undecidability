From Undecidability.L.Tactics Require Import LTactics.
From Undecidability.L Require Import UpToC.
From Undecidability.L.Datatypes Require Export List_enc List_in List_basics LBool LNat.

Set Default Proof Using "Type".

Definition lengthEq A :=
  fix f (t:list A) n :=
    match n,t with
      0,nil => true
    | (S n), _::t => f t n
    | _,_ => false
    end.
Lemma lengthEq_spec A (t:list A) n:
| t | =? n = lengthEq t n.
Proof.
  induction n in t|-*;destruct t;now cbn.
Qed.
Definition lengthEq_time k := k * 15 + 9.
Instance term_lengthEq A `{registered A} : computableTime' (lengthEq (A:=A)) (fun l _ => (5, fun n _ => (lengthEq_time (min (length l) n),tt))).
Proof.
  extract. unfold lengthEq_time. solverec.
Qed.


(* seq *)
Definition c__seq := 20.
Definition seq_time (len : nat) := (len + 1) * c__seq.
Instance term_seq : computableTime' seq (fun start _ => (5, fun len _ => (seq_time len, tt))). 
Proof. 
  extract. solverec. 
  all: unfold seq_time, c__seq; solverec. 
Qed. 

(* prodLists *)
Section fixprodLists. 
  Variable (X Y : Type).
  Context `{Xint : registered X} `{Yint : registered Y}.

  Definition c__prodLists1 := 22 + c__map + c__app. 
  Definition c__prodLists2 := 2 * c__map + 39 + c__app.
  Definition prodLists_time (l1 : list X) (l2 : list Y) := (|l1|) * (|l2| + 1) * c__prodLists2 + c__prodLists1. 
  Global Instance term_prodLists : computableTime' (@list_prod X Y) (fun l1 _ => (5, fun l2 _ => (prodLists_time l1 l2, tt))). 
  Proof. 
    apply computableTimeExt with (x := fix rec (A : list X) (B : list Y) : list (X * Y) := 
      match A with 
      | [] => []
      | x :: A' => map (@pair X Y x) B ++ rec A' B 
      end). 
    1: { unfold list_prod. change (fun x => ?h x) with h. intros l1 l2. induction l1; easy. }
    extract. solverec. 
    all: unfold prodLists_time, c__prodLists1, c__prodLists2; solverec. 
    rewrite map_length, map_time_const. leq_crossout. 
  Qed. 
End fixprodLists. 

