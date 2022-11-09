From Undecidability.L.Tactics Require Import LTactics.
From Undecidability.L.Datatypes Require Export List_enc List_in List_basics LBool LNat.

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

#[global]
Instance term_lengthEq A `{encodable A} : computable (lengthEq (A:=A)).
Proof.
  extract.
Qed.


(* seq *)
#[global]
Instance term_seq : computable seq. 
Proof.
  extract.
Qed. 

(* prodLists *)
Section fixprodLists. 
  Variable (X Y : Type).
  Context `{Xint : encodable X} `{Yint : encodable Y}.

  Global Instance term_prodLists : computable (@list_prod X Y). 
  Proof. 
    apply computableExt with (x := fix rec (A : list X) (B : list Y) : list (X * Y) := 
      match A with 
      | [] => []
      | x :: A' => map (@pair X Y x) B ++ rec A' B 
      end). 
    1: { unfold list_prod. change (fun x => ?h x) with h. intros l1 l2. induction l1; easy. }
    extract.
  Qed. 
End fixprodLists. 
