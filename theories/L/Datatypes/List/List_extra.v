From Undecidability.L.Tactics Require Import LTactics.
From Undecidability.L.Datatypes Require Export List_enc List_in List_basics LBool LNat.

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
