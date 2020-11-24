Require Import Omega Lia List. 

Ltac inv H := inversion H; subst; clear H.

Ltac invp R :=
  match goal with
  | [ H: R _ |- _] => inv H
  | [ H: R _ _ |- _] => inv H
  | [ H: R _ _ _ |- _] => inv H
  | [ H: R _ _ _ _ |- _] => inv H
  | [ H: R _ _ _ _ _ |- _] => inv H
  | [ H: R _ _ _ _ _ _ |- _] => inv H
  | [ H: R _ _ _ _ _ _ _ |- _] => inv H
  | [ H: R _ _ _ _ _ _ _ _ |- _] => inv H
  | [ H: R _ _ _ _ _ _ _ _ _ |- _] => inv H
  | [ H: R _ _ _ _ _ _ _ _ _  _|- _] => inv H
  end.


Ltac exdestruct := 
    match goal with
    | [ H: ex ?P     |- _] => destruct H
    | [ H: ex2 ?P ?Q |- _] => destruct H
    | [ H: sig ?P    |- _] => destruct H
    | [ H: sigT ?P   |- _] => destruct H
    end.


(* _Modus Ponens_ - applies to implications,
    will generate a subgoal for the premise of H and then specialize H with the result *)
Ltac mp H :=
let x := fresh "H" in
    match type of H with
    | ?Q -> ?P => assert P as x; [apply H | clear H; assert P as H by exact x; clear x]
    end.


Ltac mapinj :=
  match goal with
  | [H: In _ (map _ _) |-_] =>
    let H1 := fresh "H" in
    eapply in_map_iff in H as H1; destruct H1 as (? & ? & ?); subst
  end.


Ltac dostep := econstructor 2; [ eauto |].

Hint Rewrite
     Nat.sub_0_l Nat.sub_0_r Nat.sub_diag
     Nat.add_sub minus_plus Nat.sub_succ
     Nat.add_0_l Nat.add_0_r : simplify. 
        
Ltac simplify := autorewrite with simplify listdb. 
Tactic Notation "simplify" "in" hyp_list(H) := autorewrite with simplify listdb in H. 
Tactic Notation "simplify" "in" "*" := autorewrite with simplify listdb in *. 

