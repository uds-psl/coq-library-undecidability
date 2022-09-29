Module DN.
Definition ret_ {A : Prop} : 
  A -> ~~A.
tauto. Defined.

Definition bind_ {A B : Prop} : 
  ~~A -> (A -> ~~B) -> ~~B.
tauto. Defined.

Definition remove_ {A B} : 
  ~~A -> (A -> ~B) -> ~B.         
tauto. Defined.

Definition lem_ X : ~~(X \/ ~X).
tauto. Defined.

Definition dne_ X : ~~(~~X -> X).
tauto. Defined.

Ltac ret := apply ret_.
Ltac bind H := apply (bind_ H); clear H; intros H; try tauto.
Ltac lem P := apply (bind_ (lem_ P)); try tauto.
Ltac dne P := apply (bind_ (dne_ P)); try tauto.
End DN.