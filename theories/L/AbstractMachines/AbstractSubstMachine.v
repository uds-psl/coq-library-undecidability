From Undecidability.L Require Import L Programs Complexity.ResourceMeasures.

Require Import Lia Ring Arith.

(** ** Abstract Substitution Machine *)

Local Notation state := (list Pro*list Pro)%type.

(** *** Reduction Rules *)

Definition tc (c:Pro) C: list Pro :=
  match c with
    [] => C
  |_ => c::C
  end.

Inductive step : state -> state -> Prop :=
  step_pushVal P P' Q T V:
    jumpTarget 0 [] P = Some (Q,P')
    -> step ((lamT::P)::T,V) (tc P' T,Q::V)
| step_beta P Q R T V:
    step ((appT::P)::T,Q::R::V) (substP R 0 (lamT::Q++[retT])::tc P T,V).
Hint Constructors step : core.

Definition init s : state := ([compile s],[]).

Lemma tc_compile s c C: tc (compile s++c) C = (compile s++c)::C.
Proof.
  induction s in c|-*;cbn. all:cbn;try autorewrite with list in *;try congruence.  
Qed.

(** *** Time *)

Lemma correctTime' s t k c0 C V:
  timeBS k s t -> 
  exists p l, reprP p t /\ pow step l ((compile s++c0)::C,V) (tc c0 C,p::V) /\ l = 3*k+1.
Proof.
  intros Ev.
  induction Ev in c0, C,V |- *.
  -exists (compile s),1. split. constructor. split. 2:omega. apply (rcomp_1 step). cbn. constructor.
   autorewrite with list. apply jumpTarget_correct.
  -cbn [compile]. autorewrite with list. cbn [List.app].
   edestruct IHEv1 with (c0:=compile t ++ appT :: c0) (C:=C) (V:=V)
     as (p1&l1&rep1&R1&->);inv rep1.  
   edestruct IHEv2 with (c0:=appT :: c0) (C:=C) (V:=compile s'::V)
     as (p2&l2&rep2&R2&->);inv rep2.
   edestruct IHEv3 with (c0:=@nil Tok) (C:=tc c0 C) (V:=V)
     as (p3&l3&rep3&R3&->);inv rep3. rename s0 into u.
   eexists (compile u),_. split. now eauto. split.
   + apply pow_add. eexists. split. exact R1.
     rewrite tc_compile.
     apply pow_add. eexists. split. exact R2.
     apply pow_add. eexists. split. eapply (rcomp_1 step). constructor.
     autorewrite with list in R3.
     rewrite <- substP_correct in R3. exact R3.
   +omega. 
Qed.

Lemma correctTime s t k:
  timeBS k s t -> 
  exists p, reprP p t /\ pow step (3*k+1) (init s) ([],[p]).
Proof.
  intros Ev.
  destruct (correctTime' [] [] [] Ev) as (p&?&rep&R&->).
  autorewrite with list in R.
  eauto.
Qed.

(** *** Space *)

Lemma helperF P T: sumn (map sizeT P) + sumn (map sizeP T) <= sumn (map sizeP (tc P T)).
Proof.
  destruct P as [|[] []];cbn;try omega.   
Qed.

Lemma helper2 s m: size s <= m -> 1+ sumn (map sizeT (compile s)) <= 2*m.
Proof.
  intros. pose (sizeP_size s). omega. 
Qed.

Lemma helperF' P T:  sumn (map sizeP (tc P T)) <= sumn (map sizeT P) + sumn (map sizeP T) + 1.
Proof.
  destruct P as [|[] []];cbn;try omega. 
Qed.

Definition sizeSt '(T',V') :=  (sumn (map sizeP T') + sumn (map sizeP V')).

Definition redWithMaxSizeS := redWithMaxSize sizeSt step.


Lemma correctSpace' s t k P T V:
  Leftmost.spaceBS k s t -> 
  exists m Q , reprP Q t /\
          redWithMaxSizeS m ((compile s++P)::T,V)
                          (tc P T,Q::V)
          /\ k + sumn (map sizeP (tc P T)) + sumn (map sizeP V) <= m
            <= 2*k + sumn (map sizeP (tc P T)) + sumn (map sizeP V).


Proof.
  intros Ev. 
  induction Ev in P, T,V |- * .
  -eexists _,(compile s). cbn - [sizeP]. autorewrite with list. split. constructor. split.
   {econstructor. 2:apply redWithMaxSizeR. constructor. now eauto using jumpTarget_correct. reflexivity. reflexivity. }
   repeat (cbn - [ Nat.max sizeP];autorewrite with list).
   replace( sizeP (lamT :: compile s ++ retT :: P)) with (sizeP (compile s)+sizeP P + 1). 2:{unfold sizeP;repeat (cbn;autorewrite with list);try omega. }
   specialize (sizeP_size' s). specialize (sizeP_size s).
   specialize (helperF' P T) as ?. specialize (helperF P T) as ?.
   intros. unfold sizeP in *. eapply Nat.max_case_strong. all:omega.
  -cbn [compile]. autorewrite with list. cbn [List.app].

    edestruct IHEv1 as (m1'&p1&rep1&R1&eq11&eq12).
    inv rep1. 
    edestruct IHEv2 as (m2'&p2&rep2&R2&eq21&eq22).
    inv rep2.     
    edestruct IHEv3 with (P:=@nil Tok)as (m3'&p3&rep3&R3&eq31&eq32).
    eexists _,p3. split. tauto. split.
    eapply redWithMaxSize_trans.
    eapply R1. 
    rewrite tc_compile.
    eapply redWithMaxSize_trans.
    eapply R2.
    eapply redWithMaxSize_trans.
    eapply redWithMaxSizeC. cbn;now eauto.
    autorewrite with list in R3. 
    erewrite substP_correct with (t:=lam t'). 
    eapply R3.
    reflexivity.
    cbn. eapply redWithMaxSizeR. reflexivity. reflexivity. reflexivity. reflexivity. 
    1:{
      cbn -[max].
      rewrite !tc_compile in *.
      split.
      { clear eq12 eq22 eq32.
      all:specialize (sizeP_size' s'). 
      all:specialize (sizeP_size' s).
      all:specialize (sizeP_size' t'). 
      all:specialize (sizeP_size' t).
      all:specialize (sizeP_size' u).
      specialize (helperF' P T) as H'.
      unfold sizeP in *.
      all:repeat (cbn - [max] in *;autorewrite with list in * ).
      all:lia.
      }
      { clear eq11 eq21 eq31.
        all:specialize (sizeP_size s'). 
        all:specialize (sizeP_size s).
        all:specialize (sizeP_size t'). 
        all:specialize (sizeP_size t).
        all:specialize (sizeP_size u).
        all:apply Leftmost.spaceBS_ge in Ev1 as [? ?].
        all:apply Leftmost.spaceBS_ge in Ev2 as [? ?]. 
        all:apply Leftmost.spaceBS_ge in Ev3 as [H'' ?].
        apply redWithMaxSize_ge in R3 as [].
        
        specialize (helperF P T).
        intros.
        
        
        all:repeat (match goal with [ H: size _ <= _  |- _] => (apply helper2 in H;cbn in H;autorewrite with list in H) end ).
        unfold sizeSt,sizeP in *.
        repeat (cbn -[Nat.max] in *;try autorewrite with list in * ).
        lia.
      }
    }
Qed.

Lemma correctSpace s t m:
  Leftmost.spaceBS m s t -> 
  exists m' P, reprP P t /\ redWithMaxSizeS m' (init s) ([],[P]) /\ m <= m' <= 2*m.
Proof.
  intros Ev. specialize (correctSpace' [] [] [] Ev) as (m'&P&?&R&leq).
  eexists m',P. split. tauto. 
  autorewrite with list in *.
  split.
  -eapply R.
  -cbn in leq. omega.
Qed.
