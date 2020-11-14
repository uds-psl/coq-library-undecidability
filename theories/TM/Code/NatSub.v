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

From Undecidability Require Import UpToC Hoare.
  
Theorem Subtract_SpecT:
{ f : UpToC (fun x => x + 1) & forall (x y : nat),
  TripleT ≃≃([],[|Contains _ x;Contains _ y|])
  (f (y)) Subtract
  (fun b => ≃≃([b = (y <=? x)],
    ([|Contains _ (x-y);Void|])))}.
Proof.
  eexists_UpToC f. intros x y.
  unfold Subtract.
  eapply While_SpecTReg with (PRE := fun '(x,y) => (_,_))
  (INV := fun '(x,y) b => ([b = match y with 0 => Some true | _ => match x with 0 => Some false | _ => None end end]
    ,match y with 0 => [|Contains _ x;Void|] | S y' => [|Contains _ (pred x);match x with 0 => Void | _ => Contains _ y' end|] end)) 
    (POST := fun '(x,y) b => (_,_)) (f__loop := fun '(x,y) => _)
    (f__step := fun '(x,y) => match y with 0 => _ : nat | S y' => _ end ) (x := (x,y));
    clear x y; intros (x,y).
  -cbn. hstep.
    +now hsteps_cbn.
    +refine (_ : TripleT _ match y with 0 => _ | S _ => match x with 0 => _ | _ => _ end end _ _).
      destruct y;hintros Hy. nia. hstep.
      *now hsteps_cbn.
      * cbn. destruct x;hintros ?. nia. hsteps_cbn. tspec_ext.
      *cbn. hintros ->. cbn. hsteps_cbn. tspec_ext.
      *cbn. intros b Hb. destruct b,x. 1,4:exfalso;nia. all:reflexivity.
    +cbn. hintros ->. hsteps_cbn. tspec_ext.
    +cbn - ["+" "*"]. intros b Hb.
     destruct y,b. 1,4:exfalso;nia. all:reflexivity.
  - cbn. split.
    + intros b Hb. destruct y.
      { inv Hb. cbn - ["+"]. rewrite Nat.sub_0_r. split. now tspec_ext. shelve. }
      split. 2:shelve.
      destruct x. all:inv Hb. cbn. tspec_ext.
    + destruct y. easy. destruct x. easy.
      eexists (_,_). split. cbn. reflexivity.
      split. shelve. cbn. reflexivity.
  - Unshelve.
    4,5,6:unfold Reset_steps;rewrite ?Encode_nat_hasSize;ring_simplify.
    [f]:exact (fun y => y * 30 + CaseNat_steps + 30).
    2:exact 0.
    1:now subst f;smpl_upToC_solve.
    all:unfold f.
    2:destruct x.
    all:nia.
Qed.

Ltac hstep_Subtract :=
  lazymatch goal with
  | [ |- TripleT ?P ?k Subtract ?Q ] => notypeclasses refine (projT2 Subtract_SpecT _ _);shelve
  end.

Smpl Add hstep_Subtract : hstep_smpl.