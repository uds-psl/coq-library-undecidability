(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List Arith Lia Bool.

From Undecidability.Shared.Libs.DLW 
  Require Import utils list_bool pos vec subcode sss.

From Undecidability.StackMachines.BSM 
  Require Import bsm_defs.

From Undecidability.TM
  Require Import SBTM.

Set Implicit Arguments.

Set Default Proof Using "Type".

Tactic Notation "rew" "length" := autorewrite with length_db.

Local Notation "e #> x" := (vec_pos e x).
Local Notation "e [ v / x ]" := (vec_change e x v).

Local Notation "P // s -[ k ]-> t" := (sss_steps (@bsm_sss _) P k s t).
Local Notation "P // s ->> t" := (sss_compute (@bsm_sss _) P s t).
Local Notation "P // s -+> t" := (sss_progress (@bsm_sss _) P s t) (at level 70, no associativity).

Section Binary_Stack_Machines.

  Variable (n : nat).

  Ltac dest x y := destruct (pos_eq_dec x y) as [ | ]; [ subst x | ]; rew vec.

  Section jump.

   Variable (x : pos n) (i j : nat).

   Definition jump := PUSH x Zero :: POP x j j :: nil.

   Fact jump_length : length jump = 2.
   Proof. reflexivity. Qed.

   Fact jump_spec v w : v = w -> (i,jump) // (i,v) ->> (j,w).
   Proof.
     unfold jump; intros <-.
     bsm sss PUSH with x Zero.
     bsm sss POP zero with x j j (v#>x); rew vec.
     bsm sss stop.
   Qed.

  End jump.

  Hint Rewrite jump_length : length_db.

  Hint Resolve jump_spec : core.

  Section read_head.

    Variable (x : pos n) (i : nat) (j0 j1 : nat).
    
    (* Code for reading the head *)

    Definition read_head := 
      POP x (4+i) (5+i) :: 
      PUSH x One :: 
      jump x j1 ++
      PUSH x Zero ::
      jump x j0.

    Fact read_head_length : length read_head = 7.
    Proof. reflexivity. Qed.

    Fact read_head_empty v :
           v#>x = nil -> (i,read_head) // (i,v) -+> (j0,v).
    Proof.
      unfold read_head; intros H.
      bsm sss POP empty with x (4+i) (5+i).
      apply subcode_sss_compute_trans with (P := (5+i,jump x j0))
                                           (st2 := (j0,v)); auto.
      bsm sss stop.
    Qed.

    Fact read_head_Zero v l :
           v#>x = Zero::l -> (i,read_head) // (i,v) -+> (j0,v).
    Proof.
      unfold read_head; intros H.
      bsm sss POP zero with x (4+i) (5+i) l.
      bsm sss PUSH with x Zero.
      apply subcode_sss_compute_trans with (P := (5+i,jump x j0))
                                           (st2 := (j0,v)); auto.
      2: bsm sss stop.
      apply jump_spec.
      rew vec; rewrite <- H; rew vec.
    Qed.

    Fact read_head_One v l :
           v#>x = One::l -> (i,read_head) // (i,v) -+> (j1,v).
    Proof.
      unfold read_head; intros H.
      bsm sss POP one with x (4+i) (5+i) l.
      bsm sss PUSH with x One.
      apply subcode_sss_compute_trans with (P := (2+i,jump x j1))
                                           (st2 := (j1,v)); auto.
      2: bsm sss stop.
      apply jump_spec.
      rew vec; rewrite <- H; rew vec.
    Qed.

    Fact read_head_spec v (b : bool) l w k :
           v = w 
        -> v#>x = b::l 
        -> k = (if b then j1 else j0)
        -> (i,read_head) // (i,v) -+> (k,w).
    Proof.
      intros <- H ->.
      destruct b.
      + eapply read_head_One; eauto.
      + eapply read_head_Zero; eauto.
    Qed.

  End read_head.

  Hint Rewrite read_head_length : length_db.
  Hint Resolve read_head_spec : core.

  Section to_default.

    Variable (x : pos n) (i j : nat).

    Let j' := j.

    Definition to_default :=
      POP x (4+i) (4+i) ::
      PUSH x One ::
      jump x j ++
      PUSH x Zero ::
      jump x j'.

    Fact to_default_length : length to_default = 7.
    Proof. reflexivity. Qed.

    Definition default_stack (l : list bool) :=
      match l with nil => Zero::nil | _ => l end.

    Fact to_default_spec v w :
           w = v[(default_stack (v#>x))/x]
        -> (i,to_default) // (i,v) ->> (j,w).
    Proof.
      intros ->; unfold to_default.
      case_eq (v#>x); [ intros H | intros [] l H ].
      + bsm sss POP empty with x (4+i) (4+i).
        bsm sss PUSH with x Zero.
        rewrite H.
        apply subcode_sss_compute_trans with (P := (5+i,jump x j'))
                                             (st2 := (j,v[(Zero::nil)/x])); auto.
        bsm sss stop.
      + bsm sss POP one with x (4+i) (4+i) l.
        bsm sss PUSH with x One.
        rew vec; simpl default_stack. 
        apply subcode_sss_compute_trans with (P := (2+i,jump x j))
                                             (st2 := (j,v[(One::l)/x])); auto.
        bsm sss stop.
      + bsm sss POP zero with x (4+i) (4+i) l.
        bsm sss PUSH with x Zero.
        rew vec; simpl default_stack. 
        apply subcode_sss_compute_trans with (P := (5+i,jump x j'))
                                             (st2 := (j,v[(Zero::l)/x])); auto.
        bsm sss stop.
    Qed.

  End to_default.

  Hint Rewrite to_default_length : length_db.

  Section ovwrite_head.

    Variable (x : pos n) (b : bool) (i j : nat).
    
    (* Code for overwriting the head *)

    Definition ovwrite_head := POP x (1+i) (1+i) :: PUSH x b :: jump x j.

    Fact ovwrite_head_length : length ovwrite_head = 4.
    Proof. reflexivity. Qed.

    Fact ovwrite_head_1 c l v :
         v#>x = c::l 
      -> (i,ovwrite_head) // (i,v) ->> (1+i,v[l/x]).
    Proof.
      intros H; unfold ovwrite_head; destruct c.
      + bsm sss POP one with x (1+i) (1+i) l; bsm sss stop.
      + bsm sss POP zero with x (1+i) (1+i) l; bsm sss stop.
    Qed.

    Fact ovwrite_head_spec c l v w :
         v#>x = c::l 
      -> w = v[(b::l)/x]
      -> (i,ovwrite_head) // (i,v) ->> (j,w).
    Proof.
      intros H ->.
      apply sss_compute_trans with (1 := ovwrite_head_1 _ H).
      unfold ovwrite_head.
      bsm sss PUSH with x b.
      apply subcode_sss_compute_trans with (P := (2+i,jump x j))
                                           (st2 := (j,v[(b::l)/x])); auto.
      2: bsm sss stop.
      apply jump_spec; rew vec.
    Qed.

  End ovwrite_head.

  Hint Rewrite ovwrite_head_length : length_db.

  Import SBTMNotations.

  Definition tape_eq_stacks (t : tape) (lft : list bool) (rt : list bool) :=
     match t with (l,x,r) => l = lft /\ x::r = rt end.

  Section move_tape.

    Variable (x y : pos n) (Hxy : x <> y) (i j : nat).

    Notation "t '~r' v" := (tape_eq_stacks t (v#>x) (v#>y)) (at level 70).

    (* Code for reading the head *)

    Let j' := j.

    Local Definition mv_left := 
      POP x (11+i) (11+i) :: 
      PUSH y One :: 
      jump x j ++
      to_default x i i ++ (* dead code to match the size with mv_right *)
      PUSH y Zero ::
      jump x j'
      .

    Local Definition mv_right := 
      POP y (4+i) (4+i) :: 
      PUSH x One :: 
      jump x (5+i) ++
      PUSH x Zero ::
      to_default y (5+i) j ++
      jump x j           (* dead code to match the size with mv_left *)
      .

    Fact mv_left_spec t v w : 
          t ~r v
       -> mv go_left t ~r w
       -> (forall z, z <> x -> z <> y -> v#>z = w#>z)
       -> (i,mv_left) // (i,v) ->> (j,w).
    Proof using Hxy.
      destruct t as ((l,b),r).
      intros (H1 & H2) H3 H4.
      unfold mv_left.
      destruct l as [ | [] l ].
      + bsm sss POP empty with x (11+i) (11+i).
        bsm sss PUSH with y Zero.
        apply subcode_sss_compute_trans with (P := (12+i,jump x j'))
                                           (st2 := (j,w)); auto.
        2: bsm sss stop.
        unfold j'; apply jump_spec.
        simpl in H3.
        destruct H3 as (H3 & H5).
        apply vec_pos_ext; intros z.
        dest z x.
        1: rewrite <- H3; auto.
        dest z y.
        rewrite <- H5, <- H2; auto.
      + bsm sss POP one with x (11+i) (11+i) l.
        bsm sss PUSH with y One.
        apply subcode_sss_compute_trans with (P := (2+i,jump x j))
                                           (st2 := (j,w)); auto.
        2: bsm sss stop.
        apply jump_spec.
        simpl in H3.
        destruct H3 as (H3 & H5).
        apply vec_pos_ext; intros z.
        dest z x.
        dest z y.
        rewrite <- H2, <- H5; auto.
      + bsm sss POP zero with x (11+i) (11+i) l.
        bsm sss PUSH with y Zero.
        apply subcode_sss_compute_trans with (P := (12+i,jump x j'))
                                           (st2 := (j,w)); auto.
        2: bsm sss stop.
        apply jump_spec.
        simpl in H3.
        destruct H3 as (H3 & H5).
        apply vec_pos_ext; intros z.
        dest z x.
        dest z y.
        rewrite <- H2, <- H5; auto.
    Qed.

    Fact mv_right_spec t v w : 
          t ~r v
       -> mv go_right t ~r w
       -> (forall z, z <> x -> z <> y -> v#>z = w#>z)
       -> (i,mv_right) // (i,v) ->> (j,w).
    Proof using Hxy.
      destruct t as ((l,b),r).
      intros (H1 & H2) H3 H4.
      unfold mv_right.
      destruct b.
      + bsm sss POP one with y (4+i) (4+i) r.
        bsm sss PUSH with x One.
        rew vec; rewrite <- H1.
        apply subcode_sss_compute_trans with (P := (2+i,jump x (5+i)))
                                           (st2 := (5+i,v[r/y][(One::l)/x])); auto.
        apply subcode_sss_compute with (P := (5+i,to_default y (5+i) j)); auto.
        apply to_default_spec.
        rew vec.
        symmetry.
        apply vec_pos_ext; intros z.
        dest z y.
        2: dest z x; auto.
        all: destruct r; simpl in *; destruct H3; auto.
      + bsm sss POP zero with y (4+i) (4+i) r.
        bsm sss PUSH with x Zero.
        rew vec; rewrite <- H1.
        apply subcode_sss_compute with (P := (5+i,to_default y (5+i) j)); auto.
        apply to_default_spec.
        rew vec.
        symmetry.
        apply vec_pos_ext; intros z.
        dest z y.
        2: dest z x; auto.
        all: destruct r; simpl in *; destruct H3; auto.
    Qed.

    Definition move_tape d :=
      match d with
        | go_left  => mv_left
        | go_right => mv_right
      end.

    Fact move_tape_length d : length (move_tape d) = 14.
    Proof. destruct d; reflexivity. Qed.

    Fact move_tape_spec d t v w : 
          t ~r v
       -> mv d t ~r w
       -> (forall z, z <> x -> z <> y -> v#>z = w#>z)
       -> (i,move_tape d) // (i,v) ->> (j,w).
    Proof using Hxy.
      destruct d; simpl move_tape.
      + apply mv_left_spec.
      + apply mv_right_spec.
    Qed.

  End move_tape.

  Hint Rewrite move_tape_length : length_db.

  Section sbtm2_op.

    (* if head reads true, write b1, mv d1 and jump j1
       if head reads false, write b0, mv d0 and jump j0 *)

    Variable (x y : pos n) (Hxy : x <> y) (i : nat)
       (o0 o1 : bool) (b0 b1 : bool) (d0 d1 : direction) (j0 j1 k : nat).

    Notation "t '~r' v" := (tape_eq_stacks t (v#>x) (v#>y)) (at level 70).

    Definition sbtm2_op :=
    (*  0+i *) read_head y i (7+i) (27+i) ++
    (*  7+i *) PUSH x o0 :: POP x k 0 ::
    (*  9+i *) ovwrite_head y b0 (9+i) (13+i) ++ 
    (* 13+i *) move_tape x y (13+i) j0 d0 ++
    (* 27+i *) PUSH x o1 :: POP x k 1 ::
    (* 29+i *) ovwrite_head y b1 (29+i) (33+i) ++ 
    (* 33+i *) move_tape x y (33+i) j1 d1.

    Fact sbtm2_op_length : length sbtm2_op = 47.
    Proof. unfold sbtm2_op; rew length; auto. Qed.

    Definition rtape (t : tape) :=
      match t with 
        | (_,a,_) => a
      end.

    Definition utape (t : tape) (a : bool) :=
      match t with 
        | (l,_,r) => (l,a,r)
      end.

    Fact sbtm2_op_spec t v w :
       let o := if rtape t then o1 else o0 in
       let d := if rtape t then d1 else d0 in
       let b := if rtape t then b1 else b0 in
       let j := if rtape t then j1 else j0 
       in               t    ~r v
         -> (o = true -> mv d (utape t b) ~r w) 
         -> (forall z, z <> x -> z <> y -> v#>z = w#>z)
         -> (i,sbtm2_op) // (i,v) -+> if o then (j,w) else (k,v).
    Proof using Hxy.
      intros o d b j H1 H2 H3.
      unfold sbtm2_op.
      destruct t as ((l,[]),r); simpl in * |-; unfold d, b, j, o in *; clear d b j o; destruct H1 as [ H0 H1 ].
      + apply sss_progress_compute_trans with (st2 := (27+i,v)); auto.
        1:{ apply subcode_sss_progress with (P := (i,read_head y i (7 + i) (27 + i))); auto.
            eapply read_head_spec; eauto. }
        bsm sss PUSH with x o1.
        destruct o1.
        * bsm sss POP one with x k 1 (v#>x); rew vec.
          apply subcode_sss_compute_trans with (P := (29+i,ovwrite_head y b1 (29 + i) (33 + i)))
                                               (st2 := (33+i,v[(b1::r)/y])); auto.
          1: eapply ovwrite_head_spec; eauto.
          apply subcode_sss_compute with (P := (33+i,move_tape x y (33 + i) j1 d1)); auto.
          eapply move_tape_spec; eauto.
          - split; rew vec.
          - intros; rew vec.
        * bsm sss POP zero with x k 1 (v#>x); rew vec.
          bsm sss stop.
      + apply sss_progress_compute_trans with (st2 := (7+i,v)); auto.
        1:{ apply subcode_sss_progress with (P := (i,read_head y i (7 + i) (27 + i))); auto.
            eapply read_head_spec; eauto. }
        bsm sss PUSH with x o0.
        destruct o0.
        * bsm sss POP one with x k 0 (v#>x); rew vec.
          apply subcode_sss_compute_trans with (P := (9+i,ovwrite_head y b0 (9 + i) (13 + i)))
                                               (st2 := (13+i,v[(b0::r)/y])); auto.
          1: eapply ovwrite_head_spec; eauto.
          apply subcode_sss_compute with (P := (13+i,move_tape x y (13 + i) j0 d0)); auto.
          eapply move_tape_spec; eauto.
          - split; rew vec.
          - intros; rew vec.
        * bsm sss POP zero with x k 0 (v#>x); rew vec.
          bsm sss stop.
    Qed.

  End sbtm2_op.

End Binary_Stack_Machines.

Section SBTM.

  Variable (M : SBTM).

  Import SBTMNotations.

  Let x : pos 2 := pos0.
  Let y : pos 2 := pos1.

  Let Hxy : x <> y. Proof. easy. Qed.

  Check trans' M.

  Let f (k : option (state M * bool * direction)) :=
    match k with
      | None => (false,false,go_left,0)
      | Some (s,b,d) => (true,b,d,pos2nat s)
    end.

  Check trans.

  Check sbtm2_op_spec Hxy.

  Let g s := 
   let '(o1,b1,d1,j1) := f (trans' M (s,true)) in
   let '(o0,b0,d0,j0) := f (trans' M (s,false))
   in sbtm2_op x y (1+47*pos2nat s) o0 o1 b0 b1 d0 d1 (1+47*j0) (1+47*j1) 0.

  Let length_g s : length (g s) = 47.
  Proof.
    unfold g.
    destruct (f (trans' M (s,true))) as (((?,?),?),?).
    destruct (f (trans' M (s,false))) as (((?,?),?),?).
    apply sbtm2_op_length.
  Qed.

  Let gs_sc l s r : (1+47*length l,g s) <sc (1,flat_map g (l++s::r)).
  Proof.
    exists (flat_map g l), (flat_map g r); split.
    + rewrite flat_map_app; auto.
    + f_equal; clear s r.
      induction l as [ | s l IHl ]; simpl flat_map; auto.
      rewrite app_length, <- IHl, length_g; simpl; lia.
  Qed.

  Definition sbtm2bsm := flat_map g (pos_list _).

  Let P := sbtm2bsm.

  Let pos_list_split n p : exists l r, pos_list n = l++p::r /\ length l = pos2nat p.
  Proof. 
    induction p as [ n | n p (l & r & H1 & H2) ].
    + exists nil, (map pos_nxt (pos_list n)); auto.
    + exists (pos0::map pos_nxt l), (map pos_nxt r); split; simpl.
      * rewrite H1, map_app; simpl; auto.
      * rewrite map_length, H2; auto.
  Qed.

  Let P_sc i : (1+47*pos2nat i, g i) <sc (1,P).
  Proof.
    unfold P, sbtm2bsm.
    destruct (pos_list_split i) as (l & r & -> & <-).
    apply gs_sc.
  Qed.

  Notation "t '~r' v" := (tape_eq_stacks t (v#>x) (v#>y)) (at level 70).

  Fact sbtm2bsm_step_None i t v : 
        step M (i,t) = None 
     -> t ~r v 
     -> (1,P) // (1+47*pos2nat i,v) -+> (0,v).
  Proof.
    intros H1 H2.
    apply subcode_sss_progress with (1 := P_sc i).
    destruct t as ((l,[]),r); unfold step in H1.
    + revert H1; case_eq (trans' M (i,true)). 
      1: now intros ((?,?),?).
      unfold g; intros -> _.
      unfold f at 1.
      destruct (f (trans' M (i, Zero))) as (((o0,b0),d0),j0).
      apply (sbtm2_op_spec Hxy (1+47*pos2nat i) o0 false b0 false d0 go_left (1+47*j0) (1+47*0) 0 (l,One,r) v v); auto.
      simpl; easy.
    + revert H1; case_eq (trans' M (i,false)). 
      1: now intros ((?,?),?).
      unfold g; intros -> _.
      unfold f at 2.
      destruct (f (trans' M (i, One))) as (((o1,b1),d1),j1).
      apply (sbtm2_op_spec Hxy (1+47*pos2nat i) false o1 false b1 go_left d1 (1+47*0) (1+47*j1) 0 (l,Zero,r) _ v); auto.
      simpl; easy.
  Qed.

  Fact sbtm2bsm_step_Some i t j t' v w : 
        step M (i,t) = Some (j,t') 
     -> t ~r v 
     -> t' ~r w
     -> (1,P) // (1+47*pos2nat i,v) -+> (1+47*pos2nat j,w).
  Proof.
    intros H1 H2 H3.
    apply subcode_sss_progress with (1 := P_sc i).
    destruct t as ((l,[]),r); unfold step in H1.
    + revert H1; case_eq (trans' M (i,true)). 
      2: easy.
      unfold g; intros ((j1,b1),d1) -> H1.
      inversion H1; subst j.
      unfold f at 1.
      destruct (f (trans' M (i, Zero))) as (((o0,b0),d0),j0).
      apply (sbtm2_op_spec Hxy (1+47*pos2nat i) o0 true b0 b1 d0 d1 (1+47*j0) (1+47*pos2nat j1) 0 (l,One,r) v w); auto.
      * simpl; subst; auto.
      * intros z; repeat (invert pos z; try easy).
    + revert H1; case_eq (trans' M (i,false)). 
      2: easy.
      unfold g; intros ((j0,b0),d0) -> H1.
      inversion H1; subst j.
      unfold f at 2.
      destruct (f (trans' M (i, One))) as (((o1,b1),d1),j1).
      apply (sbtm2_op_spec Hxy (1+47*pos2nat i) true o1 b0 b1 d0 d1 (1+47*pos2nat j0) (1+47*j1) 0 (l,Zero,r) v w); auto.
      * simpl; subst; auto.
      * intros z; repeat (invert pos z; try easy).
  Qed.

End SBTM.

Check sbtm2bsm_step_None.
Check sbtm2bsm_step_Some.
