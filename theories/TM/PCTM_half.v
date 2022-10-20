(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List Bool Arith Lia.

From Undecidability.Shared.Libs.DLW 
  Require Import utils sss subcode.

Import ListNotations.

Set Implicit Arguments.

Notation "x ↑ n" := (list_repeat x n) (at level 1, no associativity, format "x ↑ n").

Inductive direction : Set := mv_left | mv_right.

Definition half_tape := (list bool * bool * list bool)%type.

Implicit Type t : half_tape.

Reserved Notation "l '~r' m" (at level 70, no associativity).

Inductive half_tape_equiv_right : list bool -> list bool -> Prop :=
  | ht_right_eq_lft l : l ~r [] -> false::l ~r []
  | ht_right_eq_rt  l : [] ~r l -> [] ~r false::l
  | ht_right_eq_bth b l m : l ~r m -> b::l ~r b::m
where "l ~r m" := (half_tape_equiv_right l m).

Definition half_tape_equiv t1 t2 :=
  match t1, t2 with
  | (l₁,h₁,r₁), (l₂, h₂, r₂) => l₁ = l₂ /\ h₁ = h₂ /\ r₁ ~r r₂
  end.

Infix "~~" := half_tape_equiv (at level 70, no associativity).

Definition half_tape_opt_equiv (ot1 ot2 : option half_tape) :=
  match ot1, ot2 with
  | Some t1, Some t2 => t1 ~~ t2
  | None, None       => True
  | _   , _          => False
  end.

Infix "~o" := half_tape_opt_equiv (at level 70, no associativity).

Definition half_tape_left t :=
  match t with
  | ([],h,r)   => None
  | (x::l,h,r) => Some (l,x,h::r)
  end.

Definition half_tape_right t :=
  Some (match t with 
  | (l,h,[])   => (h::l,false,[])
  | (l,h,x::r) => (h::l,x,r)
  end).

Arguments half_tape_right t /.

Definition half_tape_move d :=
  match d with
  | mv_left  => half_tape_left
  | mv_right => half_tape_right
  end.

Definition half_tape_read t :=
  match t with
  | (_,h,_) => h
  end.

Definition half_tape_write t h : half_tape := 
  match t with
  | (l,_,r) => (l,h,r)
  end.

(** ~~ is a congruence for all tape operations *)

Fact half_tape_left_equiv t1 t2 : t1 ~~ t2 -> half_tape_left t1 ~o half_tape_left t2.
Proof.
  revert t1 t2; intros ((l,h),r1) ((l2,h2),r2) (<- & <- & H).
  destruct l as [ | x l ]; simpl; auto; msplit 2; auto; now constructor.
Qed.

Fact half_tape_right_equiv t1 t2 : t1 ~~ t2 -> half_tape_right t1 ~o half_tape_right t2.
Proof.
  revert t1 t2; intros ((l,h),r1) ((l2,h2),r2) (<- & <- & H).
  induction H as [ r1 H IH | r2 H IH | b r1 r2 H IH ]; simpl; auto.
Qed.

Fact half_tape_move_equiv d t1 t2 : t1 ~~ t2 -> half_tape_move d t1 ~o half_tape_move d t2.
Proof.
  destruct d; simpl half_tape_move.
  + apply half_tape_left_equiv.
  + apply half_tape_right_equiv.
Qed.

Fact half_tape_read_equiv t1 t2 : t1 ~~ t2 -> half_tape_read t1 = half_tape_read t2.
Proof. revert t1 t2; intros ([]&?) ([]&?) (_ & ? & _); auto. Qed.

Fact half_tape_write_equiv {t1 t2} h : t1 ~~ t2 -> half_tape_write t1 h ~~ half_tape_write t2 h.
Proof. revert t1 t2; intros ([]&?) ([]&?) (? & ? & ?); subst; msplit 2; auto. Qed.

(** * Halting problem for (micro-programmed) Turing machines with a PC counter *)

(* Three instructions: MV d | WR b | BR i j *)
Inductive pctm_instr : Set :=
  | pctm_combi  : bool -> direction -> nat 
               -> bool -> direction -> nat 
               -> pctm_instr.

Module PCTMNotations.
  Notation rd := half_tape_read.
  Notation wr := half_tape_write.
  Notation mv := half_tape_move.
  Notation L := mv_left.
  Notation R := mv_right.
  Notation "'<<' w₀ , d₀ , j₀ '|' w₁ , d₁ , j₁ '>>'" := (pctm_combi w₀ d₀ j₀ w₁ d₁ j₁) (at level 1).
End PCTMNotations.

Import PCTMNotations.

(* ** Small-step semantics for PC based TM *)

(* state is a value for the PC value and a tape *) 
Definition pctm_state := (nat * half_tape)%type.

(**    ρ // (i,t₁) -1> (j,t₂) 
    means instruction ρ at PC i transforms 
    the state (i,t₁) into the state (j,t₂) *)

Inductive pctm_sss : pctm_instr -> pctm_state -> pctm_state -> Prop :=
  | in_pctm_sss₀ w₀ d₀ j₀ w₁ d₁ j₁ i t t' : 
       rd t = false -> mv d₀ (wr t w₀) = Some t' -> pctm_combi w₀ d₀ j₀ w₁ d₁ j₁ // (i,t) -1> (j₀,t')
  | in_pctm_sss₁ w₀ d₀ j₀ w₁ d₁ j₁ i t t' : 
       rd t = true  -> mv d₁ (wr t w₁) = Some t' -> pctm_combi w₀ d₀ j₀ w₁ d₁ j₁ // (i,t) -1> (j₁,t')
where "ρ // s -1> t" := (pctm_sss ρ s t).

Definition pctm_state_equiv (s₁ s₂ : pctm_state) := 
  match s₁, s₂ with
  | (i1,t1), (i2,t2) => i1 = i2 /\ t1 ~~ t2
  end.

Infix "~s" := pctm_state_equiv (at level 70).

Fact pctm_sss_equiv ρ s₁ s₂ s₁' : 
   ρ // s₁ -1> s₁' -> s₁ ~s s₂ -> exists s₂', ρ // s₂ -1> s₂' /\ s₁' ~s s₂'.
Proof.
  destruct s₂ as (i2,t2).
  induction 1 as [ w0 d0 j0 w1 d1 j1 i t1 t1' H1 H2 | w0 d0 j0 w1 d1 j1 i t1 t1' H1 H2 ]; intros (H3 & H4); simpl; subst i2.
  + generalize (half_tape_write_equiv w0 H4); intros H5.
    apply half_tape_move_equiv with (d := d0) in H5.
    rewrite H2 in H5.
    case_eq (mv d0 (wr t2 w0)).
    * intros t2' H'; rewrite H' in H5; simpl in H5. 
      exists (j0,t2'); split; auto.
      constructor 1; auto.
      now apply half_tape_read_equiv in H4 as <-.
    * intros H; now rewrite H in H5.
  + generalize (half_tape_write_equiv w1 H4); intros H5.
    apply half_tape_move_equiv with (d := d1) in H5.
    rewrite H2 in H5.
    case_eq (mv d1 (wr t2 w1)).
    * intros t2' H'; rewrite H' in H5; simpl in H5. 
      exists (j1,t2'); split; auto.
      constructor 2; auto.
      now apply half_tape_read_equiv in H4 as <-.
    * intros H; now rewrite H in H5.
Qed.

#[local] Notation "P // s -[ k ]-> t" := (sss_steps pctm_sss P k s t).
#[local] Notation "P // s ->> t" := (sss_compute pctm_sss P s t).
#[local] Notation "P // s -+> t" := (sss_progress pctm_sss P s t).

Section PC_based_Turing_Machine.

  Implicit Type P : (nat*list pctm_instr)%type.

  Tactic Notation "mydiscr" := 
    match goal with H: ?x = _, G : ?x = _ |- _ => rewrite H in G; discriminate end.

  Tactic Notation "myinj" := 
    match goal with H: ?x = _, G : ?x = _ |- _ => rewrite H in G; inversion G; subst; auto end.      
  
  (* pctm_sss is a functional relation *)
      
  Fact pctm_sss_fun ρ s s1 s2 : ρ // s -1> s1 -> ρ // s -1> s2 -> s1 = s2.
  Proof. intros []; subst; inversion 1; subst; auto; try mydiscr; myinj. Qed.

  Tactic Notation "solve" "progress" :=
    let H := fresh 
    in intros H;
       apply sss_progress_compute_trans;
       apply subcode_sss_progress with (1 := H);
       exists 1; split; auto; apply sss_steps_1;
       apply in_sss_step with (l := nil); [ simpl; lia | ];
       try (constructor; auto).

  Fact pctm_progress P w0 d0 j0 w1 d1 j1 i t st :
         (i,[<< w0,d0,j0 | w1,d1,j1 >>]) <sc P
      -> match rd t with
         | true => 
           match mv d1 (wr t w1) with
           | Some t1 => P // (j1,t1) ->> st
           | None => False
           end
         | false => 
           match mv d0 (wr t w0) with
           | Some t0 => P // (j0,t0) ->> st
           | None => False
           end
         end
      -> P // (i,t) -+> st.
  Proof. 
    intros H.
    destruct t as ((l,[]),r); simpl.
    + case_eq (mv d1 (l,w1,r)); try easy; intros t' E.
      apply sss_progress_compute_trans.
      apply subcode_sss_progress with (1 := H).
      exists 1; split; auto; apply sss_steps_1.
      apply in_sss_step with (l := nil); [ simpl; lia | ].
      constructor; auto.
    + case_eq (mv d0 (l,w0,r)); try easy; intros t' E.
      apply sss_progress_compute_trans.
      apply subcode_sss_progress with (1 := H).
      exists 1; split; auto; apply sss_steps_1.
      apply in_sss_step with (l := nil); [ simpl; lia | ].
      constructor; auto.
  Qed.

  Hint Resolve pctm_progress : core.

  Tactic Notation "solve" "compute" :=
    intros; apply sss_progress_compute; eauto.

  Fact pctm_compute P w0 d0 j0 w1 d1 j1 i t st :
         (i,[<< w0,d0,j0 | w1,d1,j1 >>]) <sc P
      -> match rd t with
         | true => 
           match mv d1 (wr t w1) with
           | Some t1 => P // (j1,t1) ->> st
           | None => False
           end
         | false => 
           match mv d0 (wr t w0) with
           | Some t0 => P // (j0,t0) ->> st
           | None => False
           end
         end
      -> P // (i,t) ->> st.
  Proof. solve compute. Qed. 

End PC_based_Turing_Machine.

Tactic Notation "pctm" "sss" "with" uconstr(a) uconstr(b) uconstr(c) uconstr(d) uconstr(e) uconstr(f) := 
  match goal with
    | |- _ // _ -+> _ => apply pctm_progress with (w0 := a) (d0 := b) (j0 := c) (w1 := d) (d1 := e) (j1 := f)
    | |- _ // _ ->> _ => apply pctm_compute with (w0 := a) (d0 := b) (j0 := c) (w1 := d) (d1 := e) (j1 := f)
  end; auto.

Tactic Notation "pctm" "sss" "stop" := exists 0; apply sss_steps_0; auto.

#[local] Hint Resolve subcode_refl : core.

Section pctm_move_right.

  Variable (i j : nat).

  Definition pctm_move_right :=
    [ << false, R, j | true, R, j >> ].

  Fact pctm_move_right_length : length pctm_move_right = 1.
  Proof. trivial. Qed.

  Fact pctm_move_right_spec l h x r : (i,pctm_move_right) // (i,(l,h,x::r)) -+> (j,(h::l,x,r)).
  Proof.
    unfold pctm_move_right.
    pctm sss with false R j true R j; simpl.
    destruct h; simpl; pctm sss stop.
  Qed.

End pctm_move_right.

Section pctm_write_l.

  Variables (i : nat) (b : bool).

  Definition pctm_write_l := 
    [ << b,     L, 1+i | b,    L, 1+i >> ;
      << false, R, 2+i | true, R, 2+i >> ].

  Fact pctm_write_l_length : length pctm_write_l = 2.
  Proof. trivial. Qed.

  Variables (l r : list bool) (x h : bool).

  Fact pctm_write_l_spec : (i,pctm_write_l) // (i,(x::l,h,r)) -+> (2+i,(x::l,b,r)).
  Proof.
    unfold pctm_write_l.
    pctm sss with b L (1+i) b L (1+i); cbn.
    destruct h; pctm sss with false R (S (S i)) true R (S (S i));
      destruct x; simpl; pctm sss stop.
  Qed.

End pctm_write_l.

Section pctm_write_r.

  Variables (i : nat) (b : bool).

  Definition pctm_write_r := 
    [ << b,     R, 1+i | b,    R, 1+i >> ;
      << false, L, 2+i | true, L, 2+i >> ].

  Fact pctm_write_r_length : length pctm_write_r = 2.
  Proof. trivial. Qed.

  Variables (l r : list bool) (x h : bool).

  Fact pctm_write_r_spec : (i,pctm_write_r) // (i,(l,h,x::r)) -+> (2+i,(l,b,x::r)).
  Proof.
    unfold pctm_write_r.
    pctm sss with b R (1+i) b R (1+i); cbn.
    destruct h; pctm sss with false L (S (S i)) true L (S (S i));
      destruct x; simpl; pctm sss stop.
  Qed.

End pctm_write_r.

Section pctm_tozero_right.

  Variables (i : nat).

  Definition pctm_tozero_right :=
    [ << true, R, 1+i | true, R, i >> ].

  Fact pctm_tozero_right_length : length pctm_tozero_right = 1.
  Proof. trivial. Qed.

  Fact pctm_tozero_spec_false l x r : (i,pctm_tozero_right) // (i,(l,false,x::r)) -+> (1+i,(true::l,x,r)).
  Proof.
    unfold pctm_tozero_right.
    pctm sss with true R (1+i) true R i; simpl.
    pctm sss stop.
  Qed.

  Fact pctm_tozero_spec_true n l x r : (i,pctm_tozero_right) // (i,(l,true,true↑n++false::x::r)) -+> (1+i,(true↑(n+2)++l,x,r)).
  Proof.
    unfold pctm_tozero_right.
    revert l; induction n as [ | n IHn ]; intros l.
    + do 2 (pctm sss with true R (1+i) true R i; simpl).
      pctm sss stop.
    + pctm sss with true R (1+i) true R i; simpl.
      apply sss_progress_compute.
      apply sss_progress_compute_trans with (1 := IHn (true::l)).
      pctm sss stop; do 3 f_equal.
      change (true::l) with (true↑1++l); rewrite <- app_ass, <- list_repeat_plus.
      change (true :: true↑(n+2) ++ l) with (true↑(1+(n+2)) ++ l).
      do 2 f_equal; lia.
  Qed.

End pctm_tozero_right.

#[local] Hint Rewrite pctm_move_right_length
                      pctm_write_l_length
                      pctm_write_r_length
                      pctm_tozero_right_length : length_db.

Section displace_1a_right.

  Variables (i : nat).

  Definition displace_1a_right :=
       pctm_move_right (1+i)
    ++ << false,R,3+i | false,R,2+i >>
    :: pctm_tozero_right (2+i)
    ++ pctm_write_l (3+i) false.

  Fact displace_1a_right_length : length displace_1a_right = 5.
  Proof. trivial. Qed.

  (* l - [x] - T↑a - F - y - r    -->    l - x - F - T↑a - [F] - r *)
  Fact displace_1a_right_spec l x a y r : 
     (i,displace_1a_right) // (i,(l,x,true↑a++false::y::r)) -+> (5+i,(true↑a++false::x::l,false,r)).
  Proof.
    unfold displace_1a_right.
    destruct a as [ | a ]; simpl list_repeat.
    + apply sss_progress_compute_trans with (1+i,(x::l,false,y::r)).
      * apply subcode_sss_progress with (2 := pctm_move_right_spec _ _ _ _ _ _); auto.
      * pctm sss with false R (3+i) false R (2+i). 
        simpl rd; simpl mv; simpl half_tape_right; cbv iota.
        apply sss_progress_compute,
              subcode_sss_progress with (2 := pctm_write_l_spec _ _ _ _ _ _); auto.
    + apply sss_progress_compute_trans with (1+i,(x::l,true,true↑a++false::y::r)).
      * apply subcode_sss_progress with (2 := pctm_move_right_spec _ _ _ _ _ _); auto.
      * pctm sss with false R (3+i) false R (2+i).
        simpl rd; cbn iota.
        destruct a as [ | a ]; simpl list_repeat; simpl mv; cbn iota.
        - apply sss_compute_trans with (3+i,(true::false::x::l,y,r)).
          ++ apply sss_progress_compute,
                   subcode_sss_progress with (2 := pctm_tozero_spec_false _ _ _ _); auto.
          ++ apply sss_progress_compute,
                   subcode_sss_progress with (2 := pctm_write_l_spec _ _ _ _ _ _); auto.
        - apply sss_compute_trans with (3+i,(true↑(a+2)++false::x::l,y,r)).
          ++ apply sss_progress_compute,
                   subcode_sss_progress with (2 := pctm_tozero_spec_true _ _ _ _ _); auto.
          ++ change (true::true::true↑a) with (true↑(2+a)); rewrite (plus_comm a). 
             apply sss_progress_compute,
                   subcode_sss_progress with (2 := pctm_write_l_spec _ _ _ _ _ _); auto.
  Qed.

End displace_1a_right.

Check displace_1a_right_spec.

Section write_ones.

  Variable (i : nat).

  Definition write_ones := 
    [ << false, L, (1+i) | true, R, i >> ].

  Fact write_ones_length : length write_ones = 1.
  Proof. trivial. Qed.

  Fact write_ones_spec l n r : (i,write_ones) // (i,(l,true,true↑n++false::r)) -+> (1+i,(true↑n++l,true,false::r)).
  Proof.
    unfold write_ones.
    induction n as [ | n IHn ] in l |- *; simpl list_repeat; simpl app.
    + do 2 (pctm sss with false L (1+i) true R i; simpl rd; simpl mv; cbn iota).
      pctm sss stop.
    + pctm sss with false L (1+i) true R i; simpl.
      apply sss_progress_compute.
      replace (true :: true↑n ++ l) with (true↑n ++ true↑1 ++ l).
      * apply IHn.
      * now rewrite <- app_ass, <- list_repeat_plus, plus_comm.
  Qed.

End write_ones.

#[local] Hint Rewrite write_ones_length : length_db. 

Section displace_1a_left.

  Variable (i : nat).

  Definition displace_1a_left : list pctm_instr :=
    pctm_write_r i true ++ write_ones (2+i) ++ pctm_write_r (3+i) false.

  Fact displace_1a_left_length : length displace_1a_left = 5.
  Proof. trivial. Qed.

  (* l - [x] - T↑a - F - r   -->   l - T↑a - [F] - F - r *)
  Fact displace_1a_left_spec l x a r : 
     (i,displace_1a_left) // (i,(l,x,true↑a++false::r)) -+> (5+i,(true↑a++l,false,false::r)).
  Proof.
    unfold displace_1a_left.
    apply sss_progress_trans with (2+i,(l,true,true↑a++false::r)).
    1: destruct a; apply subcode_sss_progress with (2 := pctm_write_r_spec _ _ _ _ _ _); auto.
    apply sss_progress_trans with (3+i,(true↑a++l,true,false::r)).
    1: apply subcode_sss_progress with (2 := write_ones_spec _ _ _ _); auto.
    apply subcode_sss_progress with (2 := pctm_write_r_spec _ _ _ _ _ _); auto.
  Qed.

End displace_1a_left.


Definition option_lift X Y (f : X -> option Y) x :=
  match x with Some x => f x | _ => None end.


Fact nth_error_nil X n : @nth_error X [] n = None.
Proof. induction n; simpl; auto. Qed.  

Fact nth_error_eq X (l m : list X) : (forall n, nth_error l n = nth_error m n) -> l = m.
Proof.
  revert m; induction l as [ | x l IHl ]; intros [ | y m ] H; f_equal.
  1,2,3: specialize (H 0); try easy; simpl in H; now inversion H.
  apply IHl; intros n.
  apply (H (S n)).
Qed.

Fact nth_S X n a l (x : X) : nth (S n) (a::l) x = nth n l x.
Proof. reflexivity. Qed.

Fact nth_nil X n (x : X) : nth n [] x = x.
Proof. destruct n; trivial. Qed.

Fact nth_eq_cons X (x y : X) l m d₁ d₂ : (forall n, nth n (x::l) d₁ = nth n (y::m) d₂) -> x = y.
Proof. intros H; apply (H 0). Qed.

Fact nth_bool_eq_2 l m : (forall n, nth n (l++[true]) false = nth n (m++[true]) false) -> l = m.
Proof.
  revert m; induction l as [ | a l IHl ]; intros [ | b m ] H; f_equal.
  + specialize (H (S (length m))).
    simpl app in H; now rewrite !nth_S, nth_nil, nth_middle in H.
  + specialize (H (S (length l))).
    simpl app in H; now rewrite !nth_S, nth_nil, nth_middle in H.
  + apply (H 0).
  + apply IHl; intros n.
    apply (H (S n)).
Qed.

(*

Definition half_tape := (list bool * bool * option (list bool))%type.

Section half_tape.

  Implicit Type (ot : option half_tape)
                (t : half_tape).

  Definition half_tape_left t :=
    match t with
    | ([],h,r)          => None
    | (x::l,false,None) => Some (l,x,None)
    | (x::l,true,None)  => Some (l,x,Some [])
    | (x::l,h,Some r)   => Some (l,x,Some (h::r))
    end.

  Definition half_tape_right t :=
    Some (match t with 
    | (l,h,None)        => (h::l,false,None)
    | (l,h,Some [])     => (h::l,true,None)
    | (l,h,Some (x::r)) => (h::l,x,Some r)
    end).

  Definition half_tape_mv d :=
    match d with
    | mv_left  => half_tape_left
    | mv_right => half_tape_right
    end.

  Arguments half_tape_left _ /.
  Arguments half_tape_right _ /.
  Arguments half_tape_mv _ /.

  Definition half_tape_write t b : half_tape :=
    match t with
      | (l,_,r) => (l,b,r)
    end.

  Definition half_tape_read t := 
    match t with (_,h,_) => h end.

  Definition opt_half_tape_left := option_lift half_tape_left.
  Definition opt_half_tape_right := option_lift half_tape_right.
  Definition opt_half_tape_read :=
    option_lift (fun t => Some (half_tape_read t)).

  Fact opt_half_tape_left_right : forall ot, opt_half_tape_left (opt_half_tape_right ot) = ot.
  Proof. now intros [ (([],[]),[[|[]]|]) | ]. Qed.

  Fact opt_half_tape_right_left ot : 
         match opt_half_tape_left ot with
         | Some t' => opt_half_tape_right (opt_half_tape_left ot) = ot
         | None    => True
         end.
  Proof. now destruct ot as [ (([],[]),[[|[]]|]) | ]. Qed.

  Definition opt_half_tape_mv d := option_lift (half_tape_mv d).

  Fixpoint opt_half_tape_mmv l st :=
    match l with
    | []   => st
    | d::l => opt_half_tape_mmv l (opt_half_tape_mv d st)
    end.

  Fact opt_half_tape_mv_None d : opt_half_tape_mv d None = None.
  Proof. now destruct d. Qed. 

  Fact opt_half_tape_mmv_None l : opt_half_tape_mmv l None = None.
  Proof. induction l; auto. Qed.

  Definition opt_half_tape_equiv ot₁ ot₂ := forall l, 
    opt_half_tape_read (opt_half_tape_mmv l ot₁) = opt_half_tape_read (opt_half_tape_mmv l ot₂).

  Fact opt_half_tape_equiv_lft l x r n : 
         opt_half_tape_read (opt_half_tape_mmv (list_repeat mv_left n) (Some (l,x,r))) 
       = nth_error (x::l) n.
  Proof.
    induction l as [ | u l IHl ] in x, r, n |- *; destruct n as [ | n ]; auto.
    + simpl; rewrite nth_error_nil; induction n; simpl; auto.
    + now simpl; destruct x; destruct r; rewrite IHl.
  Qed.

  Fact opt_half_tape_equiv_rt_None l x n : 
         opt_half_tape_read (opt_half_tape_mmv (list_repeat mv_right n) (Some (l,x,None))) 
       = Some (nth n [x] false).
  Proof.
    do 3 try destruct n as [|n]; simpl; trivial.
    generalize (false::false::x::l); clear x l.
    induction n; intros l; simpl; unfold half_tape_right; simpl; auto.
  Qed.

  Fact opt_half_tape_equiv_rt_Some l x r n : 
         opt_half_tape_read (opt_half_tape_mmv (list_repeat mv_right n) (Some (l,x,Some r))) 
       = Some (nth n (x::r++[true]) false).
  Proof.
    induction r as [ | u r IHr ] in x, l, n |- *.
    + simpl; do 3 try destruct n as [|n]; simpl; auto.
      generalize (false::true::x::l); clear x l.
      induction n; intros l; simpl; auto.
    + destruct n as [ | n ]; auto; rewrite nth_S; simpl app.
      simpl opt_half_tape_mmv; auto.
  Qed.

  (** Half tapes which are observationally equivalent are equal *)
  Theorem opt_half_tape_equiv_equal : forall t₁ t₂, opt_half_tape_equiv t₁ t₂ <-> t₁ = t₂.
  Proof.
    intros t1 t2; split; [ | now intros -> ]; revert t1 t2. 
    intros [ ((l1,x1),r1) | ] [ ((l2,x2),r2) | ]; auto; simpl; intros H.
    2, 3: now specialize (H []).
    assert (x1::l1 = x2::l2) as E.
    1:{ apply nth_error_eq; intros n.
        specialize (H (list_repeat mv_left n)).
        now rewrite !opt_half_tape_equiv_lft in H. }
    inversion E; subst x2 l2; repeat f_equal; clear E.
    revert r1 r2 H; intros [ r1 | ] [ r2 | ]; simpl; intros H; auto.
    2: specialize (H (list_repeat mv_right (S (length r1)))).
    3: specialize (H (list_repeat mv_right (S (length r2)))).
    2,3: now rewrite opt_half_tape_equiv_rt_Some, 
                     opt_half_tape_equiv_rt_None, !nth_S, nth_nil, nth_middle in H.
    f_equal.
    assert (x1::r1 = x1::r2) as E; [ | now inversion E ].
    apply nth_bool_eq_2; intros n.
    specialize (H (list_repeat mv_right n)).
    rewrite !opt_half_tape_equiv_rt_Some in H.
    now inversion H.
  Qed.

End half_tape.

*)