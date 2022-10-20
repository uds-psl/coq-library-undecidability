(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List Bool.

From Undecidability.Shared.Libs.DLW 
  Require Import utils sss.

Import ListNotations.

Set Implicit Arguments.

Definition option_lift X Y (f : X -> option Y) x :=
  match x with Some x => f x | _ => None end.

Inductive direction : Set := mv_left | mv_right.

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

(** * Halting problem for (micro-programmed) Turing machines with a PC counter *)

(* Three instructions: MV d | WR b | BR i j *)
Inductive pctm_instr : Set :=
  | pctm_mv  : direction -> pctm_instr
  | pctm_wr  : bool -> pctm_instr
  | pctm_br  : nat -> nat -> pctm_instr
  .

Module PCTMNotations.

  Notation MV  := pctm_mv.
  Notation WR  := pctm_wr.
  Notation BR  := pctm_br.

  Notation rd := half_tape_read.
  Notation wr := half_tape_write.

End PCTMNotations.

Import PCTMNotations.

(* ** Small-step semantics for PC based TM *)

(* state is a value for the PC value and a tape *) 
Definition pctm_state := (nat * half_tape)%type.

(**    ρ // (i,t₁) -1> (j,t₂) 
    means instruction ρ at PC i transforms 
    the state (i,t₁) into the state (j,t₂) *)

Inductive pctm_sss : pctm_instr -> pctm_state -> pctm_state -> Prop :=
  | pctm_sss_mv d i t t' :  half_tape_mv d t = Some t' -> MV d // (i,t) -1> (1+i,t')
  | pctm_sss_wr b i t :                                   WR b // (i,t) -1> (1+i,wr t b)
  | pctm_sss_br i j p t :                               BR j p // (i,t) -1> (if rd t then j else p,t)
where "ρ // s -1> t" := (pctm_sss ρ s t).

