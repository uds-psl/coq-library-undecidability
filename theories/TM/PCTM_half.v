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

#[local] Notation ø := nil.

#[local] Notation "◻" := false.
#[local] Notation "◼" := true.

Notation "x ↑ n" := (list_repeat x n) (at level 1, no associativity, format "x ↑ n").

Inductive direction : Set := mv_left | mv_right.

#[local] Notation L := mv_left.
#[local] Notation R := mv_right.

Definition half_tape := (list bool * bool * list bool)%type.

Implicit Type t : half_tape.

Reserved Notation "l '~r' m" (at level 70, no associativity).

Inductive half_tape_equiv_right : list bool -> list bool -> Prop :=
  | ht_right_eq_nil : ø ~r ø
  | ht_right_eq_lft l : l ~r ø -> ◻::l ~r ø
  | ht_right_eq_rt  l : ø ~r l -> ø ~r ◻::l
  | ht_right_eq_bth b l m : l ~r m -> b::l ~r b::m
where "l ~r m" := (half_tape_equiv_right l m).

#[local] Hint Constructors half_tape_equiv_right : core.

Fact half_tape_equiv_right_app k l m  : l ~r m -> k++l ~r k++m.
Proof. intro; induction k; simpl; eauto. Qed. 

Fact half_tape_equiv_right_refl l : l ~r l.
Proof. induction l; eauto. Qed.

Fact half_tape_equiv_right_sym l m : l ~r m -> m ~r l.
Proof. induction 1; eauto. Qed.

Fact half_tape_equiv_right_trans l m k : l ~r m -> m ~r k -> l ~r k.
Proof. induction 1 in k |- *; auto; inversion 1; eauto. Qed.

#[local] Hint Resolve half_tape_equiv_right_refl
                      half_tape_equiv_right_sym
                      half_tape_equiv_right_trans : core.

Definition half_tape_equiv t1 t2 :=
  match t1, t2 with
  | (l₁,h₁,r₁), (l₂, h₂, r₂) => l₁ = l₂ /\ h₁ = h₂ /\ r₁ ~r r₂
  end.

Infix "~~" := half_tape_equiv (at level 70, no associativity).

Fact half_tape_equiv_refl : forall t, t ~~ t.
Proof. intros ((?,?),?); msplit 2; eauto. Qed.

Fact half_tape_equiv_sym : forall t₁ t₂, t₁ ~~ t₂ -> t₂ ~~ t₁.
Proof. intros ([]&?) ([]&?) (? & ? & ?); msplit 2; eauto. Qed.

Fact half_tape_equiv_trans : forall t₁ t₂ t₃, t₁ ~~ t₂ -> t₂ ~~ t₃ -> t₁ ~~ t₃.
Proof. intros ([]&?) ([]&?) ([]&?) (? & ? & ?) (? & ? & ?); msplit 2; subst; eauto. Qed.

Definition half_tape_opt_equiv (ot1 ot2 : option half_tape) :=
  match ot1, ot2 with
  | Some t1, Some t2 => t1 ~~ t2
  | None, None       => True
  | _   , _          => False
  end.

Infix "~o" := half_tape_opt_equiv (at level 70, no associativity).

#[local] Notation "'⟬' l '⟨' x '⟩' r '⟭'" := (l,x,r) (at level 1, format "⟬  l  ⟨ x ⟩  r  ⟭").

(* ⟬⟨⟩⟭ ◻ ◼ *)

Definition half_tape_left t :=
  match t with
  | ⟬ ø ⟨x⟩ r ⟭   => None
  | ⟬ x::l ⟨h⟩ r⟭ => Some ⟬ l ⟨x⟩ h::r ⟭ 
  end.

Definition half_tape_right t :=
  Some (match t with 
  | ⟬ l ⟨h⟩ ø ⟭    => ⟬ h::l ⟨◻⟩ ø ⟭
  | ⟬ l ⟨h⟩ x::r ⟭ => ⟬ h::l ⟨x⟩ r ⟭
  end).

Arguments half_tape_right t /.

Definition half_tape_move d :=
  match d with
  | L => half_tape_left
  | R => half_tape_right
  end.

Definition half_tape_read t := match t with ⟬ _ ⟨h⟩ _ ⟭ => h end.

Definition half_tape_write t h : half_tape :=
  match t with ⟬ l ⟨_⟩ r ⟭ => ⟬ l ⟨h⟩ r ⟭ end.

(** ~~ is a congruence for all tape operations *)

Fact half_tape_left_equiv t1 t2 : t1 ~~ t2 -> half_tape_left t1 ~o half_tape_left t2.
Proof.
  revert t1 t2; intros ((l,h),r1) ((l2,h2),r2) (<- & <- & H).
  destruct l as [ | x l ]; simpl; auto; msplit 2; auto; now constructor.
Qed.

Fact half_tape_right_equiv t1 t2 : t1 ~~ t2 -> half_tape_right t1 ~o half_tape_right t2.
Proof.
  revert t1 t2; intros ((l,h),r1) ((l2,h2),r2) (<- & <- & H).
  induction H as [ | r1 H IH | r2 H IH | b r1 r2 H IH ]; simpl; auto.
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

#[local] Notation "P // s :1> t" := (sss_step pctm_sss P s t).
#[local] Notation "P // s -[ k ]-> t" := (sss_steps pctm_sss P k s t).
#[local] Notation "P // s -[ k ]-> t" := (sss_steps pctm_sss P k s t).
#[local] Notation "P // s ->> t" := (sss_compute pctm_sss P s t).
#[local] Notation "P // s -+> t" := (sss_progress pctm_sss P s t).
#[local] Notation "P // s ↓" := (sss_terminates pctm_sss P s).

Fact pctm_step_equiv P s₁ s₂ s₁' : 
   P // s₁ :1> s₁' -> s₁ ~s s₂ -> exists s₂', P // s₂ :1> s₂' /\ s₁' ~s s₂'.
Proof.
  intros (i & l & rho & r & t & H1 & H2 & H3) H4.
  destruct pctm_sss_equiv with (1 := H3) (2 := H4) as (s' & H5 & H6).
  exists s'; split; auto.
  case_eq s₂; intros j t2 E.
  rewrite <- E.
  exists i, l, rho, r, t2; msplit 2; auto.
  subst; destruct H4; subst; auto.
Qed.

Fact pctm_steps_equiv P k s₁ s₂ s₁' : 
   P // s₁ -[k]-> s₁' -> s₁ ~s s₂ -> exists s₂', P // s₂ -[k]-> s₂' /\ s₁' ~s s₂'.
Proof.
  intros H; revert H s₂.
  induction 1 as [ s | k s1 s1' s1'' H1 H2 IH2 ]; intros s2 H3.
  + eexists; split; eauto; constructor.
  + destruct pctm_step_equiv with (1 := H1) (2 := H3)
      as (s2' & H4 & H5).
    destruct IH2 with (1 := H5) as (s2'' & H6 & H7).
    exists s2''; split; auto.
    constructor 2 with s2'; auto.
Qed.

Fact pctm_progress_equiv P s₁ s₂ s₁' : 
   P // s₁ -+> s₁' -> s₁ ~s s₂ -> exists s₂', P // s₂ -+> s₂' /\ s₁' ~s s₂'.
Proof.
  intros (k & Hk & H) H'.
  destruct pctm_steps_equiv with (1 := H) (2 := H')
    as (s₂' & ? & ?).
  exists s₂'; split; auto.
  exists k; auto.
Qed.

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

Section pctm_move_left.

  Variable (i j : nat).

  Definition pctm_move_left :=
    [ << ◻, L, j | ◼, L, j >> ].

  Fact pctm_move_left_length : length pctm_move_left = 1.
  Proof. trivial. Qed.

  Fact pctm_move_left_spec l h x r : (i,pctm_move_left) // (i,⟬ x::l ⟨h⟩ r ⟭) -+> (j,⟬ l ⟨x⟩ h::r ⟭).
  Proof.
    unfold pctm_move_left.
    pctm sss with false L j true L j; simpl.
    destruct h; simpl; pctm sss stop.
  Qed.

End pctm_move_left.

Section pctm_move_right.

  Variable (i j : nat).

  Definition pctm_move_right :=
    [ << ◻, R, j | ◼, R, j >> ].

  Fact pctm_move_right_length : length pctm_move_right = 1.
  Proof. trivial. Qed.

  Fact pctm_move_right_spec l h x r : (i,pctm_move_right) // (i,⟬ l ⟨h⟩ x::r ⟭) -+> (j,⟬ h::l ⟨x⟩ r ⟭).
  Proof.
    unfold pctm_move_right.
    pctm sss with false R j true R j; simpl.
    destruct h; simpl; pctm sss stop.
  Qed.

End pctm_move_right.

Section pctm_write_l.

  Variables (i : nat) (b : bool).

  Definition pctm_write_l := 
    [ << b, L, 1+i | b, L, 1+i >> ;
      << ◻, R, 2+i | ◼, R, 2+i >> ].

  Fact pctm_write_l_length : length pctm_write_l = 2.
  Proof. trivial. Qed.

  Variables (l r : list bool) (h : bool).

  Fact pctm_write_l_spec : l <> ø -> (i,pctm_write_l) // (i,⟬ l ⟨h⟩ r ⟭) -+> (2+i,⟬ l ⟨b⟩ r ⟭).
  Proof.
    unfold pctm_write_l.
    destruct l as [ | x l' ]; [ now intros [] | intros _ ].
    pctm sss with b L (1+i) b L (1+i); cbn.
    destruct h; pctm sss with false R (S (S i)) true R (S (S i));
      destruct x; simpl; pctm sss stop.
  Qed.

End pctm_write_l.

Section pctm_write_r.

  Variables (i : nat) (b : bool).

  Definition pctm_write_r := 
    [ << b, R, 1+i | b, R, 1+i >> ;
      << ◻, L, 2+i | ◼, L, 2+i >> ].

  Fact pctm_write_r_length : length pctm_write_r = 2.
  Proof. trivial. Qed.

  Variables (l r : list bool) (h : bool).

  Fact pctm_write_r_spec : r <> ø -> (i,pctm_write_r) // (i,⟬ l ⟨h⟩ r ⟭) -+> (2+i,⟬ l ⟨b⟩ r ⟭).
  Proof.
    unfold pctm_write_r.
    destruct r as [ | x r' ]; [ now intros [] | intros _ ].
    pctm sss with b R (1+i) b R (1+i); cbn.
    destruct h; pctm sss with false L (S (S i)) true L (S (S i));
      destruct x; simpl; pctm sss stop.
  Qed.

End pctm_write_r.

#[local] Hint Rewrite pctm_move_left_length
                      pctm_move_right_length
                      pctm_write_l_length
                      pctm_write_r_length : length_db.

Section pctm_tozero_right.

  Variables (i : nat).

  Definition pctm_tozero_right :=
    [ << ◼, R, 1+i | ◼, R, i >> ].

  Fact pctm_tozero_right_length : length pctm_tozero_right = 1.
  Proof. trivial. Qed.

  Fact pctm_tozero_spec_false l x r : (i,pctm_tozero_right) // (i,⟬ l ⟨◻⟩ x::r ⟭) -+> (1+i,⟬ ◼::l ⟨x⟩ r ⟭).
  Proof.
    unfold pctm_tozero_right.
    pctm sss with true R (1+i) true R i; simpl.
    pctm sss stop.
  Qed.

  Fact pctm_tozero_spec_true n l x r : (i,pctm_tozero_right) // (i,⟬ l ⟨◼⟩ ◼↑n++◻::x::r ⟭) -+> (1+i,⟬ ◼↑(n+2)++l ⟨x⟩ r ⟭).
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

Section pctm_next_zero.

  Variables (i j : nat).

  Local Definition pctm_seak_zero_right :=
    [ << ◻, L, 2+i | ◼, R, 1+i >> ].

  Local Fact pctm_seak_zero_right_length : length pctm_seak_zero_right = 1.
  Proof. trivial. Qed.

  Hint Rewrite pctm_seak_zero_right_length : length_db.

  Local Fact pctm_seak_zero_right_spec_false l x r : (1+i,pctm_seak_zero_right) // (1+i,⟬ x::l ⟨◻⟩ r ⟭) -+> (2+i,⟬ l ⟨x⟩ ◻::r ⟭).
  Proof.
    unfold pctm_seak_zero_right.
    pctm sss with false L (2+i) true R (1+i); simpl.
    pctm sss stop.
  Qed.

  Local Fact pctm_seak_zero_right_spec_true n l r : (1+i,pctm_seak_zero_right) // (1+i,⟬ l ⟨◼⟩ ◼↑n++◻::r ⟭) -+> (2+i,⟬ ◼↑n++l ⟨◼⟩ ◻::r ⟭).
  Proof.
    unfold pctm_seak_zero_right.
    revert l; induction n as [ | n IHn ]; intros l.
    + do 2 (pctm sss with false L (2+i) true R (1+i); simpl).
      pctm sss stop.
    + pctm sss with false L (2+i) true R (1+i); simpl.
      apply sss_progress_compute.
      apply sss_progress_compute_trans with (1 := IHn (true::l)).
      pctm sss stop; do 3 f_equal.
      change (true::l) with (true↑1++l); rewrite <- app_ass, <- list_repeat_plus.
      change (true :: true↑n ++ l) with (true↑(1+n) ++ l).
      do 2 f_equal; lia.
  Qed.

  Definition pctm_next_zero :=
    pctm_move_right (1+i) ++ pctm_seak_zero_right ++ pctm_move_right j.

  Fact pctm_next_zero_length : length pctm_next_zero = 3.
  Proof. trivial. Qed.

  Fact pctm_next_zero_spec n l r : (i,pctm_next_zero) // (i,⟬ l ⟨◻⟩ ◼↑n++◻::r ⟭) -+> (j, ⟬ ◼↑n++◻::l ⟨◻⟩ r ⟭).
  Proof.
    unfold pctm_next_zero.
    destruct n as [ | n ]; simpl list_repeat; simpl app at 3 4.
    + apply sss_progress_trans with (1+i,⟬ ◻::l ⟨◻⟩ r ⟭).
      1: apply subcode_sss_progress with (2 := pctm_move_right_spec _ _ _ _ _ _); auto.
      apply sss_progress_trans with (2+i,⟬ l ⟨◻⟩ ◻::r ⟭).
      1: apply subcode_sss_progress with (2 := pctm_seak_zero_right_spec_false _ _ _); auto.
      apply subcode_sss_progress with (2 := pctm_move_right_spec _ _ _ _ _ _); auto.
    + apply sss_progress_trans with (1+i,⟬ ◻::l ⟨◼⟩ ◼↑n++◻::r ⟭).
      1: apply subcode_sss_progress with (2 := pctm_move_right_spec _ _ _ _ _ _); auto.
      apply sss_progress_trans with (2+i,⟬ ◼↑n++◻::l ⟨◼⟩ ◻::r ⟭).
      1: apply subcode_sss_progress with (2 := pctm_seak_zero_right_spec_true _ _ _); auto.
      apply subcode_sss_progress with (2 := pctm_move_right_spec _ _ _ _ _ _); auto.
  Qed.

End pctm_next_zero.

Section pctm_prev_zero.

  Variables (i j : nat).

  Local Definition pctm_seak_zero_left :=
    [ << ◻, R, 2+i | ◼, L, 1+i >> ].

  Local Fact pctm_seak_zero_left_length : length pctm_seak_zero_left = 1.
  Proof. trivial. Qed.

  Hint Rewrite pctm_seak_zero_left_length : length_db.

  Local Fact pctm_seak_zero_left_spec_false l x r : (1+i,pctm_seak_zero_left) // (1+i,⟬ l ⟨◻⟩ x::r ⟭) -+> (2+i,⟬ ◻::l ⟨x⟩ r ⟭).
  Proof.
    unfold pctm_seak_zero_left.
    pctm sss with false R (2+i) true L (1+i); simpl.
    pctm sss stop.
  Qed.

  Local Fact pctm_seak_zero_left_spec_true n l r : (1+i,pctm_seak_zero_left) // (1+i,⟬ ◼↑n++◻::l ⟨◼⟩ r ⟭) -+> (2+i,⟬ ◻::l ⟨◼⟩ ◼↑n++r ⟭).
  Proof.
    unfold pctm_seak_zero_left.
    revert r; induction n as [ | n IHn ]; intros r.
    + do 2 (pctm sss with false R (2+i) true L (1+i); simpl).
      pctm sss stop.
    + pctm sss with false R (2+i) true L (1+i); simpl.
      apply sss_progress_compute.
      apply sss_progress_compute_trans with (1 := IHn (true::r)).
      pctm sss stop; do 3 f_equal.
      change (true::r) with (true↑1++r); rewrite <- app_ass, <- list_repeat_plus.
      change (true :: true↑n ++ r) with (true↑(1+n) ++ r).
      do 2 f_equal; lia.
  Qed.

  Definition pctm_prev_zero :=
    pctm_move_left (1+i) ++ pctm_seak_zero_left ++ pctm_move_left j.

  Fact pctm_prev_zero_length : length pctm_prev_zero = 3.
  Proof. trivial. Qed.

  Fact pctm_prev_zero_spec n l r : (i,pctm_prev_zero) // (i,⟬ ◼↑n++◻::l ⟨◻⟩ r ⟭) -+> (j, ⟬ l ⟨◻⟩ ◼↑n++◻::r ⟭).
  Proof.
    unfold pctm_prev_zero.
    destruct n as [ | n ]; simpl list_repeat; simpl app at 3 4.
    + apply sss_progress_trans with (1+i,⟬ l ⟨◻⟩ ◻::r ⟭).
      1: apply subcode_sss_progress with (2 := pctm_move_left_spec _ _ _ _ _ _); auto.
      apply sss_progress_trans with (2+i,⟬ ◻::l ⟨◻⟩ r ⟭).
      1: apply subcode_sss_progress with (2 := pctm_seak_zero_left_spec_false _ _ _); auto.
      apply subcode_sss_progress with (2 := pctm_move_left_spec _ _ _ _ _ _); auto.
    + apply sss_progress_trans with (1+i,⟬ ◼↑n++◻::l ⟨◼⟩ ◻::r ⟭).
      1: apply subcode_sss_progress with (2 := pctm_move_left_spec _ _ _ _ _ _); auto.
      apply sss_progress_trans with (2+i,⟬ ◻::l ⟨◼⟩ ◼↑n++◻::r ⟭).
      1: apply subcode_sss_progress with (2 := pctm_seak_zero_left_spec_true _ _ _); auto.
      apply subcode_sss_progress with (2 := pctm_move_left_spec _ _ _ _ _ _); auto.
  Qed.

End pctm_prev_zero.

(** These are the two main tools to move arround to ◻ markers on the tape *)
Check pctm_prev_zero_spec.
Check pctm_next_zero_spec.

#[local] Hint Rewrite pctm_tozero_right_length 
                      pctm_prev_zero_length
                      pctm_next_zero_length : length_db.

Section displace_1a_right.

  Variables (i : nat).

  Local Definition displace_1a_right :=
       pctm_move_right (1+i)
    ++ << ◻, R, 3+i | ◻, R, 2+i >>
    :: pctm_tozero_right (2+i)
    ++ pctm_write_l (3+i) ◻.

  Local Fact displace_1a_right_length : length displace_1a_right = 5.
  Proof. trivial. Qed.

  (* l - [x] - ◼↑a - F - y - r    -->    l - x - ◻ - ◼↑a - [◻] - r *)
  Local Fact displace_1a_right_spec l x a y r : 
     (i,displace_1a_right) // (i,⟬ l ⟨x⟩ ◼↑a++◻::y::r ⟭) -+> (5+i,⟬ ◼↑a++◻::x::l ⟨◻⟩ r ⟭).
  Proof.
    unfold displace_1a_right.
    destruct a as [ | a ]; simpl list_repeat.
    + apply sss_progress_compute_trans with (1+i,(x::l,false,y::r)).
      * apply subcode_sss_progress with (2 := pctm_move_right_spec _ _ _ _ _ _); auto.
      * pctm sss with false R (3+i) false R (2+i). 
        simpl rd; simpl mv; simpl half_tape_right; cbv iota.
        apply sss_progress_compute.
        apply subcode_sss_progress with (3+i,pctm_write_l (3+i) ◻); auto.
        now apply pctm_write_l_spec.
    + apply sss_progress_compute_trans with (1+i,(x::l,true,true↑a++false::y::r)).
      * apply subcode_sss_progress with (2 := pctm_move_right_spec _ _ _ _ _ _); auto.
      * pctm sss with false R (3+i) false R (2+i).
        simpl rd; cbn iota.
        destruct a as [ | a ]; simpl list_repeat; simpl mv; cbn iota.
        - apply sss_compute_trans with (3+i,(true::false::x::l,y,r)).
          ++ apply sss_progress_compute,
                   subcode_sss_progress with (2 := pctm_tozero_spec_false _ _ _ _); auto.
          ++ apply sss_progress_compute.
             apply subcode_sss_progress with (3+i,pctm_write_l (3+i) ◻); auto.
             now apply pctm_write_l_spec.
        - apply sss_compute_trans with (3+i,(true↑(a+2)++false::x::l,y,r)).
          ++ apply sss_progress_compute,
                   subcode_sss_progress with (2 := pctm_tozero_spec_true _ _ _ _ _); auto.
          ++ change (true::true::true↑a) with (true↑(2+a)); rewrite (plus_comm a).
             apply sss_progress_compute.
             apply subcode_sss_progress with (3+i,pctm_write_l (3+i) ◻); auto.
             now apply pctm_write_l_spec.
  Qed.

End displace_1a_right.

Section displace_1a_left.

  Variable (i : nat).

  Local Definition write_ones := 
    [ << ◻, L, (3+i) | ◼, R, (2+i) >> ].

  Local Fact write_ones_length : length write_ones = 1.
  Proof. trivial. Qed.

  Local Fact write_ones_spec l n r : (2+i,write_ones) // (2+i,⟬ l ⟨◼⟩ ◼↑n++◻::r ⟭) -+> (3+i,⟬ ◼↑n++l ⟨◼⟩ ◻::r ⟭).
  Proof.
    unfold write_ones.
    induction n as [ | n IHn ] in l |- *; simpl list_repeat; simpl app.
    + do 2 (pctm sss with false L (3+i) true R (2+i); simpl rd; simpl mv; cbn iota).
      pctm sss stop.
    + pctm sss with false L (3+i) true R (2+i); simpl.
      apply sss_progress_compute.
      replace (true :: true↑n ++ l) with (true↑n ++ true↑1 ++ l).
      * apply IHn.
      * now rewrite <- app_ass, <- list_repeat_plus, plus_comm.
  Qed.

  Hint Rewrite write_ones_length : length_db. 

  Local Definition displace_1a_left : list pctm_instr :=
    pctm_write_r i ◼ ++ write_ones ++ pctm_write_r (3+i) ◻.

  Local Fact displace_1a_left_length : length displace_1a_left = 5.
  Proof. trivial. Qed.

  (* l - [_] - ◼↑a - ◻ - r   -->   l - T↑a - [◻] - ◻ - r *)
  Local Fact displace_1a_left_spec l x a r : 
     (i,displace_1a_left) // (i,⟬ l ⟨x⟩ ◼↑a++◻::r ⟭) -+> (5+i,⟬ ◼↑a++l ⟨◻⟩ ◻::r ⟭).
  Proof.
    unfold displace_1a_left.
    apply sss_progress_trans with (2+i,(l,true,true↑a++false::r)).
    1:{ apply subcode_sss_progress with (i, pctm_write_r i ◼); auto.
        apply pctm_write_r_spec.
        now destruct a. }
    apply sss_progress_trans with (3+i,(true↑a++l,true,false::r)).
    1: apply subcode_sss_progress with (2 := write_ones_spec _ _ _); auto.
    apply subcode_sss_progress with (3+i, pctm_write_r (3+i) ◻); auto.
    now apply pctm_write_r_spec.
  Qed.

End displace_1a_left.

#[local] Hint Rewrite displace_1a_left_length
                      displace_1a_right_length : length_db.

Section pctm_inc_a.

  Variable (i : nat).

  Definition pctm_inc_a :=
   (*    i *)    pctm_next_zero i (3+i)
   (*  3+i *) ++ pctm_write_r (3+i) ◼
   (*  5+i *) ++ displace_1a_right (5+i)
   (* 10+i *) ++ pctm_prev_zero (10+i) (13+i)
   (* 13+i *) ++ pctm_prev_zero (13+i) (16+i)
   .

  Fact pctm_inc_a_length : length pctm_inc_a = 16.
  Proof. reflexivity. Qed.

  Fact pctm_inc_a_spec a b : (i,pctm_inc_a) // (i,⟬ ø ⟨◻⟩ ◼↑a++◻::◼↑b++[◻;◻] ⟭) -+> (16+i,⟬ ø ⟨◻⟩ ◼↑(1+a)++◻::◼↑b++[◻] ⟭).
  Proof.
    unfold pctm_inc_a.
    apply sss_progress_trans with (3+i,⟬ ◼↑a++◻::ø ⟨◻⟩ ◼↑b++◻::◻::ø ⟭).
    1:{ apply subcode_sss_progress with (i,pctm_next_zero i (3+i)); auto.
        apply pctm_next_zero_spec. }
    apply sss_progress_trans with (5+i,⟬ ◼↑a++◻::ø ⟨◼⟩ ◼↑b++◻::◻::ø ⟭).
    1:{ apply subcode_sss_progress with (3+i,pctm_write_r (3+i) ◼); auto.
        apply pctm_write_r_spec.
        now destruct b. }
    apply sss_progress_trans with (10+i,⟬ ◼↑b++◻::◼↑(1+a)++◻::ø ⟨◻⟩ ø ⟭).
    1:{ apply subcode_sss_progress with (5+i,displace_1a_right (5+i)); auto.
        apply displace_1a_right_spec. }
    apply sss_progress_trans with (13+i,⟬ ◼↑(1+a)++◻::ø ⟨◻⟩ ◼↑b++◻::ø ⟭).
    1:{ apply subcode_sss_progress with (10+i,pctm_prev_zero (10+i) (13+i)); auto.
        apply pctm_prev_zero_spec. }
    apply subcode_sss_progress with (13+i,pctm_prev_zero (13+i) (16+i)); auto.
    apply pctm_prev_zero_spec.
  Qed.

End pctm_inc_a.

Section pctm_inc_b.

  Variable (i : nat).

  Definition pctm_inc_b :=
   (*    i *)    pctm_next_zero i (3+i)
   (*  3+i *) ++ pctm_next_zero (3+i) (6+i)
   (*  6+i *) ++ << ◼, R, 7+i | ◼, R, 7+i >>
   (*  7+i *) :: pctm_prev_zero (7+i) (10+i)
   (* 10+i *) ++ pctm_prev_zero (10+i) (13+i)
   .

  Fact pctm_inc_b_length : length pctm_inc_b = 13.
  Proof. reflexivity. Qed.

  Fact pctm_inc_b_spec a b : (i,pctm_inc_b) // (i,⟬ ø ⟨◻⟩ ◼↑a++◻::◼↑b++[◻] ⟭) -+> (13+i,⟬ ø ⟨◻⟩ ◼↑a++◻::◼↑(1+b)++[◻] ⟭).
  Proof.
    unfold pctm_inc_b.
    apply sss_progress_trans with (3+i,⟬ ◼↑a++◻::ø ⟨◻⟩ ◼↑b++◻::ø ⟭).
    1:{ apply subcode_sss_progress with (i,pctm_next_zero i (3+i)); auto.
        apply pctm_next_zero_spec. }
    apply sss_progress_trans with (6+i,⟬ ◼↑b++◻::◼↑a++◻::ø ⟨◻⟩ ø ⟭).
    1:{ apply subcode_sss_progress with (3+i,pctm_next_zero (3+i) (6+i)); auto.
        apply pctm_next_zero_spec. }
    pctm sss with ◼ R (7+i) ◼ R (7+i); simpl rd; cbn iota; simpl mv; cbn iota.
    apply sss_progress_compute.
    apply sss_progress_trans with (10+i,⟬ ◼↑a++◻::ø ⟨◻⟩ ◼↑(1+b)++◻::ø ⟭).
    1:{ apply subcode_sss_progress with (7+i,pctm_prev_zero (7+i) (10+i)); auto.
        apply pctm_prev_zero_spec with (n := S _). }
    apply subcode_sss_progress with (10+i,pctm_prev_zero (10+i) (13+i)); auto.
    apply pctm_prev_zero_spec.
  Qed.

End pctm_inc_b.

Section pctm_dec_a.

  Variable (i j k : nat).

  Definition pctm_dec_a := 
   (*    i *)    pctm_move_right (1+i)
   (*  1+i *) ++ << ◻, L, j |  ◼, L, 2+i >>
   (*  2+i *) :: pctm_move_right (3+i)
   (*  3+i *) ++ displace_1a_left (3+i)
   (*  8+i *) ++ pctm_move_right (9+i)
   (*  9+i *) ++ displace_1a_left (9+i)
   (* 14+i *) ++ pctm_prev_zero (14+i) (17+i)
   (* 17+i *) ++ pctm_prev_zero (17+i) k
   .

  Fact pctm_dec_a_length : length pctm_dec_a = 20.
  Proof. reflexivity. Qed.

  Fact pctm_dec_a_spec_0 b : (i,pctm_dec_a) // (i,⟬ ø ⟨◻⟩ ◼↑0++◻::◼↑b++[◻] ⟭) -+> (j,⟬ ø ⟨◻⟩ ◼↑0++◻::◼↑b++[◻] ⟭).
  Proof.
    unfold pctm_dec_a.
    simpl list_repeat; simpl app at 7 9.
    apply sss_progress_trans with (1+i,⟬ ◻::ø ⟨◻⟩ ◼↑b++◻::ø ⟭).
    1:{ apply subcode_sss_progress with (i,pctm_move_right (1+i)); auto.
        apply pctm_move_right_spec. }
    pctm sss with ◻ L j ◼ L (2+i); simpl rd; simpl mv; cbn iota.
    pctm sss stop.
  Qed.

  Fact pctm_dec_a_spec_S a b : (i,pctm_dec_a) // (i,⟬ ø ⟨◻⟩ ◼↑(1+a)++◻::◼↑b++[◻] ⟭) -+> (k,⟬ ø ⟨◻⟩ ◼↑a++◻::◼↑b++[◻;◻] ⟭).
  Proof.
    unfold pctm_dec_a.
    simpl list_repeat; simpl app at 7 9.
    apply sss_progress_trans with (1+i,⟬ ◻::ø ⟨◼⟩ ◼↑a++◻::◼↑b++◻::ø ⟭).
    1:{ apply subcode_sss_progress with (i,pctm_move_right (1+i)); auto.
        apply pctm_move_right_spec. }
    pctm sss with ◻ L j ◼ L (2+i); simpl rd; simpl mv; cbn iota.
    apply sss_progress_compute.
    apply sss_progress_trans with (3+i,⟬ ◻::ø ⟨◼⟩ ◼↑a++◻::◼↑b++◻::ø ⟭).
    1:{ apply subcode_sss_progress with (2+i,pctm_move_right (3+i)); auto.
        apply pctm_move_right_spec. }
    apply sss_progress_trans with (8+i,⟬ ◼↑a++◻::ø ⟨◻⟩ ◻::◼↑b++◻::ø ⟭).
    1:{ apply subcode_sss_progress with (3+i,displace_1a_left (3+i)); auto.
        apply displace_1a_left_spec. }
    apply sss_progress_trans with (9+i,⟬ ◻::◼↑a++◻::ø ⟨◻⟩ ◼↑b++◻::ø ⟭).
    1:{ apply subcode_sss_progress with (8+i,pctm_move_right (9+i)); auto.
        apply pctm_move_right_spec. }
    apply sss_progress_trans with (14+i,⟬ ◼↑b++◻::◼↑a++◻::ø ⟨◻⟩ ◻::ø ⟭).
    1:{ apply subcode_sss_progress with (9+i,displace_1a_left (9+i)); auto.
        apply displace_1a_left_spec. }
    apply sss_progress_trans with (17+i,⟬ ◼↑a++◻::ø ⟨◻⟩ ◼↑b++[◻;◻] ⟭).
    1:{ apply subcode_sss_progress with (14+i,pctm_prev_zero (14+i) (17+i)); auto.
        apply pctm_prev_zero_spec. }
    apply subcode_sss_progress with (17+i,pctm_prev_zero (17+i) k); auto.
    apply pctm_prev_zero_spec.
  Qed.

End pctm_dec_a.

Section pctm_dec_b.

  Variable (i j k : nat).

  Definition pctm_dec_b :=
   (*    i *)    pctm_next_zero i (3+i)
   (*  3+i *) ++ pctm_move_right (4+i)
   (*  4+i *) ++ << ◻, L, 5+i | ◼, L, 8+i >>
   (*  5+i *) :: pctm_prev_zero (5+i) j
   (*  8+i *) ++ pctm_move_right (9+i)
   (*  9+i *) ++ displace_1a_left (9+i)
   (* 14+i *) ++ pctm_prev_zero (14+i) (17+i)
   (* 17+i *) ++ pctm_prev_zero (17+i) k
   .

  Fact pctm_dec_b_length : length pctm_dec_b = 20.
  Proof. reflexivity. Qed.

  Fact pctm_dec_b_spec_0 a : (i,pctm_dec_b) // (i,⟬ ø ⟨◻⟩ ◼↑a++◻::◼↑0++[◻] ⟭) -+> (j,⟬ ø ⟨◻⟩ ◼↑a++◻::◼↑0++[◻] ⟭).
  Proof.
    unfold pctm_dec_b.
    simpl list_repeat; simpl app at 7 9.
    apply sss_progress_trans with (3+i,⟬ ◼↑a++◻::ø ⟨◻⟩ ◻::ø ⟭).
    1:{ apply subcode_sss_progress with (i,pctm_next_zero i (3+i)); auto.
        apply pctm_next_zero_spec. }
    apply sss_progress_trans with (4+i,⟬ ◻::◼↑a++◻::ø ⟨◻⟩ ø ⟭).
    1:{ apply subcode_sss_progress with (3+i,pctm_move_right (4+i)); auto.
        apply pctm_move_right_spec. }
    pctm sss with ◻ L (5+i) ◼ L (8+i); simpl rd; simpl mv; cbn iota.
    apply sss_progress_compute.
    apply subcode_sss_progress with (5+i,pctm_prev_zero (5+i) j); auto.
    apply pctm_prev_zero_spec.
  Qed.

  Fact pctm_dec_b_spec_S a b : (i,pctm_dec_b) // (i,⟬ ø ⟨◻⟩ ◼↑a++◻::◼↑(1+b)++[◻] ⟭) -+> (k,⟬ ø ⟨◻⟩ ◼↑a++◻::◼↑b++[◻;◻] ⟭).
  Proof.
    unfold pctm_dec_b.
    simpl list_repeat; simpl app at 8 10.
    apply sss_progress_trans with (3+i,⟬ ◼↑a++◻::ø ⟨◻⟩ ◼::◼↑b++◻::ø ⟭).
    1:{ apply subcode_sss_progress with (i,pctm_next_zero i (3+i)); auto.
        apply pctm_next_zero_spec. }
    apply sss_progress_trans with (4+i,⟬ ◻::◼↑a++◻::ø ⟨◼⟩ ◼↑b ++ [◻] ⟭).
    1:{ apply subcode_sss_progress with (3+i,pctm_move_right (4+i)); auto.
        apply pctm_move_right_spec. }
    pctm sss with ◻ L (5+i) ◼ L (8+i); simpl rd; simpl mv; cbn iota.
    apply sss_progress_compute.
    apply sss_progress_trans with (9+i,⟬ ◻::◼↑a++◻::ø ⟨◼⟩ ◼↑b ++ [◻] ⟭).
    1:{ apply subcode_sss_progress with (8+i,pctm_move_right (9+i)); auto.
        apply pctm_move_right_spec. }
    apply sss_progress_trans with (14+i,⟬ ◼↑b ++◻::◼↑a++[◻] ⟨◻⟩ [◻] ⟭).
    1:{ apply subcode_sss_progress with (9+i,displace_1a_left (9+i)); auto.
        apply displace_1a_left_spec. }
    apply sss_progress_trans with (17+i,⟬ ◼↑a++◻::ø ⟨◻⟩ ◼↑b++[◻;◻] ⟭).
    1:{ apply subcode_sss_progress with (14+i,pctm_prev_zero (14+i) (17+i)); auto.
        apply pctm_prev_zero_spec. }
    apply subcode_sss_progress with (17+i,pctm_prev_zero (17+i) k); auto.
    apply pctm_prev_zero_spec.
  Qed.

End pctm_dec_b.

(* These are the tools to simulate MM2 instructions with PCTM_half *)

Check pctm_inc_a_spec.
Check pctm_inc_b_spec.

Check pctm_dec_a_spec_0.
Check pctm_dec_a_spec_S.

Check pctm_dec_b_spec_0.
Check pctm_dec_b_spec_S.

From Undecidability.Shared.Libs.DLW
  Require Import compiler compiler_correction.

From Undecidability.MinskyMachines 
  Require Import MM2 mm2_from_zero.

#[local] Notation "i '/MM/' r '⇢' s" := (mm2_atom i r s) (at level 70, no associativity).
#[local] Notation "P '/MM/' r '→' s" := (sss_step mm2_atom P r s) (at level 70, no associativity).
#[local] Notation "P '/MM/' r '-[' k ']->' s" := (sss_steps mm2_atom P k r s) (at level 70, no associativity).
#[local] Notation "P '/MM/' r '↠' s" := (sss_compute mm2_atom P r s) (at level 70, no associativity).
#[local] Notation "P '/MM/' r '~~>' s" := (sss_output mm2_atom P r s) (at level 70, no associativity).
#[local] Notation "P '/MM/' s ↓" := (sss_terminates mm2_atom P s) (at level 70, no associativity).

Section MM2_PCTM_half.

  Definition il rho :=
    match rho with
      | mm2_inc_a   => 16
      | mm2_inc_b   => 13
      | mm2_dec_a j => 20
      | mm2_dec_b j => 20
    end.

  Definition ic lnk i rho :=
    match rho with
      | mm2_inc_a   => pctm_inc_a (lnk i)
      | mm2_inc_b   => pctm_inc_b (lnk i)
      | mm2_dec_a j => pctm_dec_a (lnk i) (lnk (1+i)) (lnk j)
      | mm2_dec_b j => pctm_dec_b (lnk i) (lnk (1+i)) (lnk j)
    end.

  Fact il_ic_ok lnk i rho : length (ic lnk i rho) = il rho.
  Proof. now destruct rho. Qed.

  Definition simul '(a,b) t := t ~~ ⟬ ø ⟨◻⟩ ◼↑a++◻::◼↑b++[◻] ⟭.

  Fact soundness : instruction_compiler_sound ic mm2_atom pctm_sss simul.
  Proof.
    intros lnk rho i1 c1 i2 c2 t1.
    change i1 with (fst (i1,c1)).
    change i2 with (fst (i2,c2)).
    change c1 with (snd (i1,c1)) at 2 6.
    change c2 with (snd (i2,c2)) at 2 4.
    rewrite <- !surjective_pairing.
    generalize (i1,c1) (i2,c2); clear i1 c1 i2 c2; intros s1 s2.
    induction 1 as [ i a b | i a b | i j a b | i j a b | i j b | i j a ]; 
      simpl fst; simpl snd; intros H1 H2; simpl in H2; simpl ic.
    + generalize (pctm_inc_a_spec (lnk i) a b); intros H3.
      destruct pctm_progress_equiv with (1 := H3) (s₂ := (lnk i, t1))
        as ((j,t2) & H4 & H5 & H6).
      * split; auto.
        apply half_tape_equiv_sym, half_tape_equiv_trans with (1 := H2).
        msplit 2; auto.
        do 2 apply half_tape_equiv_right_app, ht_right_eq_bth; auto.
      * exists t2; split.
        - now simpl in H1, H5; rewrite H1, H5.
        - now apply half_tape_equiv_sym.
    + generalize (pctm_inc_b_spec (lnk i) a b); intros H3.
      destruct pctm_progress_equiv with (1 := H3) (s₂ := (lnk i,t1))
        as ((j,t2) & H4 & H5 & H6).
      * split; auto; now apply half_tape_equiv_sym.
      * exists t2; split.
        - now simpl in H1, H5; rewrite H1, H5.
        - now apply half_tape_equiv_sym.
    + generalize (pctm_dec_a_spec_S (lnk i) (lnk (1+i)) (lnk j) a b); intros H3.
      destruct pctm_progress_equiv with (1 := H3) (s₂ := (lnk i,t1))
        as ((?,t2) & H4 & <- & H6).
      * split; auto; now apply half_tape_equiv_sym.
      * exists t2; split; auto.
        apply half_tape_equiv_sym, half_tape_equiv_trans with (2 := H6).
        msplit 2; auto.
        do 2 apply half_tape_equiv_right_app, ht_right_eq_bth; auto.
    + generalize (pctm_dec_b_spec_S (lnk i) (lnk (1+i)) (lnk j) a b); intros H3.
      destruct pctm_progress_equiv with (1 := H3) (s₂ := (lnk i,t1))
        as ((?,t2) & H4 & <- & H6).
      * split; auto; now apply half_tape_equiv_sym.
      * exists t2; split; auto.
        apply half_tape_equiv_sym, half_tape_equiv_trans with (2 := H6).
        msplit 2; auto.
        do 2 apply half_tape_equiv_right_app, ht_right_eq_bth; auto.
    + generalize (pctm_dec_a_spec_0 (lnk i) (lnk (1+i)) (lnk j) b); intros H3.
      destruct pctm_progress_equiv with (1 := H3) (s₂ := (lnk i,t1))
        as ((?,t2) & H4 & <- & H6).
      * split; auto; now apply half_tape_equiv_sym.
      * exists t2; split; auto.
        apply half_tape_equiv_sym, half_tape_equiv_trans with (2 := H6).
        apply half_tape_equiv_refl.
    + generalize (pctm_dec_b_spec_0 (lnk i) (lnk (1+i)) (lnk j) a); intros H3.
      destruct pctm_progress_equiv with (1 := H3) (s₂ := (lnk i,t1))
        as ((?,t2) & H4 & <- & H6).
      * split; auto; now apply half_tape_equiv_sym.
      * exists t2; split; auto.
        apply half_tape_equiv_sym, half_tape_equiv_trans with (2 := H6).
        apply half_tape_equiv_refl.
  Qed.

  Fact simul_0 : simul (0,0) ⟬ ø ⟨◻⟩ ø ⟭.
  Proof. msplit 2; cbv; auto. Qed.

  Theorem mm2_pctm_compiler : compiler_t mm2_atom pctm_sss simul.
  Proof.
    apply generic_compiler with ic il.
    + apply il_ic_ok.
    + apply mm2_atom_total_ni.
    + apply pctm_sss_fun.
    + apply soundness.
  Qed.

  Theorem mm2_zero_pctm_half_red P : 
    { Q | (1,P) /MM/ (1,(0,0)) ↓ <-> (1,Q) // (1,⟬ ø ⟨◻⟩ ø ⟭) ↓ }.
  Proof.
    exists (gc_code mm2_pctm_compiler (1,P) 1).
    apply compiler_t_term_equiv, simul_0.
  Qed.

End MM2_PCTM_half.

Check mm2_zero_pctm_half_red.

(*

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