(* ** Multiplication *)

From Undecidability.TM Require Import ProgrammingTools.
From Undecidability Require Import Hoare.Hoare.

From Undecidability Require Import CaseNat.
Require Import ArithRing. (* for [ring_simplify] *)

Arguments mult : simpl never.
Arguments plus : simpl never.


(* *** Addition *)


Definition Add_Step : pTM sigNat^+ (option unit) 2 :=
  If (CaseNat @ [|Fin1|])
     (Return (Constr_S @ [|Fin0|]) None)
     (Return Nop (Some tt)).

Definition Add_Step_steps : nat := 9.

Definition Add_Step_size (a b : nat) : Vector.t (nat->nat) 2 :=
  match b with
  | 0 => [|id; id|]
  | S b' => [|S; S|]
  end.

Lemma Add_Step_SpecT_space (a b : nat) (ss : Vector.t nat 2) :
  TripleT
    (≃≃([],  withSpace ( [|Contains _ a; Contains _ b|]) ss))
    Add_Step_steps
    Add_Step
    (fun yout =>
            ≃≃([yout = if b then Some tt else None]
                    ,withSpace [|Contains _ (match b with 0 => a | _ => S a end);Contains _ (pred b)|]
          (appSize (Add_Step_size a b) ss))).
Proof.
  start_TM.
  unfold Add_Step. eapply If_SpecT with (k3 := 0).
  - hsteps_cbn.
  - cbn. hintros ?.  destruct b as [ | b']; cbn in *. easy. hsteps_cbn; cbn. tspec_ext.
  - cbn. hintros ->. hsteps. cbn. tspec_ext.
  - intros. destruct yout. (* reflexivity. unfold CaseNat_steps, Add_Step_steps. lia. *)
    + reflexivity.
    + unfold CaseNat_steps, Add_Step_steps. lia.
Qed.


Definition Add_Loop : pTM sigNat^+ unit 2 := While Add_Step.

Definition Add_Loop_steps b := 9 + 10 * b.

Fixpoint Add_Loop_size (a b : nat) : Vector.t (nat->nat) 2 :=
  match b with
  | O => Add_Step_size a b
  | S b' => Add_Step_size a b >>> Add_Loop_size (S a) b'
  end.

Lemma Add_Loop_SpecT_size (a b : nat) (ss : Vector.t nat 2) :
  TripleT
    (≃≃([],  withSpace ( [|Contains _ a; Contains _ b|]) ss))
    (Add_Loop_steps b)
    (Add_Loop)
    (fun _ => tspec
             ([], withSpace [|Contains _ (a+b); Contains _ 0|]
                (appSize (Add_Loop_size a b) ss))).
Proof.
  (* We have to add the space vector to the abstract state *)
  eapply While_SpecTReg with (PRE := fun '(a,b,ss) => (_,_)) (INV := fun '(a,b,ss) y => (_,_)) 
    (POST := fun '(a,b,ss) y => (_,_)) (f__loop := fun '(a,b,ss) => _) (f__step := fun '(a,b,ss) => _) (x := (a,b,ss));
    clear a b ss; intros ((x,y),ss).
    - apply Add_Step_SpecT_space.
    - cbn. split.
      +intros []. split. 2:unfold Add_Step_steps, Add_Loop_steps;lia.
       destruct y as [ | y']; cbn in *. 2:easy. tspec_ext. f_equal. nia.
      +destruct y as [ | y']; cbn in *. easy. intros _.
      eexists (S x, y', _); cbn. repeat split.
      * tspec_ext.
      * unfold Add_Step_steps, Add_Loop_steps. lia.
      * tspec_ext. f_equal. nia.
Qed.


Definition Add : pTM sigNat^+ unit 4 :=
  LiftTapes (CopyValue _) [|Fin1; Fin2|];; (* copy n to a *)
  LiftTapes (CopyValue _) [|Fin0; Fin3|];; (* copy m to b *)
  LiftTapes Add_Loop [|Fin2; Fin3|];; (* Main loop *)
  LiftTapes (Reset _) [|Fin3|]. (* Reset b *)

Definition Add_steps m n := 98 + 12 * n + 22 * m.

Definition Add_space (a b : nat) : Vector.t (nat->nat) 4 :=
  [|(*0*) id; (*1*) id; (*2*) CopyValue_size b >> Add_Loop_size b a @>Fin0;
    (*3*) CopyValue_size a >> (Add_Loop_size b a @>Fin1) >> Reset_size 0 |].

Lemma Add_SpecT_space (a b : nat) (ss : Vector.t nat 4) :
  TripleT
    (≃≃([],  withSpace ( [|Contains _ a; Contains _ b; Void; Void|]) ss))
    (Add_steps a b)
    Add
    (fun _ => ≃≃([],  withSpace ( [|Contains _ a; Contains _ b; Contains _ (a+b); Void|])
                            (appSize (Add_space a b) ss))).
Proof. (* The tactic [hstep] takes also takes care of moving [withSpace] to the head symbol of each precondition *)
  start_TM.
  unfold Add.
  hstep. hstep.
  apply CopyValue_SpecT_size.
  cbn. intros _. cbn.
  hstep. cbn. hstep. cbn. apply CopyValue_SpecT_size.
  cbn. intros _. hstep. cbn. hstep. cbn. apply Add_Loop_SpecT_size.
  cbn. intros _. hstep. cbn. apply Reset_SpecT_space.
  cbn. intros _. replace (b+a) with (a+b) by lia. auto.
  reflexivity. reflexivity.
  unfold CopyValue_steps, Reset_steps, Add_Loop_steps, Add_steps. rewrite !Encode_nat_hasSize. lia.
Qed.

(* *** Multiplication *)


Definition Mult_Step : pTM sigNat^+ (option unit) 5 :=
  If (LiftTapes CaseNat [|Fin0|])
     (Return (
          LiftTapes Add [|Fin1; Fin2; Fin3; Fin4|];; (* Add(n, c, c') *)
          LiftTapes (MoveValue _) [|Fin3; Fin2|]
        ) (None)) (* continue *)
     (Return Nop (Some tt)). (* break *)

Definition Mult_Step_steps m' n c :=
  match m' with
  | O => 6
  | _ => 168 + 33 * c + 39 * n
  end.

Definition Mult_Step_space m' n c : Vector.t (nat->nat) 5 :=
  match m' with
  | 0 => [|id; id; id; id; id|]
  | S m'' => [| (*0*) S;
               (*1*) Add_space n c @> Fin0; (* = [id] *)
               (*2*) (Add_space n c @> Fin1) >> MoveValue_size_y (n+c) c;
               (*3*) (Add_space n c @> Fin2) >> MoveValue_size_x (n+c);
               (*4*) (Add_space n c @>Fin3)
             |]
  end.

Lemma Mult_Step_SpecT_size m' n c ss :
TripleT
  (≃≃([],  withSpace ( [|Contains _ m'; Contains _ n; Contains _ c; Void; Void|]) ss))
  (Mult_Step_steps m' n c)
  (Mult_Step)
  (fun yout =>
      ≃≃([yout = if m' then Some tt else None],
        withSpace 
        [|Contains _ (pred m'); Contains _ n; Contains _ ( if m' then c else (n + c)); Void; Void|] (appSize (Mult_Step_space m' n c) ss))).
Proof.
  start_TM.
  eapply If_SpecTReg.
  - hsteps.
  - cbn. hintros H. destruct m' as [ | m'']. now contradiction H. cbn.
    hsteps. apply Add_SpecT_space. cbn. hsteps. reflexivity. cbn. tspec_ext.
  - cbn. hintros ->. hsteps. tspec_ext.
  - cbn. destruct m'; intros []. 1,4:easy. 
    all:unfold Mult_Step_steps, MoveValue_steps, CaseNat_steps, Add_steps. 2:rewrite !Encode_nat_hasSize.
    all:lia.
Qed.


Definition Mult_Loop := While Mult_Step.

Fixpoint Mult_Loop_steps m' n c :=
  match m' with
  | O => S (Mult_Step_steps m' n c)
  | S m'' => S (Mult_Step_steps m' n c) + Mult_Loop_steps m'' n (n + c)
  end.


Fixpoint Mult_Loop_size m' n c :=
  match m' with
  | 0 => Mult_Step_space m' n c (* [id;...;id] *)
  | S m'' => Mult_Step_space m' n c >>> Mult_Loop_size m'' n (n+c)
  end.

Lemma Mult_Loop_SpecT_size m' n c ss :
  TripleT
    (≃≃([],  withSpace ( [|Contains _ m'; Contains _ n; Contains _ c; Void; Void|]) ss))
    (Mult_Loop_steps m' n c)
    (Mult_Loop)
    (fun _ => ≃≃([],withSpace
                    [|Contains _ 0; Contains _ n; Contains _ (m' * n + c); Void; Void|]
                    (appSize (Mult_Loop_size m' n c) ss))).
Proof.
  eapply While_SpecTReg with (PRE := fun '(m',n,c,ss) => (_,_)) (INV := fun '(m',n,c,ss) y => (_,_)) (POST := fun '(m',n,c,ss) y => (_,_))
   (f__loop := fun '(m,n,c,ss) => _) (f__step := fun '(m,n,c,ss) => _) (x := (m',n,c,ss));
    clear m' n c ss; intros (((m',n),c),ss).
  - apply Mult_Step_SpecT_size.
  - cbn. split.
    +intros y Hy. destruct m'. 2:easy. split. 2:cbn;lia. tspec_ext.
    +destruct m'. easy. intros _. eexists (_,_,_,_). repeat split.
      *tspec_ext.
      *cbn;nia.
      *tspec_ext. f_equal. cbn. nia.
Qed.

  
Definition Mult : pTM sigNat^+ unit 6 :=
  LiftTapes (CopyValue _) [|Fin0; Fin5|];; (* m' := m *)
  LiftTapes (Constr_O) [|Fin2|];; (* c := 0 *)
  LiftTapes Mult_Loop [|Fin5; Fin1; Fin2; Fin3; Fin4|];; (* Main loop *)
  LiftTapes (Reset _) [|Fin5|]. (* Reset m'=0 *)


Definition Mult_steps (m n : nat) : nat := 12 * m + Mult_Loop_steps m n 0 + 57.

Definition Mult_size (m n : nat) : Vector.t (nat->nat) 6 :=
  [|(*0*) id;
    (*1*) Mult_Loop_size m n 0 @> Fin1;
    (*2*) Constr_O_size >> Mult_Loop_size m n 0 @> Fin2;
    (*3*) Mult_Loop_size m n 0 @> Fin3;
    (*4*) Mult_Loop_size m n 0 @> Fin4;
    (*5*) CopyValue_size m >> Mult_Loop_size m n 0 @> Fin0 >> Reset_size 0
   |].

Lemma Mult_SpecT_space (m n : nat) (ss : Vector.t nat 6) :
  TripleT
    (≃≃([],  withSpace ( [|Contains _ m; Contains _ n; Void; Void; Void; Void|]) ss))
    (Mult_steps m n)
    (Mult)
    (fun _ => ≃≃([],  withSpace ( [|Contains _ m; Contains _ n; Contains _ (m * n); Void; Void; Void|])
                            (appSize (Mult_size m n) ss))).
Proof.
  start_TM.
  unfold Mult.
  hstep. hstep. cbn. 
  apply CopyValue_SpecT_size.
  cbn. intros _. hsteps.
  cbn. intros _. hstep. cbn. hstep. cbn. apply Mult_Loop_SpecT_size.
  cbn. intros. hstep. cbn. apply Reset_SpecT_space.
  cbn. intros t. replace (m * n + 0) with (m * n) by lia. auto.
  reflexivity. reflexivity.
  unfold Mult_steps. ring_simplify. unfold CopyValue_steps, Constr_O_steps, Reset_steps. rewrite !Encode_nat_hasSize. cbn. ring_simplify. reflexivity.
Qed.
