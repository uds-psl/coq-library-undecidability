From Undecidability Require TM.TM TM.Util.TM_facts.
From Undecidability Require Import TM.SBTM TM.Util.SBTM_facts.
Require Import Undecidability.Shared.Libs.PSL.FiniteTypes.FinTypes.

From Stdlib Require Import PeanoNat Lia.

#[local] Unset Implicit Arguments.
#[local] Unset Strict Implicit.

From Stdlib Require Import List ssreflect ssrbool ssrfun.
Import Vector.VectorNotations SBTMNotations ListNotations.
Open Scope list.

Set Default Goal Selector "!".

Module SBTM_facts.

  Lemma almost_eq_elim l1 l2 :
    almost_eq l1 l2 -> 
    match l1 with
    | [] => l2 = repeat false (length l2)
    | a :: l1' =>
        match l2 with
        | [] => l1 = repeat false (length l1)
        | b :: l2' => a = b /\ almost_eq l1' l2'
        end
    end.
  Proof.
    elim; first done.
    move=> [|?] [|?].
    - reflexivity.
    - by rewrite repeat_length.
    - by rewrite /= repeat_length.
    - by repeat constructor.
  Qed.

  Lemma almost_eq_false_spec m l :
    almost_eq (repeat false m) l -> l = repeat false (length l).
  Proof.
    elim: m l.
    - move=> [|??]; first done.
      move=> /almost_eq_elim /= [-> ->]. by rewrite repeat_length.
    - move=> m IH [|??]; first done.
      move=> /almost_eq_elim /= [<-] /IH ?.
      by congr cons.
  Qed.

  Lemma almost_eq_trans l1 l2 l3 :
    almost_eq l1 l2 -> almost_eq l2 l3 -> almost_eq l1 l3.
  Proof.
    move=> H. elim: H l3.
    - move=> > H IH [|??] /almost_eq_elim /=.
      + move=> [->] E.
        move: H. rewrite E=> /almost_eq_sym /almost_eq_false_spec ->.
        by apply: (almost_eq_false (S _) 0).
      + move=> [<-] ?. constructor. by apply: IH.
    - move=> > /almost_eq_false_spec ->. by constructor.
  Qed.

  Lemma almost_eq_tape_refl t :
    almost_eq_tape t t.
  Proof.
    move: t => [[ls a] rs].
    constructor; by apply: almost_eq_refl.
  Qed.

  Lemma almost_eq_tape_trans t1 t2 t3 :
    almost_eq_tape t1 t2 -> almost_eq_tape t2 t3 -> almost_eq_tape t1 t3.
  Proof.
    move=> [> ??] H. inversion H. subst.
    constructor; apply: almost_eq_trans; by eassumption.
  Qed.

  Fixpoint truncate (l : list bool) : list bool :=
    if forallb negb l then [] else
    match l with
    | a :: l' => a :: truncate l'
    | [] => []
    end.

  Definition truncate_tape (t : tape) : tape :=
    match t with
    | (ls, a, rs) => (truncate ls, a, truncate rs)
    end.

  Lemma almost_eq_truncate l : almost_eq (truncate l) l. 
  Proof.
    elim: l => [|[|] l IH] /=.
    - by apply: almost_eq_false 0 0.
    - by constructor.
    - case E: (forallb negb l).
      + suff: l = repeat false (length l).
        { move=> ->. by apply: almost_eq_false 0 (S (length l)). }
        apply /Forall_eq_repeat /Forall_forall => a.
        move: E => /forallb_forall /[apply].
        by case: a.
      + by constructor.
  Qed.

  Lemma almost_eq_tape_truncate_tape t : almost_eq_tape (truncate_tape t) t.
  Proof.
    move: t => [[ls a] rs]. constructor; by apply: almost_eq_truncate.
  Qed.

  Lemma truncate_repeat_false n : truncate (repeat false n) = [].
  Proof.
    elim: n; first done.
    move=> n IH /=.
    case E: (forallb negb (repeat false n)); first done.
    exfalso.
    suff: (forallb negb (repeat false n) = true) by congruence.
    by apply /forallb_forall => a /(@repeat_spec bool) ->.
  Qed.

  Lemma almost_eq_truncate_iff l1 l2 : almost_eq l1 l2 <-> truncate l1 = truncate l2.
  Proof.
    split.
    - elim.
      + move=> a {}l1 {}l2 IH E /=.
        suff ->: forallb negb l1 = forallb negb l2 by rewrite E.
        elim: IH {E}.
        * by move=> > /= _ ->.
        * by elim; [elim|].
      + move=> a1 a2. by rewrite !truncate_repeat_false.
    - move=> E.
      have := almost_eq_truncate l2.
      have /almost_eq_sym := almost_eq_truncate l1.
      rewrite E.
      by apply: almost_eq_trans.
  Qed.
      
  Lemma almost_eq_truncate_tape_iff t1 t2:
    truncate_tape t1 = truncate_tape t2 <-> almost_eq_tape t1 t2.
  Proof.
    split.
    - move=> E.
      apply: almost_eq_tape_trans; [|by apply: almost_eq_tape_truncate_tape].
      apply: almost_eq_tape_sym.
      apply: almost_eq_tape_trans; [|by apply: almost_eq_tape_truncate_tape].
      rewrite E.
      by apply: almost_eq_tape_refl.
    - move=> E.
      destruct E. unfold truncate_tape.
      apply almost_eq_truncate_iff in H, H0.
      now rewrite H H0.
  Qed.

  #[local] Opaque step.

  Lemma steps_truncate_tape_None {M k q t} :
    steps M k (q, truncate_tape t) = None <-> (steps M k (q, t) = None).
  Proof.
    apply: almost_eq_tape_steps_None.
    by apply: almost_eq_tape_truncate_tape.
  Qed.

End SBTM_facts.

(* translate between Fin and a listable type *)
Module ListFin.
  Fixpoint decode {X : Type} (L : list X) (i : Fin.t (length L)) : X :=
    (match L return Fin.t (length L) -> X with
    | [] => fun j => Fin.case0 (fun=> X) j
    | x :: L' => fun j => Fin.caseS' j (fun=> X) x (fun j' => decode L' j')
    end) i.

  Definition encode_sig
    {X : Type} (HX : forall (x y : X), {x = y} + {x <> y})
    {L : list X} (HL : forall x, In x L) (x : X) :
      {i : Fin.t (length L) | decode L i = x }.
  Proof.
    elim: L {HL} (HL x); first done.
    move=> y L IH /=. case: (HX y x).
    - move=> -> _. by exists Fin.F1.
    - move=> ??. have /IH [i Hi] : In x L by tauto.
      by exists (Fin.FS i).
  Qed.

  Definition encode
    {X : Type} (HX : forall (x y : X), {x = y} + {x <> y})
    {L : list X} (HL : forall x, In x L) (x : X) :
      Fin.t (length L) := sval (encode_sig HX HL x).

  Lemma decode_encode 
    {X : Type} (HX : forall (x y : X), {x = y} + {x <> y})
    {L : list X} (HL : forall x, In x L)
    (x : X) : decode L (encode HX HL x) = x.
  Proof. exact: (svalP (encode_sig HX HL x)). Qed.
End ListFin.

Import SBTM_facts.

Section Construction.
  (* input TM *)
  Context (M : TM.TM (finType_CS bool) 1).

  (* symbols are "01", "11" *)
  Definition encode_symbol (a : finType_CS bool) : list bool := [a; true].

  (* blank is 00 *)
  Definition encode_tape (t : TM.tape (finType_CS bool)) : tape :=
    match t with
    | TM.niltape => ([], false, [])
    | TM.leftof a rs => ([], false, flat_map encode_symbol (a :: rs))
    | TM.rightof a ls => (false :: flat_map (fun a' => rev (encode_symbol a')) (a :: ls), false, [])
    | TM.midtape ls a rs => (a :: flat_map (fun a' => rev (encode_symbol a')) ls, true, flat_map encode_symbol rs)
    end.

  Inductive space : Type :=
  (* corresponds to q *)
  | space_base (q : TM.state M) : space
  (* reading symbol *)
  | space_read (q : TM.state M) : space
  (* stepping twice in direction d *)
  | space_move (q : TM.state M) (d : direction) (t : bool) : space 
  (* test next symbol in direction d: on false return, on true q *)
  | space_test (q : TM.state M) (d : direction) (t : bool) : space
  (* write b then move in direction *)
  | space_write (q : TM.state M) (a : bool) (d : TM.move) : space.
  
  Lemma listable_space : {L : list space | forall x, In x L}.
  Proof.
    have : {L' | forall (d : direction) (t : bool) (m : TM.move), In (d, t, m) L'}.
    { exists (list_prod (list_prod [go_left; go_right] [true; false]) [TM.Lmove; TM.Rmove; TM.Nmove]).
      move=> [] [] [] /=; tauto. }
    move=> [L' HL'].
    exists (
      flat_map (fun '(q, (d, t, m)) =>
        [space_base q; space_read q; space_move q d t; space_test q d t; space_write q t m]) 
        (list_prod (elem (TM.state M)) L')).
    move=> [].
    - move=> q. apply /in_flat_map.
      exists (q, (go_left, true, TM.Lmove)) => /=. split; last tauto.
      apply /in_prod; by [apply: elem_spec|].
    - move=> q. apply /in_flat_map.
      exists (q, (go_left, true, TM.Lmove)) => /=. split; last tauto.
      apply /in_prod; by [apply: elem_spec|].
    - move=> q d t. apply /in_flat_map.
      exists (q, (d, t, TM.Lmove)) => /=. split; last tauto.
      apply /in_prod; by [apply: elem_spec|].
    - move=> q d t. apply /in_flat_map.
      exists (q, (d, t, TM.Lmove)) => /=. split; last tauto.
      apply /in_prod; by [apply: elem_spec|].
    - move=> q a m. apply /in_flat_map.
      exists (q, (go_left, a, m)) => /=. split; last tauto.
      apply /in_prod; by [apply: elem_spec|].
  Qed.

  Lemma eqdec_space : forall (x y : space), {x = y} + {x <> y}.
  Proof.
    have := @eqType_dec (TM.state M). move=> H.
    intros. do ? decide equality; by apply: H.
  Qed.

  #[local] Notation size := (length (sval listable_space)).

  Definition encode_space : space -> Fin.t size :=
    fun x => ListFin.encode eqdec_space (svalP listable_space) x.

  Definition decode_space : Fin.t size -> space :=
    fun x => ListFin.decode (sval listable_space) x.

  Lemma decode_encode_space (x : space) : decode_space (encode_space x) = x.
  Proof. by apply: ListFin.decode_encode. Qed.

  #[local] Notation encode_state q := (encode_space (space_base q)).
  Open Scope vector.

  Definition go_back (d : direction) :=
    match d with
    | go_left => go_right
    | go_right => go_left
    end.

  Definition M' : SBTM.
  Proof using M.
    refine (Build_SBTM size
      (construct_trans (fun '(q, a) => _))).
    (* in state q reading symbol a *)
    refine (
      match decode_space q with
      | space_base q_base => _
      | space_read q_read => _
      (* move d twice *)
      | space_move q' d true => 
          Some (encode_space (space_move q' d false), a, d)
      (* move d once *)
      | space_move q' d false => 
          Some (encode_state q', a, d)
      (* test d in distance 1 *)
      | space_test q' d true => 
          Some (encode_space (space_test q' d false), a, d)
      (* test *)
      | space_test q' d false => 
          match a with
          | true => Some (encode_space (space_move q' go_right false), a, go_left)
          | false => Some (encode_space (space_move q' (go_back d) false), a, go_back d)
          end
      (* write *)
      | space_write q' b TM.Lmove =>
          Some (encode_state q', b, go_left)
      | space_write q' b TM.Rmove =>
          Some (encode_space (space_move q' go_right true), b, go_right)
      | space_write q' b TM.Nmove =>
          Some (encode_state q', b, go_right)
      end).
    + (* case space_base *)
      refine (
        match TM.halt M q_base with
        (* halting condition *)
        | true => None
        | false =>
            match a with
            (* a = true, read actual symbol *)
            | true => Some (encode_space (space_read q_base), true, go_left)
            (* case a = false, no symbol *)
            | false => 
              match TM.trans M (q_base, [ None ]) with
              | (q_next, result) =>
                  match Vector.hd result with
                  (* case write b, move *)
                  | (Some b, m) => Some (encode_space (space_write q_next b m), true, go_left)
                  (* case no write *)
                  | (None, TM.Lmove) => Some (encode_space (space_test q_next go_left true), a, go_left)
                  | (None, TM.Rmove) => Some (encode_space (space_test q_next go_right true), a, go_right)
                  | (None, TM.Nmove) =>  Some (encode_space (space_move q_next go_right false), a, go_left)
                  end
              end
            end
        end).
    + (* case space_read *)
      refine ( 
        match TM.trans M (q_read, [ Some a ]) with
        | (q_next, result) =>
          match Vector.hd result with
          (* case write bL, Lmove *)
          | (Some bL, TM.Lmove) => Some (encode_state q_next, bL, go_left)
          (* case write bR, Rmove *)
          | (Some bR, TM.Rmove) => Some (encode_space (space_move q_next go_right true), bR, go_right)
          (* case write bN, Nmove *)
          | (Some bN, TM.Nmove) => Some (encode_state q_next, bN, go_right)
          (* case no write *)
          | (None, TM.Lmove) => Some (encode_state q_next, a, go_left)
          | (None, TM.Rmove) => Some (encode_space (space_move q_next go_right true), a, go_right)
          | (None, TM.Nmove) => Some (encode_state q_next, a, go_right)
          end
        end).
  Defined.

  #[local] Notation step := (step M').
  #[local] Notation steps := (steps M').
  #[local] Notation state := (state M').
  #[local] Notation config := (config M').

  #[local] Notation TM_step x := (@TM_facts.step _ _ M x).
  #[local] Notation TM_config := (@TM_facts.mconfig (finType_CS bool) (TM.state M) 1).

  Definition encode_config : TM_config -> config :=
    fun '(TM_facts.mk_mconfig q ctapes) =>
      (encode_state q, truncate_tape (encode_tape (Vector.hd ctapes))).

  (* simulation up to truncation *)
  Lemma simulation_step q t : TM.halt M q = false ->
    exists k,
      (omap (fun '(q', t') => (q', truncate_tape t')) (steps (S k) (encode_state q, encode_tape t))) =
        Some (encode_config (TM_step (TM_facts.mk_mconfig q ([ t ])))).
  Proof.
    move=> Hq. case: t.
    - (* case niltape *)
      rewrite /TM_facts.step.
      move E: (TM.trans _) => [q' a']. move: E.
      rewrite (Vector.eta a') /TM_facts.current_chars /=.
      move: (Vector.hd a') => [ob m] /=.
      case: m ob.
      + (* case Lmove *)
        move=> [b|] /= E.
        * exists 1. by do ? rewrite /= /step /= construct_trans_spec decode_encode_space ?E ?Hq.
        * exists 3. by do ? rewrite /= /step /= construct_trans_spec decode_encode_space ?E ?Hq.
      + (* case Rmove *)
        move=> [b|] /= E.
        * exists 3. by do ? rewrite /= /step /= construct_trans_spec decode_encode_space ?E ?Hq.
        * exists 3. by do ? rewrite /= /step /= construct_trans_spec decode_encode_space ?E ?Hq.
      + (* case Nmove *)
        move=> [b|] /= E.
        * exists 1. by do ? rewrite /= /step /= construct_trans_spec decode_encode_space ?E ?Hq.
        * exists 1. by do ? rewrite /= /step /= construct_trans_spec decode_encode_space ?E ?Hq.
    - (* case leftof *)
      move=> a rs.
      rewrite /TM_facts.step.
      move E: (TM.trans _) => [q' a']. move: E.
      rewrite (Vector.eta a') /TM_facts.current_chars /=.
      move: (Vector.hd a') => [ob m] /=.
      case: m ob.
      + (* case Lmove *)
        move=> [b|] /= E.
        * exists 1. by do ? rewrite /= /step /= construct_trans_spec decode_encode_space ?E ?Hq.
        * exists 3. by do ? rewrite /= /step /= construct_trans_spec decode_encode_space ?E ?Hq.
      + (* case Rmove *)
        move=> [b|] /= E.
        * exists 3. by do ? rewrite /= /step /= construct_trans_spec decode_encode_space ?E ?Hq.
        * exists 3. do ? rewrite /= /step /= construct_trans_spec decode_encode_space ?E ?Hq.
          by case: a.
      + (* case Nmove *)
        move=> [b|] /= E.
        * exists 1. by do ? rewrite /= /step /= construct_trans_spec decode_encode_space ?E ?Hq.
        * exists 1. by do ? rewrite /= /step /= construct_trans_spec decode_encode_space ?E ?Hq.
    - (* case rightof *)
      move=> a ls.
      rewrite /TM_facts.step.
      move E: (TM.trans _) => [q' a']. move: E.
      rewrite (Vector.eta a') /TM_facts.current_chars /=.
      move: (Vector.hd a') => [ob m] /=.
      case: m ob.
      + (* case Lmove *)
        move=> [b|] /= E.
        * exists 1. by do ? rewrite /= /step /= construct_trans_spec decode_encode_space ?E ?Hq.
        * exists 3. by do ? rewrite /= /step /= construct_trans_spec decode_encode_space ?E ?Hq.
      + (* case Rmove *)
        move=> [b|] /= E.
        * exists 3. by do ? rewrite /= /step /= construct_trans_spec decode_encode_space ?E ?Hq.
        * exists 3. by do ? rewrite /= /step /= construct_trans_spec decode_encode_space ?E ?Hq.
      + (* case Nmove *)
        move=> [b|] /= E.
        * exists 1. by do ? rewrite /= /step /= construct_trans_spec decode_encode_space ?E ?Hq.
        * exists 1. by do ? rewrite /= /step /= construct_trans_spec decode_encode_space ?E ?Hq.
    - (* case midtape *)
      move=> ls a rs.
      rewrite /TM_facts.step.
      move E: (TM.trans _) => [q' a']. move: E.
      rewrite (Vector.eta a') /TM_facts.current_chars /=.
      move: (Vector.hd a') => [ob m] /=.
      case: m ob.
      + (* case Lmove *)
        move=> [b|] /= E.
        * exists 1. do ? rewrite /= /step /= construct_trans_spec decode_encode_space ?E ?Hq.
          move: ls => [|l ls]; by do ? rewrite construct_trans_spec decode_encode_space.
        * exists 1. do ? rewrite /= /step /= construct_trans_spec decode_encode_space ?E ?Hq.
          move: ls => [|l ls]; by do ? rewrite /= construct_trans_spec decode_encode_space.
      + (* case Rmove *)
        move=> [b|] /= E.
        * exists 3. do ? rewrite /= /step /= construct_trans_spec decode_encode_space ?E ?Hq.
          move: rs => [|r rs]; by do ? rewrite /= construct_trans_spec decode_encode_space.
        * exists 3. do ? rewrite /= /step /= construct_trans_spec decode_encode_space ?E ?Hq.
          move: rs => [|r rs]; by do ? rewrite /= construct_trans_spec decode_encode_space.
      + (* case Nmove *)
        move=> [b|] /= E.
        * exists 1. by do ? rewrite /= /step /= construct_trans_spec decode_encode_space ?E ?Hq.
        * exists 1. by do ? rewrite /= /step /= construct_trans_spec decode_encode_space ?E ?Hq.
  Qed.


  Lemma simulation_halt q t : TM.halt M q = true ->
    step (encode_state q, t) = None.
  Proof.
    move: t => [[? ?] ?] /= Hq.
    by rewrite /= /step /= construct_trans_spec decode_encode_space ?Hq.
  Qed.

  Lemma almost_eq_tape_step q q' t1 t t' :
    almost_eq_tape t' t ->
    step (q, t) = Some (q', t1) ->
    exists t0, step (q, t') = Some (q', t0) /\ almost_eq_tape t0 t1.
  Proof.
    move E: (step (q, t')) => [[q2 t2]|].
    - move: E => /almost_eq_tape_step_Some /[apply] /[apply].
      move=> [<-] ?. by eexists.
    - by move: E => /almost_eq_tape_step_None /[apply] ->.
  Qed.

  Lemma almost_eq_tape_steps  k q q' t1 t t' :
    almost_eq_tape t' t ->
    steps k (q, t) = Some (q', t1) ->
    exists t0, steps k (q, t') = Some (q', t0) /\ almost_eq_tape t0 t1.
  Proof.
    move=> Ht't.
    elim: k q' t1.
    - move=> ?? /= [<- <-]. by eexists.
    - move=> k IH q' t1.
      have ->: S k = k +1 by lia.
      rewrite steps_plus /=.
      move E: (steps k (q, t)) => [[??]|]; last done.
      move: E => /IH [?] [Hk] /= /almost_eq_tape_step /[apply].
      move=> [t''] [??].
      exists t''. split; last done.
      by rewrite steps_plus Hk.
  Qed.

  Lemma simulation_output q q' t t' t''':
    TM.eval M q t q' t' ->
    almost_eq_tape t''' (encode_tape (Vector.hd t)) ->
    (exists k l,
      steps k ((encode_state q), t''') = Some (encode_state q', l) /\
      steps (S k) ((encode_state q), t''') = None /\
      almost_eq_tape l ((encode_tape (Vector.hd t')))).
  Proof.
    move=> /TM_facts.TM_eval_iff [n].
    elim: n q t q' t' t'''.
    { move=> q t q' t' t'''. rewrite /= /TM_facts.haltConf /=.
      case E: (TM.halt q) => [|]; last done.
      move: E => /simulation_halt => /(_ t''') H [<- <-] ?.
      by exists 0, t'''. }
    move=> n IH q t q' t' t'''. rewrite /= /TM_facts.haltConf /=.
    case E: (TM.halt q) => [|].
    { move: E => /simulation_halt => /(_ t''') H [<- <-] ?.
      by exists 0, t'''. }
    rewrite (Vector.eta t).
    move: E => /simulation_step => /(_ (Vector.hd t)) [k1].
    move: (VectorDef.tl t). apply: Vector.case0.
    move: (TM_step _) => [q'' ts''].
    move E: (steps (S k1) _) => [[qk1 tk1]|]; last done.
    move=> Hk1 /IH /= {}IH.
    move: E => /almost_eq_tape_steps /[apply] - [t''''].
    move: Hk1 => /= [->] /almost_eq_truncate_tape_iff /IH [k2] [t'''''].
    move=> [/[dup] + ->].
    move=> /almost_eq_tape_steps H'k2 /= [Hk2 ?] [Hk1].
    move=> /[dup] /H'k2 [t8] [H''k2 ?] ?.
    exists ((S k1) + k2), t8. rewrite (steps_plus) /= Hk1 /=.
    split; [done|split].
    - rewrite H''k2 /=.
      apply: (almost_eq_tape_step_None M') Hk2.
      by apply: almost_eq_tape_sym.
    - apply: almost_eq_tape_trans; eassumption.
  Qed.

  Lemma simulation q t :
    (exists q' t', TM.eval M q t q' t') ->
    exists k, steps k ((encode_state q), (encode_tape (Vector.hd t))) = None.
  Proof.
    move=> [q'] [t'] /simulation_output => /(_ _ (almost_eq_tape_refl (encode_tape (Vector.hd t)))).
    move=> [k] [l] [?] [??].
    by exists (S k).
  Qed.

  Lemma inverse_simulation q t k :
    steps k ((encode_state q), (encode_tape (Vector.hd t))) = None ->
    exists q' t', TM.eval M q t q' t'.
  Proof.
    elim: k q t; first done.
    move=> k IH q t.
    move Hq: (TM.halt q) => [|].
    { move=> _. exists q, t. by apply: TM.eval_halt. }
    move: (Hq) => /simulation_step => /(_ (Vector.hd t)).
    move=> [k1].
    move Hk1: (steps (S k1) _) => [[q' t']|]; last done.
    move=> [] Hq't'.
    move: Hk1 => /steps_sync H /H{H} /steps_truncate_tape_None.
    move E: (TM_step _) Hq't' => [q'' t''].
    move=> [] -> -> /steps_truncate_tape_None /IH.
    move=> [q'''] [t'''] /TM_facts.TM_eval_iff [n Hn].
    exists q''', t'''. apply /TM_facts.TM_eval_iff. exists (S n).
    rewrite /= /TM_facts.haltConf Hq -Hn -E (Vector.eta t) /=.
    move: (Vector.tl t). by apply: Vector.case0.
  Qed.

End Construction.

Require Import Undecidability.Synthetic.Definitions.
Require Import Undecidability.Synthetic.ReducibilityFacts.
Require Undecidability.TM.Reductions.Arbitrary_to_Binary.

Lemma SBTM_simulation (M : TM.TM (finType_CS bool) 1) :
  {M' : SBTM & 
    { q_start : SBTMNotations.state M' |
        ((forall q t t' t'', TM.eval M (TM.start M) t q t' ->
         SBTM_facts.almost_eq_tape t'' (encode_tape (Vector.hd t)) ->
         exists k q' t''', (SBTM.steps M' k (q_start, t'') = Some (q', t''') /\
         SBTM.steps M' (S k) (q_start, t'') = None /\
         almost_eq_tape t'''  (encode_tape (Vector.hd t'))))) /\
        (forall t, (exists k, SBTM.steps M' k (q_start, (encode_tape (Vector.hd t))) = None) -> (exists q' t', TM.eval M (TM.start M) t q' t'))}}.
Proof.
  exists (M' M).
  exists ((encode_space M (space_base M (TM.start M)))).
  split.
  - intros q t t' t'' H H0.
    destruct (simulation_output M (TM.start M) q t t' t'' H H0) as [k [l H1]].
    eexists _, _ , _.
    apply H1.
  - intros t H.
    destruct H as [k H].
    apply (inverse_simulation M (TM.start M) t k H).
Qed.

Theorem reduction :
  TM.HaltTM 1 ⪯ SBTM_HALT.
Proof.
  apply: (reduces_transitive Arbitrary_to_Binary.reduction).
  exists (fun '(M, t) =>
    existT _ (M' M) (encode_config M (TM_facts.mk_mconfig (TM.start M) t))).
  move=> [M t]. split.
  - move=> /simulation [k Hk]. exists k.
    by move: Hk => /steps_truncate_tape_None.
  - by move=> [k] /steps_truncate_tape_None /inverse_simulation.
Qed.
