Require Import Undecidability.FOL.Util.Syntax.
Require Import Undecidability.FOL.Util.FullTarski.
Require Import Undecidability.FOL.Util.FullDeduction.
Require Import Undecidability.FOL.Reification.GeneralReflection.
Require Import Undecidability.FOL.PA.
Import MetaCoq.Template.Ast MetaCoq.Template.TemplateMonad.Core.
Import Vector.VectorNotations.
Require Import String List.

(* ** Signature for PA axiomatisation, containing function symbols for set operations *)



Fixpoint num n := match n with 0 => zero | S n => σ (num n) end.

Section ReificationExample.
  Context (D':Type).
  Context {I : interp D'}.
  Context {D_ext : extensional I}.

  Notation "'izero'" := (@i_func _ _ D' I Zero ([])) (at level 1) : PA_Notation.
  Notation "'iσ' x" := (@i_func _ _ D' I Succ ([x])) (at level 37) : PA_Notation.
  Notation "x 'i⊕' y" := (@i_func _ _ D' I Plus ([x ; y]) ) (at level 39) : PA_Notation.
  Notation "x 'i⊗' y" := (@i_func _ _ D' I Mult ([x ; y]) ) (at level 38) : PA_Notation.
  Notation "x 'i=' y" := (@i_atom _ _ D' I Eq ([x ; y]) ) (at level 40) : PA_Notation.
  Open Scope string_scope.

  Fixpoint inum n := match n with 0 => izero | S n => iσ (inum n) end.
  Definition proj1 {X:Type} {Y:X->Type} (H:{x:X&Y x}) : X := match H with existT x y => x end.
  Definition proj2 {X:Type} {Y:X->Type} (H:{x:X&Y x}) : Y (proj1 H) := match H with existT x y => y end.

  Instance PA_reflector : tarski_reflector := buildDefaultTarski 
                        (i_func (f:=Zero) (Vector.nil D')) 
                        (anyVariableOf ("D'" :: nil)).

  Lemma example (a b : D) : representableP 0 (a i⊕ b i= b i⊕ a).
  Proof. represent. Show Proof. Defined. (* Defined, so we can pull out the representative witness later *)

  Eval cbn in (proj1 (example izero izero)).


  Lemma only_logic : representableP 0 (~(True <-> False)).
  Proof. represent. Defined.

  Lemma large : representableP 0 
    (True /\ True /\ True \/ False /\ True /\ True /\ True \/ False /\ ~False \/ True <-> True
    /\ True /\ True /\ True \/ False /\ True /\ True /\ True \/ False /\ ~False \/ True <-> True
    \/ True /\ True /\ True \/ False /\ True /\ True /\ True \/ False /\ ~False \/ True <-> True
    /\ True /\ True /\ True \/ False /\ True /\ True /\ True \/ False /\ ~False \/ True <-> True
    /\ True /\ True /\ True \/ False /\ True /\ True /\ True \/ False /\ ~False \/ True <-> True
    \/ True /\ True /\ True \/ False /\ True /\ True /\ True \/ False /\ ~False \/ True <-> True).
  Proof. Time representNP. Restart. Time represent. Defined. 

  Section ReflectionExtension.
    (* Do a correctness proof for the specific extension *)
    Definition mergeNum (rho:nat -> D) (n:nat) : representsF (inum n) (num n) rho.
    Proof. unfold representsF. induction n.
    * easy.
    * cbn. do 2 f_equal. cbn in IHn. now rewrite IHn.
    Defined.
    (* Define some MetaCoq terms we will need later *)
    MetaCoq Quote Definition qNum := inum.
    MetaCoq Quote Definition qMergeNum := mergeNum.
    MetaCoq Quote Definition qMergeTermNum := @num.

    Definition mergeEqProp (rho:nat -> D) (d1 d2 : D) (t1 t2 : Syntax.term) : representsF d1 t1 rho -> representsF d2 t2 rho -> @representsP _ _ 0 (t1==t2) rho (d1 = d2).
    Proof. intros pt1 pt2. cbn. unfold representsF in pt1, pt2. cbn in pt1, pt2. rewrite pt1, pt2. now rewrite D_ext.
    Defined.
    MetaCoq Quote Definition qMergeFormEq := (constructForm Eq).
    MetaCoq Quote Definition qMergeEqProp := mergeEqProp.


    Definition reifyCoqEq : baseConnectiveReifier := fun tct qff l fuel envTerm env fPR fTR => match l with (tv::x::y::nil) => if maybeD tct tv then
                                               xr <- fTR tct qff x envTerm env ;;
                                               yr <- fTR tct qff y envTerm env ;; let '((xt,xp),(yt,yp)) := (xr,yr) in
                                               ret (tApp qMergeFormEq (xt::yt::nil), tApp qMergeEqProp (envTerm::x::y::xt::yt::xp::yp::nil)) else fail "Eq applied to wrong type" | _ => fail "Eq constructor applied to != 2 terms" end.
    Definition varsCoqEq : baseConnectiveVars := fun lst fuel tct _ fUVT => match lst with tv::x::y::nil => if maybeD tct tv then
                                               xr <- fUVT x;;
                                               yr <- fUVT y;;
                                               ret (List.app xr yr) else fail "Eq applied to wrong type" | _ => fail "Eq constructor applied to != 2 terms" end.
    Definition reifyBLC (s:string) : baseConnectiveReifier := match s with "eq"%string => reifyCoqEq | _ => fun _ _ _ _ _ _ _ _ => fail ("Unknown connective " ++ s) end.
    Definition varsBLC (s:string) : baseConnectiveVars := match s with "eq"%string => varsCoqEq | _ => fun _ _ _ _ _ => fail ("Unknown connective " ++ s) end.
    Definition findVarsTerm : termFinderVars := fun fuel t fUVT => match t with (tApp qMu (k::nil)) => ret nil | _ => fail "Fail" end.
    Definition reifyTerm : termFinderReifier := fun tct qff fuel t envTerm env fTR => match t with tApp qMu (k::nil) => ret (tApp qMergeTermNum (k::nil), tApp qMergeNum (envTerm::k::nil)) | _ => fail "Fail" end.
  End ReflectionExtension.
  (* If we want to extend the capabilities, we define an extension point instance *)
  Instance PA_reflector_ext : tarski_reflector_extensions PA_reflector := {| (*Cannot define instance in section because they are dropped afterwards *)
    baseLogicConnHelper := Some (reifyBLC);
    baseLogicVarHelper := Some (varsBLC);
    termReifierVarHelper := Some (findVarsTerm);
    termReifierReifyHelper := Some (reifyTerm);
    formReifierVarHelper := None;
    formReifierReifyHelper := None
  |}.

  Lemma foo (a : D) (n:nat) : representableP 1 (fun (b:D) => forall (c:D), exists (d:D), a i⊕ b i⊗ c = iσ d /\ (True \/ ~False) <-> (inum n = inum n)).
  Proof. represent. Defined.

  Eval cbn in (fun d n => proj1 (foo d n)).



End ReificationExample.
