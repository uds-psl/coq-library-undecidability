From Undecidability.L Require Import Prelim.MoreBase Util.L_facts AbstractMachines.LargestVar.
Require Import Lia.
Require Export Undecidability.L.AbstractMachines.FlatPro.ProgramsDef.

(** * Abstract L machines *)

(** *** Program size *)

Definition sizeT t := 
  match t with
    varT n => 1 + n
  |  _ => 1
  end.  

Definition sizeP (P:Pro) := sumn (map sizeT P) + 1.
Hint Unfold sizeP : core.


Lemma size_geq_1 s: 1<= size s.
Proof.
  induction s;cbn. all:try lia.
Qed.

Lemma sizeP_size' s :size s <= sumn (map sizeT (compile s)).
Proof.
  induction s;cbn.
  all:autorewrite with list. all:cbn. all:try lia.
Qed.

Lemma sizeP_size s: sumn (map sizeT (compile s)) + 1<= 2*size s.
Proof.
  induction s;cbn.
  all:autorewrite with list. all:cbn. all:try lia.
Qed.


Lemma le_length_sizeP P :
  length P <= sizeP P.
Proof.
  unfold sizeP. induction P as [|[]];cbn in *;try Lia.lia.
Qed.


Lemma length_compile_leq s : |compile s| <= 2*size s.
Proof.
  induction s;cbn. all:autorewrite with list;cbn. all:nia.
Qed.

(** *** Programm Decomposition *)


Fixpoint jumpTarget (l:nat) (res:Pro) (P:Pro) : option (Pro*Pro) :=
  match P with
  | retT :: P => match l with
                | 0 => Some (res,P)
                | S l => jumpTarget l (res++[retT]) P
                end
  | lamT :: P => jumpTarget (S l) (res++[lamT])P
  | t :: P    => jumpTarget l (res++[t]) P
  | []        => None
  end.


Lemma jumpTarget_correct s c:
  jumpTarget 0 [] (compile s ++ retT::c) = Some (compile s,c).
Proof.
  change (Some (compile s,c)) with (jumpTarget 0 ([]++compile s) (retT::c)).
  generalize 0.
  generalize (retT::c) as c'. clear c.
  generalize (@nil Tok) as c. 
  induction s;intros c' c l.
  -reflexivity.
  -cbn. autorewrite with list. rewrite IHs1,IHs2. cbn. now autorewrite with list. 
  -cbn. autorewrite with list. rewrite IHs. cbn. now autorewrite with list.
Qed.

(** *** Program Substitution *)

Fixpoint substP (P:Pro) k Q : Pro :=
  match P with
    [] => []
  | lamT::P => lamT::substP P (S k) Q
  | retT::P => retT::match k with
                      S k => substP P k Q
                    | 0 => [(* doesnt matter *)]
                    end
  | varT k'::P => (if k' =? k then Q else [varT k'])++substP P k Q
  | appT::P => appT::substP P k Q
  end.


Lemma substP_correct' s k c' t:
  substP (compile s++c') k (compile t)
  = compile (subst s k t)++substP c' k (compile t).
Proof.
  induction s in k,c'|-*;cbn.
  -destruct (Nat.eqb_spec n k);cbn. all:now autorewrite with list.
  -autorewrite with list. rewrite IHs1,IHs2. reflexivity.
  -autorewrite with list. rewrite IHs. reflexivity. 
Qed.

Lemma substP_correct s k t:
  substP (compile s) k (compile t) = compile (subst s k t).
Proof.
  replace (compile s) with (compile s++[]) by now autorewrite with list.
  rewrite substP_correct'. now autorewrite with list. 
Qed.


(** *** Injectivity of Programm Encoding *)

(** returning the internal state as inr allows for stronger results w.r.t. decompiling initial segments*)
Fixpoint decompile l P A {struct P}: (list term) + (nat * Pro * list term) :=
  match P with
    retT::P => match l with
                0 => inr (l,retT::P,A)
              | S l => match A with
                        s::A => decompile l P (lam s::A)
                      | [] => inr (S l, retT::P, A)
                      end
              end
  | varT n::P => decompile l P (var n::A)
  | lamT::P =>  decompile (S l) P A
  | appT::P => match A with
               t::s::A => decompile l P (app s t::A)
             | _ => inr (l, appT::P, A)
              end
  | [] => inl A
  end.

Lemma decompile_correct' l s P A:
  decompile l (compile s++P) A = decompile l P (s::A).
Proof.
  induction s in l,P,A|-*. all:cbn.
  -congruence.
  -autorewrite with list. rewrite IHs1. cbn. rewrite IHs2. reflexivity.
  -autorewrite with list. rewrite IHs. reflexivity.
Qed.


Lemma decompile_correct l s:
  decompile l (compile s) [] = inl [s].
Proof.
  specialize (decompile_correct' l s [] []) as H. autorewrite with list in H. rewrite H. easy.
Qed.

(** We can not show a lemma that if decompile produces a term, the inout was a compilation as decompile itself sometimes decompiles incorrect programs if the lamTs are at wrong positions*)
Lemma decompile_resSize l P A B:
  decompile l P A = inl B -> sumn (map size B) <= sumn (map size A) + sumn (map sizeT P).
Proof.
  induction P as [ |[] P] in l,A|-*.
  -cbn. intros [= ->]. nia.
  -cbn. intros ->%IHP. cbn. nia.
  -destruct A as [ | ? []]. 1,2:easy.
   intros ->%IHP. cbn. nia.
  -cbn.  intros ->%IHP. nia.
  -destruct l. easy.
   destruct A as []. 1:easy.
   intros ->%IHP. cbn. nia.
   all:cbn.
Qed.

Lemma compile_inj s s' :
  compile s = compile s' -> s = s'.
Proof.
  intros eq.
  specialize (@decompile_correct' 0 s [] []) as H1.
  specialize (@decompile_correct' 0 s' [] []) as H2.
  rewrite eq in H1. rewrite H1 in H2. now inv H2.
Qed.

Lemma compile_neq_nil s:
  compile s <> [].
Proof.
  edestruct (compile s) eqn:eq. 2:easy.
  specialize decompile_correct' with (l:=0) (s:=s) (P:=[]) (A:=[]).
  rewrite eq.
  cbn. easy.
Qed.

Lemma compile_inj_retT s s' P P':
  compile s ++ retT::P = compile s' ++ retT::P' -> s = s' /\ P = P'.
Proof.
  intros eq.
  specialize (@decompile_correct' 0 s (retT::P) []) as H1.
  specialize (@decompile_correct' 0 s' (retT::P') []) as H2.
  rewrite eq in H1. rewrite H1 in H2.
  now inv H2.
Qed.

Definition Tok_eqb (t t' : Tok) :=
  match t,t' with
    varT n, varT n' => Nat.eqb n n'
  | retT,retT => true
  | lamT, lamT => true
  | appT, appT => true
  | _,_ => false
  end.

Lemma Tok_eqb_spec t t' : reflect (t = t') (Tok_eqb t t').
Proof.
  destruct t,t'. all:cbn. destruct (Nat.eqb_spec n n0);[subst|].
  all:try left;eauto.
  all:right;congruence.
Qed.

Definition largestVarT t :=
  match t with
    varT n => n
  | _ => 0
  end.


Definition largestVarP P := maxl (map largestVarT P).

Lemma largestVar_compile s :
  largestVarP (compile s) = largestVar s.
Proof.
  unfold largestVarP in *. 
  induction s;cbn.
  -Lia.lia.
  -autorewrite with list. rewrite ! maxl_app.
   rewrite IHs1,IHs2. cbn. Lia.lia.
  -autorewrite with list. rewrite ! maxl_app.
   rewrite IHs. cbn. Lia.lia.
Qed.
