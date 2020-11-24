(* * Notations for [Fin.t] *)
(* Author: Maximilian Wuttke *)


From Undecidability.Shared.Libs.PSL Require Import Fin.

Notation "'Fin0'"  := (Fin.F1).
Notation "'Fin1'"  := (Fin.FS Fin0).
Notation "'Fin2'"  := (Fin.FS Fin1).
Notation "'Fin3'"  := (Fin.FS Fin2).
Notation "'Fin4'"  := (Fin.FS Fin3).
Notation "'Fin5'"  := (Fin.FS Fin4).
Notation "'Fin6'"  := (Fin.FS Fin5).
Notation "'Fin7'"  := (Fin.FS Fin6).
Notation "'Fin8'"  := (Fin.FS Fin7).
Notation "'Fin9'"  := (Fin.FS Fin8).
Notation "'Fin10'" := (Fin.FS Fin9).
Notation "'Fin11'" := (Fin.FS Fin10).
Notation "'Fin12'" := (Fin.FS Fin11).
Notation "'Fin13'" := (Fin.FS Fin12).
Notation "'Fin14'" := (Fin.FS Fin13).
Notation "'Fin15'" := (Fin.FS Fin14).
Notation "'Fin16'" := (Fin.FS Fin15).
Notation "'Fin17'" := (Fin.FS Fin16).
Notation "'Fin18'" := (Fin.FS Fin17).
Notation "'Fin19'" := (Fin.FS Fin18).
Notation "'Fin20'" := (Fin.FS Fin19).
Notation "'Fin21'" := (Fin.FS Fin20).
Notation "'Fin22'" := (Fin.FS Fin21).
Notation "'Fin23'" := (Fin.FS Fin22).
Notation "'Fin24'" := (Fin.FS Fin23).
Notation "'Fin25'" := (Fin.FS Fin24).
Notation "'Fin26'" := (Fin.FS Fin25).
Notation "'Fin27'" := (Fin.FS Fin26).
Notation "'Fin28'" := (Fin.FS Fin27).
Notation "'Fin29'" := (Fin.FS Fin28).
Notation "'Fin30'" := (Fin.FS Fin29).
Notation "'Fin31'" := (Fin.FS Fin30).
Notation "'Fin32'" := (Fin.FS Fin31).
Notation "'Fin33'" := (Fin.FS Fin32).
Notation "'Fin34'" := (Fin.FS Fin33).
Notation "'Fin35'" := (Fin.FS Fin34).
Notation "'Fin36'" := (Fin.FS Fin35).
Notation "'Fin37'" := (Fin.FS Fin36).
Notation "'Fin38'" := (Fin.FS Fin37).
Notation "'Fin39'" := (Fin.FS Fin38).
Notation "'Fin40'" := (Fin.FS Fin39).
Notation "'Fin41'" := (Fin.FS Fin40).
Notation "'Fin42'" := (Fin.FS Fin41).
Notation "'Fin43'" := (Fin.FS Fin42).
Notation "'Fin44'" := (Fin.FS Fin43).
Notation "'Fin45'" := (Fin.FS Fin44).
Notation "'Fin46'" := (Fin.FS Fin45).
Notation "'Fin47'" := (Fin.FS Fin46).
Notation "'Fin48'" := (Fin.FS Fin47).
Notation "'Fin49'" := (Fin.FS Fin48).
Notation "'Fin50'" := (Fin.FS Fin49).
Notation "'Fin51'" := (Fin.FS Fin50).
Notation "'Fin52'" := (Fin.FS Fin51).
Notation "'Fin53'" := (Fin.FS Fin52).
Notation "'Fin54'" := (Fin.FS Fin53).
Notation "'Fin55'" := (Fin.FS Fin54).
Notation "'Fin56'" := (Fin.FS Fin55).
Notation "'Fin57'" := (Fin.FS Fin56).
Notation "'Fin58'" := (Fin.FS Fin57).
Notation "'Fin59'" := (Fin.FS Fin58).
Notation "'Fin60'" := (Fin.FS Fin59).
Notation "'Fin61'" := (Fin.FS Fin60).
Notation "'Fin62'" := (Fin.FS Fin61).
Notation "'Fin63'" := (Fin.FS Fin62).
Notation "'Fin64'" := (Fin.FS Fin63).
Notation "'Fin65'" := (Fin.FS Fin64).
Notation "'Fin66'" := (Fin.FS Fin65).
Notation "'Fin67'" := (Fin.FS Fin66).
Notation "'Fin68'" := (Fin.FS Fin67).
Notation "'Fin69'" := (Fin.FS Fin68).
Notation "'Fin70'" := (Fin.FS Fin69).
Notation "'Fin71'" := (Fin.FS Fin70).
Notation "'Fin72'" := (Fin.FS Fin71).
Notation "'Fin73'" := (Fin.FS Fin72).
Notation "'Fin74'" := (Fin.FS Fin73).
Notation "'Fin75'" := (Fin.FS Fin74).
Notation "'Fin76'" := (Fin.FS Fin75).
Notation "'Fin77'" := (Fin.FS Fin76).
Notation "'Fin78'" := (Fin.FS Fin77).
Notation "'Fin79'" := (Fin.FS Fin78).
Notation "'Fin80'" := (Fin.FS Fin79).
Notation "'Fin81'" := (Fin.FS Fin80).
Notation "'Fin82'" := (Fin.FS Fin81).
Notation "'Fin83'" := (Fin.FS Fin82).
Notation "'Fin84'" := (Fin.FS Fin83).
Notation "'Fin85'" := (Fin.FS Fin84).
Notation "'Fin86'" := (Fin.FS Fin85).
Notation "'Fin87'" := (Fin.FS Fin86).
Notation "'Fin88'" := (Fin.FS Fin87).
Notation "'Fin89'" := (Fin.FS Fin88).
Notation "'Fin90'" := (Fin.FS Fin89).
Notation "'Fin91'" := (Fin.FS Fin90).
Notation "'Fin92'" := (Fin.FS Fin91).
Notation "'Fin93'" := (Fin.FS Fin92).
Notation "'Fin94'" := (Fin.FS Fin93).
Notation "'Fin95'" := (Fin.FS Fin94).
Notation "'Fin96'" := (Fin.FS Fin95).
Notation "'Fin97'" := (Fin.FS Fin96).
Notation "'Fin98'" := (Fin.FS Fin97).
Notation "'Fin99'" := (Fin.FS Fin98).

(* Generate arbitrary big Fin.t's *)

Ltac getFin i :=
  match i with
  | 0 =>
    eapply Fin.F1
  | S ?i' =>
    eapply Fin.FS;
    ltac:(getFin i')
  end.

(*
Section Test.
  Compute ltac:(getFin 4) : Fin.t 100.
  Compute ltac:(getFin 8) : Fin.t 100.
  Compute ltac:(getFin 15) : Fin.t 100.
  Compute ltac:(getFin 16) : Fin.t 100.
  Compute ltac:(getFin 23) : Fin.t 100.
  Compute ltac:(getFin 42) : Fin.t 100.
End Test.
*)