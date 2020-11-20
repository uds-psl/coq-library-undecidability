From Undecidability.L.Tactics Require Import LTactics.

From Undecidability.L Require Import Functions.Decoding.

Class linTimeDecodable `(X:Type) `{decodable X}: Type :=
  {
    c__linDec : nat;
    comp_enc_lin : computableTime' (decode X) (fun x _ => (size x *c__linDec + c__linDec,tt));
  }.

Arguments linTimeDecodable : clear implicits.
Arguments linTimeDecodable _ {_ _}.

Arguments c__linDec : clear implicits.
Arguments c__linDec _ {_ _ _}.

Existing Instance comp_enc_lin.