(** * Complement and fix to SSRefect/MathComp *)
(******************************************************************************)
(*      Copyright (C) 2021      Florent Hivert <florent.hivert@lri.fr>        *)
(*                                                                            *)
(*  Distributed under the terms of the GNU General Public License (GPL)       *)
(*                                                                            *)
(*    This code is distributed in the hope that it will be useful,            *)
(*    but WITHOUT ANY WARRANTY; without even the implied warranty of          *)
(*    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU       *)
(*    General Public License for more details.                                *)
(*                                                                            *)
(*  The full text of the GPL is available at:                                 *)
(*                                                                            *)
(*                  http://www.gnu.org/licenses/                              *)
(******************************************************************************)
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.
From mathcomp Require Import choice fintype finset.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Section ImsetFix.

Variables aT aT2 rT : finType.
Implicit Types (f g : aT -> rT) (D : {pred aT}) (R : {pred rT}).

Lemma eq_preimset f g R : f =1 g -> f @^-1: R = g @^-1: R.
Proof. by move=> eqfg; apply/setP => y; rewrite !inE eqfg. Qed.

Lemma eq_imset f g D : f =1 g -> f @: D = g @: D.
Proof.
move=> eqfg; apply/setP=> y.
by apply/imsetP/imsetP=> [] [x Dx ->]; exists x; rewrite ?eqfg.
Qed.

Lemma eq_in_imset f g D : {in D, f =1 g} -> f @: D = g @: D.
Proof.
move=> eqfg; apply/setP => y.
by apply/imsetP/imsetP=> [] [x Dx ->]; exists x; rewrite ?eqfg.
Qed.

Lemma eq_in_imset2 (f g : aT -> aT2 -> rT) (D : {pred aT}) (D2 : {pred aT2}) :
  {in D & D2, f =2 g} -> f @2: (D, D2) = g @2: (D, D2).
Proof.
move=> eqfg; apply/setP => y.
by apply/imset2P/imset2P=> [] [x x2 Dx Dx2 ->]; exists x x2; rewrite ?eqfg.
Qed.

End ImsetFix.
