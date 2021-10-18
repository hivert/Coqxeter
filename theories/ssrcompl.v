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
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype seq ssrnat.
From mathcomp Require Import choice fintype finset fingroup bigop.

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



Section GroupCompl.

Import GroupScope.

Variables (gT : finGroupType).
Implicit Types (x y z : gT).

Lemma inv_sq1 x : x * x = 1 -> x^-1 = x.
Proof. by move=> /(congr1 (mulg^~ x^-1)); rewrite mulgK mul1g => {2}->. Qed.

Lemma conjgg x : x ^ x = x.
Proof. by rewrite conjgE mulKg. Qed.

Lemma eq_conjg x y z : (x == y ^ z) = (x ^ (z ^-1) == y).
Proof. by rewrite -(inj_eq (conjg_inj z ^-1)) -conjgM mulgV conjg1. Qed.

Lemma iter_mulg n x : iter n (mulg x) 1 = x ^+ n.
Proof. by rewrite /expgn /expgn_rec Monoid.iteropE /=. Qed.

Lemma prodgV I r (P : pred I) (F : I -> gT) :
  (\prod_(i <- r | P i) F i) ^-1 = \prod_(i <- rev r | P i) (F i)^-1.
Proof.
elim: r => [| r i IHr]; first by rewrite !big_nil invg1.
rewrite big_cons rev_cons -cats1 big_cat big_cons big_nil /= mulg1.
rewrite -{}IHr -{4}invg1 -fun_if -invMg.
by case: (P r); last by rewrite mul1g.
Qed.

End GroupCompl.
