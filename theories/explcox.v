(** * Example of Coxeter groups *)
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
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From mathcomp Require Import choice fintype finset finfun order fingraph.
From mathcomp Require Import tuple bigop fingroup perm morphism alt gproduct.
Require Import present coxsystem.


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope group_scope.

Section Triv.

Variables (gT : finGroupType).

Definition set1_coxmat := fun _ : 'I_0 * 'I_0 => 0.
Definition set1_coxgen := fun _ : 'I_0 => 1 : gT.
Lemma set1_coxmatP : set1_coxmat \is a Coxeter_matrix.
Proof. by apply/Coxeter_matrixP; split => [][]. Qed.
Lemma set1_present :
  (set1_coxgen, coxrels_of_mat set1_coxmat) \present [1 gT].
Proof.
have nbrel : size (coxrels_of_mat set1_coxmat) = 0.
  by rewrite size_allpairs size_enum_ord muln0.
suff -> : coxrels_of_mat set1_coxmat = [::] by exact: present_trivG.
by apply/nilP; rewrite /nilp nbrel.
Qed.
Canonical set1_coxgrp := CoxGrp (CoxSys set1_coxmatP set1_present).

End Triv.

Definition bool_coxmat := fun _ : 'I_1 * 'I_1 => 1%N.
Definition bool_coxgen := fun _ : 'I_1 => true.
Lemma bool_coxmatP : bool_coxmat \is a Coxeter_matrix.
Proof. by apply/Coxeter_matrixP; split => [][[|]// H1][[|]]. Qed.
Lemma bool_present :
  (bool_coxgen, coxrels_of_mat bool_coxmat) \present [set: bool].
Proof.
have nbrel : size (coxrels_of_mat bool_coxmat) = 1%N.
  by rewrite size_allpairs size_enum_ord muln1.
suff -> : coxrels_of_mat bool_coxmat = [:: ([:: ord0; ord0], [::])]
    by exact: present_bool.
apply (eq_from_nth (x0 := ([::], [::]))); rewrite nbrel // => [][|]// _.
rewrite /= /coxrels_of_mat.
suff -> : enum (ordinal_finType 1) = [:: ord0] by rewrite allpairs1l /=.
apply (eq_from_nth (x0 := ord0)); rewrite size_enum_ord // => i _.
by rewrite !ord1.
Qed.
Canonical bool_coxgrp := CoxGrp (CoxSys bool_coxmatP bool_present).


Section Products.

Variables (gT : finGroupType) (A B G : {coxgrp gT}).

Definition dprod_coxmat :=
  fun (p : ('I[A] + 'I[B]) * ('I[A] + 'I[B])) =>
    match p with
    | (inl i, inl j) | (inr i, inr j) => 'M_(i, j)
    | _ => 2
    end.

Lemma dprod_coxmatP : dprod_coxmat \is a Coxeter_matrix.
Proof.
have /Coxeter_matrixP [AD AS]:= coxmatP A.
have /Coxeter_matrixP [BD BS]:= coxmatP B.
rewrite /dprod_coxmat; apply/Coxeter_matrixP.
by split => [][a1|b1][a2|b2]; rewrite -?AD -?BD.
Qed.

Lemma dprod_coxmatE (hT : finGroupType) :
  satisfy (gT := hT) (coxrels_of_mat dprod_coxmat)
  =1 satisfy (dprod_rels (coxrels_of_mat 'M[A]) (coxrels_of_mat 'M[B])).
Proof.
move=> g; rewrite !satisfy_cat -!satisfy_map.
apply/sat_coxmatP/and3P => [sat|].
- split; try do [apply/sat_coxmatP => i j /=; exact: sat].
  apply/satisfyP => /= r /allpairsP[[a b] /= [_ _] ->{r}] /=.
  rewrite /= !biggseq (coxmat_sC dprod_coxmatP) //.
  exact/sat_coxmatP.
- move => [/sat_coxmatP/= satA /sat_coxmatP/= satB comAB].
  have sqA i : g (inl i) * g (inl i) = 1 by have:= satA i i; rewrite coxmdiag.
  have sqB i : g (inr i) * g (inr i) = 1 by have:= satB i i; rewrite coxmdiag.
  have {}comAB (a : 'I[A]) (b : 'I[B]) : commute (g (inl a)) (g (inr b)).
    have := satisfyP _ _ comAB ([:: inl a; inr b], [:: inr b; inl a]).
    by rewrite /= !biggseq; apply; exact/allpairs_f/mem_enum/mem_enum.
  move=> [a1|b1][a2|b2]; rewrite /= ?expgS ?expg0 ?mulg1 ?mulgA.
  + exact: satA.
  + by rewrite {1}comAB -[X in X * _ = 1]mulgA sqA mulg1 sqB.
  + by rewrite -{1}comAB -[X in X * _ = 1]mulgA sqB mulg1 sqA.
  + exact: satB.
Qed.

Hypothesis (eqG : A \x B = G).

Lemma coxdprod_present :
  (dprod_gens 'S[A] 'S[B], coxrels_of_mat dprod_coxmat) \present G.
Proof.
have prG := present_dprod eqG (coxpresP A) (coxpresP B).
constructor => /=.
- exact: present_gen prG.
- by rewrite dprod_coxmatE (present_sat prG).
- move=> hT gensH; rewrite (dprod_coxmatE gensH) => Hsat.
  by exists (presm prG Hsat) => p; rewrite presmP.
Qed.
Definition dprod_coxgrp := CoxGrp (CoxSys dprod_coxmatP coxdprod_present).

End Products.


Section Morph.

Variables (gT hT: finGroupType) (W : {coxgrp gT}).
Variable (f : {morphism W >-> hT}).
Hypothesis (inj_f : 'injm f).

Lemma morph_present : (f \o 'S[W], coxrels_of_mat 'M[W]) \present (f @* W).
Proof. exact: (morph_present (coxpresP W) inj_f). Qed.
Canonical morph_coxgrp := CoxGrp (CoxSys (coxmatP W) morph_present).

End Morph.
