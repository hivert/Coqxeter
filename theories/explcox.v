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
From mathcomp Require Import bigop fingroup perm morphism alt gproduct action.
From mathcomp Require Import ssralg zmodp div.
Require Import ssrcompl present coxsystem.


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Import GroupScope.


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


Section Dihedral.

Variable (n0 : nat).
Local Notation n := n0.+2.

(** We construct the Dihedral group as the semi-direct product Zn X| Bool *)
Definition bact (i : 'I_n) (b : bool) : 'I_n :=
  if b then (-i)%R else i.

Fact bactF : bact^~ false =1 id.
Proof. by []. Qed.
Fact bact_morph i : act_morph bact i.
Proof. by case => [][]//=; rewrite opprK. Qed.
Definition bact_action := TotalAction bactF bact_morph.

Fact bactP : is_groupAction [set: 'I_n] bact_action.
Proof.
move=> b _; rewrite inE; apply/andP; split.
  by apply/subsetP => i; rewrite !inE.
apply/morphicP=> /= i j _ _; rewrite !actpermE /=.
by case: b => //=; rewrite opprD.
Qed.
Definition bact_gaction := GroupAction bactP.
Definition dihedral := sdprod_by bact_gaction.

Definition dh1 : dihedral := sdpair2 _ true.
Definition dh2 : dihedral := sdpair2 _ true * sdpair1 _ Zp1.

Lemma dh1K : dh1 * dh1 = 1.
Proof. by rewrite -morphM //= morph1. Qed.
Lemma dh1V : dh1 ^-1 =  dh1.
Proof. by rewrite inv_sq1 ?dh1K. Qed.
Lemma dh2K : dh2 * dh2 = 1.
Proof.
apply val_inj; rewrite /= !val_insubd !inE /= !(mulg1, mul1g).
apply/eqP; rewrite xpair_eqE eqxx /=.
by rewrite /mulg /= addNr.
Qed.
Lemma dh2V : dh2 ^-1 =  dh2.
Proof. by rewrite inv_sq1 ?dh2K. Qed.


Lemma dh12E : dh1 * dh2 = sdpair1 _ Zp1.
Proof.
rewrite /dh1 /dh2; apply val_inj => /=.
rewrite !val_insubd !inE /= !(mulg1, mul1g).
apply/eqP; rewrite xpair_eqE eqxx /=.
by rewrite oppr0 /mulg /= add0r.
Qed.
Lemma dh12xnE : (dh1 * dh2) ^+ n = 1.
Proof.
rewrite dh12E -morphX ?inE //=.
by rewrite [X in sdpair1 _ X](_ : _ = 1) ?morph1 // Zp_expn.
Qed.
Lemma dh21xnE : (dh2 * dh1) ^+ n = 1.
Proof. by apply invg_inj; rewrite invg1 -expgVn invMg dh1V dh2V dh12xnE. Qed.


(* bool here is just a fintype with two elements *)
Definition dihedral_coxmat (p : bool * bool) :=
  if (p.1 == p.2) then 1%N else n.
Lemma dihedral_coxmatP : dihedral_coxmat \is a Coxeter_matrix.
Proof. by apply/Coxeter_matrixP; split => [][|][|]. Qed.

Lemma dihedral_present :
  ((fun b => if b then dh1 else dh2), coxrels_of_mat dihedral_coxmat)
    \present [set: dihedral].
Proof.
apply And3 => /=.
- apply/esym/eqP; rewrite -subTset.
  apply/subsetP => [[[b [i ltin]] /= Hbi]] _.
  apply/generatedP => /= G /subsetP Hsub.
  have        dh1G : dh1 \in G by apply/Hsub/imsetP; exists true.
  have {Hsub} dh2G : dh2 \in G by apply/Hsub/imsetP; exists false.
  rewrite (sdpairE (SdPair _ Hbi)) /=; apply groupM.
    by case: b {Hbi} => //; rewrite morph1; apply: group1.
  by rewrite Zp1_ord morphX ?inE // groupX //= -dh12E groupM.
- rewrite /dihedral_coxmat; apply/sat_coxmatP => [][|][|] /=.
  + by rewrite dh1K expg1.
  + exact: dh12xnE.
  + exact: dh21xnE.
  + by rewrite dh2K expg1.
- move=> gT genH /sat_coxmatP satH.
  have satB b : genH b * genH b = 1.
    by have := satH b b; rewrite /dihedral_coxmat /= eqxx expg1.
  have : satisfy ([:: ([:: ord0; ord0], [::])])
                 (fun _ : 'I_1 => genH true).
    by apply/satisfyP=> r; rewrite inE => /eqP ->{r} /=; rewrite !biggseq satB.
  case/(presm_spec present_bool) => fB /(_ ord0) eqfB.
  have satZn : (genH true * genH false) ^+ n = 1.
  by have := satH true false; rewrite /dihedral_coxmat.
  have : satisfy [:: (nseq n ord0, [::])]
                 (fun _ : 'I_1 => genH true * genH false).
    move: (nseq n ord0) (size_nseq n (ord0 : 'I_1)) => s sizes.
    apply/satisfyP => /= r; rewrite inE => /eqP ->{r} /=; rewrite !biggseq.
    by rewrite /= big_const_seq count_predT sizes iter_mulg satZn.
  case/(presm_spec (present_Zp _)) => fZn /(_ ord0) eqfZn.
  have fBZact : morph_act bact_action 'J fZn fB.
    move=> [i ltin] /= a; rewrite fun_if Zp1_ord.
    rewrite morphV ?inE // !morphX ?inE //= {fZn}eqfZn.
    case: a; last by rewrite morph1 conjg1.
    rewrite {fB}eqfB conjgE -expgVn invMg !inv_sq1 //.
    elim: i {ltin} => [|i]; first by rewrite !expg0 mul1g satB.
    rewrite !expgS !mulgA satB mul1g => ->.
    by rewrite !mulgA -[X in X * _ ^+ i]mulgA satB mulg1.
  exists [morphism of xsdprodm (to := bact_gaction) (in2W fBZact)] => [][|] /=.
  - rewrite /xsdprodm /= sdprodmEr /=; last by apply imset_f; rewrite !inE.
    by rewrite /restrm /= invmE ?inE.
  - rewrite /xsdprodm /= morphM /= ?inE //.
    rewrite sdprodmEr /=; last by apply imset_f; rewrite !inE.
    rewrite /restrm /= invmE ?inE // eqfB.
    rewrite sdprodmEl /=; last by apply imset_f; rewrite !inE.
    by rewrite /restrm /= invmE ?inE // eqfZn mulgA satB mul1g.
Qed.

End Dihedral.


Section Products.

Variables (gT : finGroupType) (A B G : {coxgrp gT}).

Definition dprod_coxmat (p : ('I[A] + 'I[B]) * ('I[A] + 'I[B])) :=
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
