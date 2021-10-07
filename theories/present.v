(** * Group Presentations *)
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
From mathcomp Require Import choice fintype finset finfun.
From mathcomp Require Import bigop fingroup perm morphism alt.
Require Import ssrcompl.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Import GroupScope.

Reserved Notation "gr \present G" (at level 10).


Section Satisfy.

Variable (gT : finGroupType) (I : finType).
Implicit Type (gens : I -> gT) (rels : seq (seq I * seq I)).

Definition satisfy rels gens :=
  all (fun r => \prod_(i <- r.1) gens i == \prod_(i <- r.2) gens i) rels.

Lemma satisfyP rels gens :
  reflect (forall r, r \in rels ->
                           \prod_(i <- r.1) gens i = \prod_(i <- r.2) gens i)
          (satisfy rels gens).
Proof. by apply: (iffP allP) => /= [H r /H /eqP| H r /H ->]. Qed.

Lemma satisfy_eq_impl gens1 gens2 rels :
  gens1 =1 gens2 -> satisfy rels gens1 -> satisfy rels gens2.
Proof.
move=> Heq /satisfyP Hsat; apply/satisfyP => /= r rin.
transitivity (\prod_(i <- r.1) gens1 i).
  by apply eq_bigr => i _; rewrite Heq.
by rewrite Hsat //; apply eq_bigr => i.
Qed.
Lemma satisfy_eq gens1 gens2 rels :
  gens1 =1 gens2 -> satisfy rels gens1 = satisfy rels gens2.
Proof. by move=> Hgen; apply/idP/idP; apply: satisfy_eq_impl. Qed.

Lemma perm_satisfy rels1 rels2 gens :
  perm_eq rels1 rels2 -> satisfy rels1 gens = satisfy rels2 gens.
Proof. by rewrite/satisfy => /perm_all ->. Qed.

Lemma satisfy_perm_impl (p : {perm I}) rels gens :
  satisfy rels gens ->
  satisfy [seq ([seq p^-1 i | i <- r.1], [seq p^-1 i | i <- r.2]) |
           r <- rels] (gens \o p).
Proof.
move/satisfyP => H; apply/satisfyP => s' /mapP [/= r rin ->{s'} /=].
rewrite !big_map; transitivity (\prod_(j <- r.1) gens j).
  by apply eq_bigr => i _; rewrite permKV.
by rewrite H //; apply eq_bigr => i _; rewrite permKV.
Qed.

Lemma satisfy_perm (p : {perm I}) rels gens :
  satisfy
    [seq ([seq p^-1 i | i <- r.1], [seq p^-1 i | i <- r.2]) | r <- rels]
    (gens \o p) =
  satisfy rels gens.
Proof.
apply/idP/idP => /satisfy_perm_impl // /(_ p^-1).
have /satisfy_eq -> : ((gens \o p) \o p^-1) =1 gens.
  by move=> i /=; rewrite permKV.
congr satisfy.
rewrite -map_comp -[RHS]map_id; apply eq_map => [[r1 r2]] /=.
rewrite -!map_comp -[in RHS](map_id r1) -[in RHS](map_id r2).
by congr (_, _); apply eq_map => i /=; rewrite permK.
Qed.

Lemma satisfy_cat rels1 rels2 gens :
  satisfy (rels1 ++ rels2) gens = satisfy rels1 gens && satisfy rels2 gens.
Proof. exact: all_cat. Qed.

End Satisfy.

Lemma morph_satisfy (I : finType)
      (gT : finGroupType) (G : {group gT})
      (hT : finGroupType) (H : {group hT})
      (f : {morphism G >-> hT}) (gens : I -> gT) rels :
  (forall i, gens i \in G) -> satisfy rels gens -> satisfy rels (f \o gens).
Proof.
move=> memgens /satisfyP /= sat; apply/satisfyP => s {}/sat /(congr1 f).
by rewrite !morph_prod.
Qed.

Inductive presentation_of (gT : finGroupType)
       (I : finType) (gr : (I -> gT) * (seq (seq I * seq I)))
       (G : {group gT}) (ph : phantom {set gT} G) : Prop :=
  Presentation of
    (G = <<[set gr.1 i | i : I]>> :> {set gT}) &
    (satisfy gr.2 gr.1) &
    (forall (hT : finGroupType) (gensH : I -> hT),
        satisfy gr.2 gensH ->
        exists presm : {morphism G >-> hT}, forall i, presm (gr.1 i) = gensH i).

Notation "gr \present G" := (presentation_of gr (Phantom {set _} G)).


Section Presentation.

Variables (gT : finGroupType) (G : {group gT})
          (I : finType) (gens  : I -> gT) (rels  : seq (seq I * seq I)).
Hypothesis prG : (gens, rels) \present G.

Lemma present_gen : G = <<[set gens i | i : I]>> :> {set gT}.
Proof. by case: prG. Qed.
Lemma present_sat : satisfy rels gens.
Proof. by case: prG. Qed.
Lemma present_mem  i : gens i \in G.
Proof. by rewrite present_gen mem_gen // imset_f. Qed.
Hint Resolve present_mem : core.

Lemma presentP x :
  reflect (exists l (c : 'I_l -> I), x = \prod_i gens (c i)) (x \in G).
Proof.
apply (iffP idP); last by move=> [l [dec ->{x}]]; apply group_prod.
rewrite present_gen => /gen_prodgP [l [gen Hgen ->{x}]].
have {}Hgen i : {j : I | gen i == gens j}.
  by apply sigW => /=; move: Hgen => /(_ i) /imsetP [/= j _ ->]; exists j.
have dec_in i : gen i \in G by case: (Hgen i) => j /eqP ->.
pose get_gen (i : 'I_l) := let: exist j _ := Hgen i in j.
have decE i : gen i = gens (get_gen i).
  by rewrite /get_gen; case: (Hgen i) => j /eqP.
by exists l, get_gen; apply eq_bigr.
Qed.


Section PresentMorphism.

Variable (hT : finGroupType) (gensH : I -> hT).
Hypothesis (sat : satisfy rels gensH).

Lemma presm_spec :
  {presm : {morphism G >-> hT} | forall i, presm (gens i) = gensH i}.
Proof.
suff : {m : {ffun gT -> hT} | morphic G m && [forall i, m (gens i) == gensH i]}.
  move=> [m /andP [morm /forallP /= Heq]].
  by exists (morphm_morphism morm) => /= i; rewrite morphmE; apply/eqP.
apply sigW; case: prG => [_ _ /(_ _ _ sat)] [m Heq] /=.
exists (finfun m); apply/andP; split.
  by apply/morphicP => x y xG yG /=; rewrite !ffunE morphM.
by apply/forallP => /= i; rewrite ffunE Heq.
Qed.
Definition presm := let: exist m _ := presm_spec in m.
Lemma presmP : forall i, presm (gens i) = gensH i.
Proof. by rewrite /presm; case: presm_spec. Qed.

Lemma presmE (phi : {morphism G >-> hT}) :
  (forall i, phi (gens i) = gensH i) -> {in G, phi =1 presm}.
Proof.
move=> Heq x /presentP [l [decc ->{x}]].
rewrite !morph_prod //.
by apply: eq_bigr => /= i _; rewrite Heq presmP.
Qed.

Lemma morphim_presm : presm @* G = <<[set gensH i | i : I]>>.
Proof.
have gsub : [set gens i | i : I] \subset G by rewrite present_gen subset_gen.
rewrite [X in presm @* X]present_gen (morphim_gen _ gsub).
rewrite /morphim (setIidPr gsub) -imset_comp; congr <<_>>.
by apply: eq_imset => i /=; rewrite presmP.
Qed.

End PresentMorphism.


Section InjMorphism.

Variables (hT: finGroupType) (f : {morphism G >-> hT}).
Hypothesis (inj_f : 'injm f).

Lemma morph_present : (f \o gens, rels) \present (f @* G).
Proof.
have [/= eqG /satisfyP/= satG morphG] := prG.
have gsub : [set gens i | i : I] \subset G by rewrite eqG subset_gen.
have gin i : gens i \in G by rewrite eqG mem_gen // imset_f.
constructor => /=.
- move=> {satG morphG}.
  rewrite [X in f @* X]eqG (morphim_gen _ gsub) /morphim.
  by rewrite (setIidPr gsub) -imset_comp /=.
- move=> {morphG}.
  apply/satisfyP => /= [][lft rgt] /= {}/satG /=.
  by rewrite -!morph_prod // => ->.
- move=> {satG} Ht gensH {}/morphG [fG eq_fG].
  have phi_morph : {in f @* G & , {morph fG \o invm inj_f : x y / x * y}}.
    by rewrite -morphpre_invm => x y xin yin; rewrite !morphM.
  by exists (Morphism phi_morph) => i /=; rewrite invmE.
Qed.

End InjMorphism.

End Presentation.


Section Permute.

Variables (gT : finGroupType) (G : {group gT})
          (I : finType) (gens  : I -> gT) (rels  : seq (seq I * seq I)).

Lemma present_perm (p : {perm I}) :
  (gens, rels) \present G ->
  (gens \o p,
   [seq ([seq p^-1 i | i <- r.1], [seq p^-1 i | i <- r.2]) | r <- rels])
    \present G.
Proof.
move=> prG; constructor => /=.
- rewrite (present_gen prG); congr <<_>>.
  apply/setP => x; apply/imsetP/imsetP => [] [/= y _ ->{x}].
  + by exists (p^-1 y) => //; rewrite permKV.
  + by exists (p y).
- exact/satisfy_perm_impl/(present_sat prG).
- move=> ht gensH.
  have /satisfy_eq -> : gensH =1 (gensH \o p^-1 \o p).
    by move=> x; rewrite /= permK.
  rewrite satisfy_perm => satH; exists (presm prG satH) => i.
  by rewrite presmP /= permK.
Qed.

End Permute.


Section Isomorphism.

Variable gT hT : finGroupType.
Variables (G : {group gT}) (H : {group hT}).
Variables (I : finType) (gens  : I -> gT) (rels  : seq (seq I * seq I)).
Hypothesis (prG : (gens, rels) \present G).

Lemma presm_id (sat : satisfy rels gens) : {in G, presm prG sat =1 id}.
Proof.
have : forall i, idm G (gens i) = (gens i) by [].
by move/(presmE prG sat) => Heq x /Heq.
Qed.

Lemma present_isog (gh : I -> hT) : (gh, rels) \present H -> G \isog H.
Proof.
move=> prH; apply/isogP.
have satG := present_sat prG; have satH := present_sat prH.
have:= morphim_presm prG satH; rewrite -(present_gen prH) => impH.
have phi_morph : morphic G (presm prH satG \o presm prG satH).
  apply/morphicP => x y xinG yinG.
  by rewrite /= !morphM // -impH mem_morphim.
have : forall i, morphm phi_morph (gens i) = gens i.
  by move=> i; rewrite morphmE /= !presmP.
move=> /(presmE prG satG) presmP.
have {presmP} presmK : {in G, cancel (presm prG satH) (presm prH satG)}.
  by move => x Hx; move: presmP => /(_ x Hx) /=; rewrite presm_id.
exists (presm prG satH) => //.
exact/injmP/(can_in_inj presmK).
Qed.

Lemma isog_present :
  G \isog H -> {gensh: I -> hT | (gensh, rels) \present H}.
Proof.
move=> /isog_isom [f /isomP [injf imf]].
have [/=]:= morph_present prG injf; rewrite imf => genH sat morph.
by exists (f \o gens).
Qed.

End Isomorphism.


Section PresentTriv.

Variable (gT : finGroupType).

Lemma present_trivG : (fun _ : 'I_0 => 1, [::]) \present [1 gT].
Proof.
constructor => //=.
- rewrite -gen0; congr << _ >>; apply/setP => x; rewrite inE.
  by apply/esym/negP => /imsetP[[]].
- by move=> hT gensH _; exists [morphism of trivm 1%G] => [[]].
Qed.

End PresentTriv.


Section PresentBool.

Lemma present_bool :
  (fun _ : 'I_1 => true, [:: ([:: ord0; ord0], [::])]) \present [set: bool].
Proof.
have trin : true \in [set true | _ : 'I_1] by apply/imsetP; exists ord0.
constructor => /=.
- apply/esym/eqP; rewrite -subTset.
  apply/subsetP => [[|]] _; apply/generatedP=> G /subsetP/(_ true)/(_ trin) => //.
  by move=> trinG; exact: (groupM trinG trinG).
- by rewrite andbT big_nil big_cons big_seq1.
- move=> gT genH; rewrite andbT big_nil big_cons big_seq1 /= => /eqP Heq.
  pose phi b := if b then genH ord0 else 1.
  have phi_morph : {in [set: bool] & , {morph phi : x y / x * y}}.
    by case=> /= [] [] _ _ /=; rewrite ?Heq ?mulg1 ?mul1g.
  by exists (Morphism phi_morph) => i /=; rewrite ord1.
Qed.

End PresentBool.
