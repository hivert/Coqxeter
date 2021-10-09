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
From mathcomp Require Import choice fintype finset finfun tuple.
From mathcomp Require Import bigop fingroup perm morphism alt gproduct.
Require Import ssrcompl.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Import GroupScope.

Reserved Notation "gr \present G" (at level 10).

Section DefPresentation.

Implicit Types (gT hT : finGroupType) (I J : finType).

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

Lemma satisfy_eq gens1 gens2 rels :
  gens1 =1 gens2 -> satisfy rels gens1 = satisfy rels gens2.
Proof.
suff impl g1 g2 : g1 =1 g2 -> satisfy rels g1 -> satisfy rels g2.
  by move=> Hgen; apply/idP/idP; apply: impl.
move=> Heq /satisfyP Hsat; apply/satisfyP => /= r rin.
transitivity (\prod_(i <- r.1) g1 i).
  by apply eq_bigr => i _; rewrite Heq.
by rewrite Hsat //; apply eq_bigr => i.
Qed.

Lemma perm_satisfy rels1 rels2 gens :
  perm_eq rels1 rels2 -> satisfy rels1 gens = satisfy rels2 gens.
Proof. by rewrite/satisfy => /perm_all ->. Qed.

Lemma satisfy_cat rels1 rels2 gens :
  satisfy (rels1 ++ rels2) gens = satisfy rels1 gens && satisfy rels2 gens.
Proof. exact: all_cat. Qed.

End Satisfy.


Lemma satisfy_map gT I J (f : I -> J) (gens : J -> gT) rels :
  satisfy rels (gens \o f) =
  satisfy [seq (map f r.1, map f r.2) | r <- rels] gens.
Proof. by rewrite /satisfy all_map; apply eq_all => r; rewrite /= !big_map. Qed.

Lemma satisfy_can gT I J (f : I -> J) f_inv :
    cancel f f_inv ->
  forall (gens : I -> gT) rels,
  satisfy [seq (map f r.1, map f r.2) | r <- rels] (gens \o f_inv) =
  satisfy rels gens.
Proof.
move=> fK gens rels; rewrite -satisfy_map; apply satisfy_eq => x.
by rewrite /= fK.
Qed.

Lemma satisfy_perm gT I J (p : {perm I}) rels (gens : I -> gT) :
  satisfy [seq (map p r.1, map p r.2) | r <- rels] (gens \o p^-1) =
  satisfy rels gens.
Proof. exact/satisfy_can/permK. Qed.

Lemma morph_satisfy gT (G : {group gT}) hT (H : {group hT}) I
      (f : {morphism G >-> hT}) (gens : I -> gT) rels :
  (forall i, gens i \in G) -> satisfy rels gens -> satisfy rels (f \o gens).
Proof.
move=> memgens /satisfyP /= sat; apply/satisfyP => s {}/sat /(congr1 f).
by rewrite !morph_prod.
Qed.


Definition presentation_of gT I (gr : (I -> gT) * (seq (seq I * seq I)))
       (G : {group gT}) (ph : phantom {set gT} G) : Prop :=
  [/\ G = <<[set gr.1 i | i : I]>> :> {set gT},
   satisfy gr.2 gr.1
   & forall (hT : finGroupType) (gensH : I -> hT),
       satisfy gr.2 gensH ->
       exists presm : {morphism G >-> hT}, forall i, presm (gr.1 i) = gensH i].

End DefPresentation.

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

Lemma present_eq (gens' : I -> gT) :
  gens =1 gens' -> (gens', rels) \present G.
Proof.
have [/= eqG satG morphG] := prG.
move=> eqgens; apply And3 => //=.
- by rewrite eqG; congr <<_>>; exact: eq_imset.
- by rewrite -(satisfy_eq _ eqgens).
- move=> hT gensH /morphG => [][phi eqphi].
  by exists phi => i; rewrite -eqgens eqphi.
Qed.

Lemma presentP x :
  reflect (exists l (c : 'I_l -> I), \prod_i gens (c i) = x) (x \in G).
Proof.
apply (iffP idP) => [| [l [dec <-{x}]]]; last exact: group_prod.
rewrite present_gen => /gen_prodgP[l [gen Hgen ->{x}]].
have {}get_gen i : {j : I | gen i == gens j}.
  by apply sigW => /=; move: Hgen => /(_ i) /imsetP[/= j _ ->]; exists j.
have dec_in i : gen i \in G by case: (get_gen i) => j /eqP ->.
have decE i : gen i = gens (val (get_gen i)).
  by case: (get_gen i) => j /= /eqP.
by exists l, (fun i => val (get_gen i)); apply eq_bigr.
Qed.

Lemma present_seq_minP x :
  x \in G ->
  {s : seq I | \prod_(i <- s) gens i = x &
                forall s', \prod_(i <- s') gens i = x -> size s <= size s'}.
Proof.
move=> xin.
suff : exists l, [exists t : l.-tuple I, \prod_(i <- t) gens i == x].
  move=> exP; case: (ex_minnP exP) => l /existsP/sigW [/= t /eqP eqt tmin].
  exists t => [//|s' eqs'].
  rewrite size_tuple; apply: tmin; apply/existsP.
  by exists (in_tuple s'); rewrite eqs'.
move/presentP : xin => [l [f eqx]]; exists l; apply/existsP.
exists [tuple f i | i < l]; rewrite -eqx big_tuple.
by apply/eqP/eq_bigr => /= i _; rewrite tnth_mktuple.
Qed.

Lemma present_seqP x :
  x \in G -> {s : seq I | \prod_(i <- s) gens i = x}.
Proof. by move=> /present_seq_minP [s Hs _]; exists s. Qed.


Section Morphism.

Variable (hT : finGroupType) (gensH : I -> hT).
Hypothesis (sat : satisfy rels gensH).

Lemma presm_spec :
  {presm : {morphism G >-> hT} | forall i, presm (gens i) = gensH i}.
Proof.
suff : {m : {ffun gT -> hT} | morphic G m && [forall i, m (gens i) == gensH i]}.
  move=> [m /andP [morm /forallP /= Heq]].
  by exists (morphm_morphism morm) => /= i; rewrite morphmE; apply/eqP.
apply sigW; case: prG => [_ _ /(_ _ _ sat)] [phi eq_phi] /=.
exists (finfun phi); apply/andP; split.
  by apply/morphicP => x y xG yG /=; rewrite !ffunE morphM.
by apply/forallP => /= i; rewrite ffunE eq_phi.
Qed.
Definition presm := let: exist m _ := presm_spec in m.
Lemma presmP : forall i, presm (gens i) = gensH i.
Proof. by rewrite /presm; case: presm_spec. Qed.

Lemma presmE (phi : {morphism G >-> hT}) :
  (forall i, phi (gens i) = gensH i) -> {in G, phi =1 presm}.
Proof.
move=> Heq x /presentP [l [decc <-{x}]].
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

End Morphism.


Section InjMorphism.

Variables (hT: finGroupType) (phi : {morphism G >-> hT}).
Hypothesis (inj_phi : 'injm phi).

Lemma morph_present : (phi \o gens, rels) \present (phi @* G).
Proof.
have gsub : [set gens i | i : I] \subset G by rewrite present_gen subset_gen.
have gin i : gens i \in G by rewrite present_gen mem_gen // imset_f.
apply And3 => /=.
- rewrite [X in phi @* X]present_gen (morphim_gen _ gsub) /morphim.
  by rewrite (setIidPr gsub) -imset_comp /=.
- apply/satisfyP => /= [][lft rgt] /= /(satisfyP _ _ present_sat) /=.
  by rewrite -!morph_prod // => ->.
- move=> Ht gensH satH.
  have psi_morph : {in phi @* G & ,
                       {morph (presm satH) \o invm inj_phi : x y / x * y}}.
    by rewrite -morphpre_invm => x y xin yin; rewrite !morphM.
  by exists (Morphism psi_morph) => i /=; rewrite invmE ?presmP.
Qed.

End InjMorphism.

End Presentation.
#[export] Hint Resolve present_mem : core.


Section PresentationMap.

Variables (gT : finGroupType) (G : {group gT}).
Variables (I J : finType) (f : I -> J) (f_inv : J -> I).
Hypothesis (f_invK : cancel f_inv f).
Variables (gens : J -> gT) (rels : seq (seq I * seq I)).

Lemma present_map :
  (gens \o f, rels) \present G ->
  (gens, [seq (map f r.1, map f r.2) | r <- rels]) \present G.
Proof.
move=> prG; apply And3 => /=.
- rewrite (present_gen prG); congr <<_>>.
  apply/setP => x; apply/imsetP/imsetP => [] [/= y _ ->{x}].
  + by exists (f y).
  + by exists (f_inv y) => //; rewrite f_invK.
- by rewrite -satisfy_map // (present_sat prG).
- move=> ht gensH; rewrite -satisfy_map => satH.
  exists (presm prG satH) => j.
  by rewrite -(f_invK j) presmP.
Qed.

End PresentationMap.

Section PresentationBij.

Variables (gT : finGroupType) (G : {group gT}).
Variables (I J : finType) (f : I -> J) (f_inv : J -> I).
Hypothesis (fK : cancel f f_inv) (f_invK : cancel f_inv f).
Variables (gens : I -> gT) (rels : seq (seq I * seq I)).

Lemma present_bij :
  (gens \o f_inv, [seq (map f r.1, map f r.2) | r <- rels]) \present G <->
  (gens, rels) \present G.
Proof.
split.
- move/(present_map fK).
  rewrite -map_comp (eq_map (f2 := id)) ?map_id // => [[r1 r2]] /=.
  rewrite -!map_comp -[in RHS](map_id r1) -[in RHS](map_id r2).
  by congr (_, _); apply eq_map => i /=; rewrite fK.
- have /present_eq : gens =1 (gens \o f_inv) \o f by move=> i; rewrite /= fK.
  by move=> /[apply]/present_map; apply.
Qed.

End PresentationBij.

Section Permute.

Variables (gT : finGroupType) (G : {group gT})
          (I : finType) (gens : I -> gT) (rels : seq (seq I * seq I)).

Lemma present_perm (p : {perm I}) :
  (gens \o p, [seq (map p^-1 r.1, map p^-1 r.2) | r <- rels]) \present G <->
  (gens, rels) \present G.
Proof. by apply: present_bij; [apply: permKV | apply permK]. Qed.

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
apply And3 => //=.
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
apply And3 => /=.
- apply/esym/eqP; rewrite -subTset.
  apply/subsetP => [[|]] _; apply/generatedP=> G /subsetP/(_ true trin) //.
  by move=> trinG; exact: (groupM trinG trinG).
- by rewrite andbT big_nil big_cons big_seq1.
- move=> gT genH; rewrite andbT big_nil big_cons big_seq1 /= => /eqP Heq.
  pose phi b := if b then genH ord0 else 1.
  have phi_morph : {in [set: bool] & , {morph phi : x y / x * y}}.
    by case=> /= [] [] _ _ /=; rewrite ?Heq ?mulg1 ?mul1g.
  by exists (Morphism phi_morph) => i /=; rewrite ord1.
Qed.

End PresentBool.


Section PresentDProd.

Variables (gT : finGroupType) (A B G : {group gT}).
Hypothesis (eqG : A \x B = G).
Variables (IA : finType) (gensA : IA -> gT) (relsA : seq (seq IA * seq IA)).
Variables (IB : finType) (gensB : IB -> gT) (relsB : seq (seq IB * seq IB)).

Definition dprod_gens (k : IA + IB) :=
  match k with | inl i => gensA i | inr i => gensB i end.

Definition dprod_rels :=
  [seq (map inl r.1, map inl r.2) | r <- relsA] ++
  [seq (map inr r.1, map inr r.2) | r <- relsB] ++
  [seq ([:: inl i; inr j], [:: inr j; inl i]) | i <- enum IA, j <- enum IB].

Theorem present_dprod :
  (gensA, relsA) \present A -> (gensB, relsB) \present B ->
  (dprod_gens, dprod_rels) \present G.
Proof.
move: eqG => /dprodP [_ eqGAB ABC _] prA prB.
apply And3 => /=.
- apply/eqP; rewrite eqEsubset; apply/andP; split.
  + rewrite -eqGAB mulG_subG (present_gen prA) (present_gen prB); apply/andP.
    by split; apply/genS/subsetP=> x /imsetP[i _ ->{x}];
      apply/imsetP; [exists (inl i)| exists (inr i)].
  + rewrite gen_subG; apply/subsetP => i /imsetP[x _ ->{i} /=].
    rewrite /dprod_gens; case: x => [a|b]; rewrite -eqGAB.
    * by rewrite -(mulg1 (gensA a)) mem_mulg // (present_mem prA).
    * by rewrite -(mul1g (gensB b)) mem_mulg // (present_mem prB).
- rewrite !satisfy_cat.
  apply/and3P; split; apply/satisfyP => /= [][lft rgt] /=.
  + move/mapP => /= [[r1 r2] rin /= [->{lft} ->{rgt}]]; rewrite !big_map.
    exact: (satisfyP _ _ (present_sat prA) _ rin).
  + move/mapP => /= [[r1 r2] rin /= [->{lft} ->{rgt}]]; rewrite !big_map.
    exact: (satisfyP _ _ (present_sat prB) _ rin).
  + move/allpairsP => [[iA iB] [_ _] [->{lft} ->{rgt}]].
    rewrite !big_cons big_nil !mulg1 /=.
    move/subsetP/(_ _ (present_mem prB iB))/centP : ABC => -> //.
    exact: (present_mem prA iA).
- move=> Ht gensH /satisfyP /= Hsat.
  have satA : satisfy relsA (fun i => gensH (inl i)).
    apply/satisfyP=> /= rel Hin.
    rewrite -!(big_map inl xpredT gensH); apply: (Hsat (_, _)).
    by rewrite !mem_cat map_f.
  move: (presm _ _) (presmP prA satA) => {satA} fA eq_fA.
  have satB : satisfy relsB (fun i => gensH (inr i)).
    apply/satisfyP=> /= rel Hin.
    rewrite -!(big_map inr xpredT gensH); apply: (Hsat (_, _)).
    by rewrite !mem_cat map_f //= orbT.
  move: (presm _ _) (presmP prB satB) => {satB} fB eq_fB.
  suff cAB : fB @* B \subset 'C(fA @* A).
    exists [morphism of dprodm eqG cAB] => [[a|b]] /=.
    + by rewrite dprodmEl // (present_mem prA).
    + by rewrite dprodmEr // (present_mem prB).
  rewrite [X in fA @* X](present_gen prA) [X in fB @* X](present_gen prB).
  rewrite !morphim_gen; first last.
    + by apply/subsetP => x /imsetP[b _ ->{x}]; apply (present_mem prB).
    + by apply/subsetP => x /imsetP[a _ ->{x}]; apply (present_mem prA).
  rewrite gen_subG /= cent_gen; apply/subsetP => /= x /imsetP[y].
  rewrite inE => /andP[_ /imsetP[b _ ->{y} ->{x}]].
  apply/centP => x /imsetP[y].
  rewrite inE => /andP[_ /imsetP[a _ ->{y} ->{x}]].
  rewrite /commute.
  have /Hsat/= : ([:: inl a; inr b], [:: inr b; inl a]) \in dprod_rels.
    by rewrite !mem_cat allpairs_f ?orbT // mem_enum.
  by rewrite !big_cons big_nil !mulg1 eq_fA eq_fB => ->.
Qed.

End PresentDProd.
