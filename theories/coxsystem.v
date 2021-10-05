(** * Coxeter system *)
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
From mathcomp Require Import tuple bigop fingroup perm morphism alt.
Require Import natbar present.


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope group_scope.

Local Reserved Notation "''s_' i" (at level 2, format "''s_' i").
Local Reserved Notation "''s_' [ w ] "
      (at level 2, w at level 100, format "''s_' [ w ]").
Local Reserved Notation "''M_' p" (at level 2, format "''M_' p").


Section GroupCompl.

Variables (gT : finGroupType) (W : {group gT}).

Lemma conjgg (x : gT) : x ^ x = x.
Proof. by rewrite conjgE mulKg. Qed.

Lemma eq_conjg (x y z : gT) : (x == y ^ z) = (x ^ (z^-1) == y).
Proof. by rewrite -(inj_eq (conjg_inj z ^-1)) -conjgM mulgV conjg1. Qed.

End GroupCompl.


Section CoxeterMatrix.
Context {I : finType}.

Definition Coxeter_matrix :=
  [qualify a m : I * I -> natbar | [&&
    [forall i : I, forall j : I, (m (i, j) >= Nat 1%N)%O],
    [forall i : I, forall j : I, (i == j) == (m (i, j) == Nat 1%N)] &
    [forall i : I, forall j : I, m (i, j) == m (j, i)] ]].

Lemma Coxeter_matrixP m :
  reflect [/\ (forall i j : I, (m (i, j) >= Nat 1%N)%O),
              (forall i j : I, (i == j) = (m (i, j) == Nat 1%N)) &
              (forall i j : I, m (i, j) = m (j, i)) ]
          (m \is a Coxeter_matrix).
Proof.
apply (iffP and3P) => [[] | [H1 H2 H3]].
- move => /forallP H1 /forallP H2 /forallP H3.
  split => i; try by apply/forallP.
  + by move=> j; have := H2 i => /forallP/(_ j)/eqP.
  + by move=> j; have := H3 i => /forallP/(_ j)/eqP.
- by split; apply/forallP => i; apply/forallP => j //; apply/eqP.
Qed.

Variable (m : I * I -> natbar).
Hypothesis (iscox : m \is a Coxeter_matrix).

Lemma coxmpos i j : (m (i, j) >= Nat 1%N)%O.
Proof. by move/Coxeter_matrixP : iscox => []. Qed.
Lemma coxmdiagE i j : (i == j) = (m (i, j) == Nat 1).
Proof. by move/Coxeter_matrixP : iscox => []. Qed.
Lemma coxmdiag i : m (i, i) = Nat 1.
Proof. by have := coxmdiagE i i; rewrite eqxx => /esym/eqP. Qed.
Lemma coxmsym i j : m (i, j) = m (j, i).
Proof. by move/Coxeter_matrixP : iscox => []. Qed.

End CoxeterMatrix.

Section Defs.

Variables (gT : finGroupType).

Definition coxrel (T : Type) (x y : T) (exp : natbar) : seq T :=
  if exp is Nat n then flatten (nseq n [:: x; y])
  else [::].
Definition coxrels_of_mat (I : finType) (M : I * I -> natbar)
  : seq (seq I * seq I) :=
  [seq (coxrel i j (M (i, j)), [::]) | i <- enum I, j <- enum I].

Record Coxeter_system (W : {group gT}) := CoxSys {
  coxind : finType;
  coxgen : coxind -> gT;
  coxmat : coxind * coxind -> natbar;
  _ : coxmat \is a Coxeter_matrix;
  _ : (coxgen, coxrels_of_mat coxmat) \present W
}.

Structure coxgrp_type := CoxGrp {
  coxgroup :> {group gT};
  _ : Coxeter_system coxgroup;
}.

Definition coxgrp_of of phant gT := coxgrp_type.
Local Notation coxgrpT := (coxgrp_of (Phant gT)).
Identity Coercion type_of_coxgrp : coxgrp_of >-> coxgrp_type.

Definition coxgrp (A : {group gT}) Sys : coxgrpT := @CoxGrp A Sys.
Definition clone_coxgrp G :=
  let: CoxGrp _ Sys := G return {type of CoxGrp for G} -> coxgrpT
  in fun k => k Sys.

Definition coxsys_of (G : coxgrpT) : Coxeter_system G :=
  let: CoxGrp _ Sys := G in Sys.

End Defs.

Notation "{ 'coxgrp' gT }" := (coxgrp_of (Phant gT))
  (at level 0, format "{ 'coxgrp'  gT }") : type_scope.

Notation "[ 'coxgrp' 'of' G ]" := (clone_coxgrp (@coxgrp _ G))
  (at level 0, format "[ 'coxgrp'  'of'  G ]") : form_scope.
Notation coxsys G := (coxsys_of (clone_coxgrp (@coxgrp _ G))).


Section Example.

Variables (gT : finGroupType).

Definition set1_coxmat := fun _ : 'I_0 * 'I_0 => Inf.
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
Canonical set1_coxsys := CoxGrp (CoxSys set1_coxmatP set1_present).

End Example.

Definition bool_coxmat := fun _ : 'I_1 * 'I_1 => Nat 1.
Definition bool_coxgen := fun _ : 'I_1 => true.
Lemma bool_coxmatP : bool_coxmat \is a Coxeter_matrix.
Proof. by apply/Coxeter_matrixP; split => [][[|]// H1][[|]]. Qed.
Lemma bool_present :
  (bool_coxgen, coxrels_of_mat bool_coxmat) \present [group of [set: bool]].
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
Canonical bool_coxsys := CoxGrp (CoxSys bool_coxmatP bool_present).

Notation "''I[' g ]" := (@coxind _ _ (coxsys g)).
Notation "''S[' g ]" := (@coxgen _ _ (coxsys g)).
Notation "''s[' g ']_' i" := ('S[g] i) (at level 2).
Notation "''M[' g ']'" := (@coxmat _ _ (coxsys g)) (at level 2).
Notation "''M[' g ']_' p" := ('M[g] p) (at level 2).
Notation "''I'" := ('I[_]).
Notation "''S'" := ('S[_]).
Notation "''s_' i" := ('S i).
Notation "''s[' g ']_' [ w ] " := (\prod_(i <- w) 's[g]_i) (at level 2).
Notation "''s_' [ w ] " := (\prod_(i <- w) 's_i).
Notation "''M'" := ('M[ _ ]).
Notation "''M_' p" := ('M p).


Section Basic.

Variables (gT : finGroupType) (W : {coxgrp gT}).
Local Notation "''I'" := 'I[W].
Implicit Types (i : 'I) (s : seq 'I).


Definition rank := #|[set: 'I]|.
Definition coxirred := n_comp (fun i j => 'M[W]_(i, j) >= Nat 3)%O predT == 1%N.
Lemma coxmatP : 'M[W] \is a Coxeter_matrix.
Proof. by case: W => [G []]. Qed.
Lemma coxpresP : ('S[W], coxrels_of_mat 'M[W]) \present (W : {group _}).
Proof. by case: W => [G []]. Qed.

Lemma coxnil : 's[W]_[[::]] = 1.
Proof. by rewrite big_nil. Qed.
Lemma coxw1 i : 's_[[:: i]] = 's_i.
Proof. by rewrite big_seq1. Qed.

Lemma memcoxs i : 's_i \in W.
Proof. by have [<- _ _] := coxpresP; exact/mem_gen/imset_f. Qed.
Lemma memcoxw s : 's_[s] \in W.
Proof. by apply group_prod => i _; apply memcoxs. Qed.

Lemma memcoxP w : reflect (exists s, 's_[s] = w) (w \in W).
Proof.
have [<- _ _] /= := coxpresP.
apply (iffP gen_prodgP) => [[n [f Hf ->{w}]] | [s <-{w}]].
- have getg j : {h | f j == 's[W]_h}.
    by apply sigW; move/(_ j) : Hf => /imsetP[k _ ->]; exists k.
  exists [seq val (getg i) | i <- index_enum [finType of 'I_n]].
  rewrite /= big_map; apply eq_bigr => j _ /=.
  by case: (getg j) => [k /= /eqP ->].
- exists (size s), (fun j => 's_(tnth (in_tuple s) j)) => [j|].
    exact: imset_f.
  by rewrite -(big_tuple _ _ _ xpredT 'S) /=.
Qed.

Lemma cox_flattennseq i j n :
  's_[flatten (nseq n [:: i; j])] = ('s_i * 's_j) ^+ n.
Proof.
elim: n => [| n IHn] /=; first by rewrite expg0 big_nil.
by rewrite expgS !big_cons mulgA -{}IHn.
Qed.
Lemma coxrelP i j n : 'M_(i, j) = Nat n -> ('s_i * 's_j) ^+ n = 1.
Proof.
move=> matij.
have [_ /satisfyP/= psat _] /= := coxpresP.
have {matij}/psat : (coxrel i j (Nat n), [::]) \in coxrels_of_mat 'M.
  by rewrite -matij; apply: allpairs_f; apply: mem_enum.
by rewrite /coxrel /= big_nil cox_flattennseq.
Qed.

Lemma exps2 i : 's_i ^+ 2 = 1.
Proof. by have /coxmdiag/(_ i)/coxrelP <- := coxmatP; rewrite expg1. Qed.
Lemma mulss i : 's_i * 's_i = 1.
Proof. exact: exps2. Qed.
Lemma coxsV i : 's_i ^-1 = 's_i.
Proof. by rewrite -[LHS](mul1g) -(mulss i) mulgK. Qed.
Lemma mulKs i : cancel (mulg 's_i) (mulg 's_i).
Proof. by move=> x; rewrite mulgA mulss mul1g. Qed.
Lemma mulsK i : cancel (mulg^~ 's_i) (mulg^~ 's_i).
Proof. by move=> x; rewrite -mulgA mulss mulg1. Qed.

Lemma coxsC i j : 'M_(i, j) = Nat 2 -> commute 's_i 's_j.
Proof.
move/coxrelP; rewrite /commute => /(congr1 (mulg ('s_ j * 's_ i))).
by rewrite mulg1 !mulgA mulsK mulss mul1g.
Qed.

End Basic.
#[export] Hint Resolve memcoxs : core.
#[export] Hint Resolve memcoxw : core.


Section Reflections.

Variables (gT : finGroupType) (W : {coxgrp gT}).
Local Notation "''I'" := 'I[W].
Local Notation word := (seq 'I).
Implicit Types (i : 'I) (s : word).


Definition reflexions := [set 's_i ^ w | i in 'I, w in W].

Lemma reflsW t : t \in reflexions -> t \in W.
Proof. by move/imset2P => [i w _ /groupJr + ->] => ->; apply memcoxs. Qed.
Lemma coxs_refls i : 's_i \in reflexions.
Proof. by apply/imset2P; exists i 1 => //; rewrite conjg1. Qed.
Lemma conj_refls w t : w \in W -> t \in reflexions -> t ^ w \in reflexions.
Proof.
move=> win /imset2P [i v _ vin ->{t}].
apply/imset2P; exists i (v * w) => //; first exact: groupM.
by rewrite conjgM.
Qed.
Lemma conjs_refls i t : t \in reflexions -> t ^ 's_i \in reflexions.
Proof. by move/conj_refls; apply; apply: memcoxs. Qed.
Lemma reflsK t : t \in reflexions -> t * t = 1.
Proof. by move/imset2P => [i w _ _ ->]; rewrite -conjMg mulss conj1g. Qed.

Lemma coxwrev s : 's_[rev s] = 's_[s] ^-1.
Proof.
elim: s => [|s0 s IHs]; first by rewrite !big_nil invg1.
by rewrite rev_cons -cats1 big_cat big_seq1 !big_cons /= {}IHs invMg coxsV.
Qed.

Definition tword s := 's_[s ++ behead (rev s)].

(** Eq 1.10 *)
Lemma twordE s si : tword (rcons s si) = 's_[s] * 's_si * 's_[s]^-1.
Proof.
by rewrite /tword rev_rcons -cats1 -catA !big_cat /= big_seq1 coxwrev mulgA.
Qed.
(** Eq 1.11 *)
Lemma Eq1_11 n s :
  n < size s -> tword (take n.+1 s) * 's_[s] = 's_[take n s ++ drop n.+1 s].
Proof.
rewrite -{3}(cat_take_drop n.+1 s) !big_cat /= mulgA => ltns.
rewrite -(take_take (leqnSn n) s).
case/lastP: (take n.+1 s) (size_takel ltns) => // s' sn {ltns}.
rewrite size_rcons -{2 3}cats1 big_cat /= => [][{2}<-].
rewrite take_size_cat // /tword rev_rcons /= big_cat /=.
by rewrite coxwrev !mulgA mulgKV -cats1 big_cat big_seq1 /= mulsK.
Qed.
Lemma Eq1_12 n s:
  n <= size s ->
  's_[take n s] = \prod_(j <- rev (iota 1 n)) tword (take j s).
Proof.
elim: n => [| n IHn] ltns; first by rewrite /= take0 !big_nil.
rewrite -{2}addn1 iotaD /= rev_cat big_cat /= big_seq1 -{}IHn ?(ltnW ltns) //.
apply: (mulIg 's_[drop n s]).
rewrite -[RHS]mulgA -[in RHS]big_cat cat_take_drop /= add1n Eq1_11 //.
rewrite -{1}(addn1 n) takeD -{2}(cat_take_drop 1 (drop n s)) drop_drop add1n.
rewrite !big_cat /= mulgA.
case: (drop n s) => [|l1 d] /=; first by rewrite big_nil !mulg1.
by rewrite take0 big_seq1 mulsK.
Qed.
Lemma tword_refl n s : n < size s -> tword (take n.+1 s) \in reflexions.
Proof.
move/size_takel; case/lastP: (take _ _) => // {}s sn _.
rewrite twordE -{1}(invgK 's_[s]) -mulgA -conjgE; apply: imset2_f => //.
by rewrite groupV.
Qed.

Definition reduced :=
  [qualify w : word |
   all (fun n => [forall l : n.-tuple 'I, 's_[l] != 's_[w]]) (iota 0 (size w))].
Lemma reducedP w :
  reflect (forall w' : word, 's_[w'] = 's_[w] -> size w' >= size w)
          (w \is reduced).
Proof.
apply (iffP allP) => [H w' /eqP | Hmin l].
- apply contraLR; rewrite -ltnNge => ltsz.
  have:= H (size w').
  by rewrite mem_iota /= add0n => /(_ ltsz)/forallP/(_ (in_tuple w')) /=.
- rewrite mem_iota /= add0n => ltsz; apply/forallP => /= t.
  apply/contraL : ltsz => /eqP/Hmin.
  by rewrite -leqNgt size_tuple.
Qed.

Lemma reduced_tword_inj (i j : nat) s :
  s \is reduced -> i < j < size s -> tword (take i.+1 s) != tword (take j.+1 s).
Proof.
move=> /reducedP sred /andP[ltij ltjs]; apply/negP => /eqP Heq.
have leij := ltnW ltij. have lejs := ltnW ltjs.
have:= erefl 's_[s]; rewrite -{1}(mul1g 's_[s]) -{1}(reflsK (tword_refl ltjs)).
rewrite -{1}Heq {Heq} -mulgA Eq1_11 // big_cat /= mulgA.
rewrite -(take_take ltij) Eq1_11 ?size_takel // -big_cat => {}/sred.
rewrite !size_cat !size_drop (take_take leij) !size_takel ?(leq_trans leij) //.
case: (size s) ltjs {leij lejs} => // sz; rewrite subSS ltnS.
case: j ltij => // j; rewrite ltnS subSS => /subnKC ->{i}.
case: sz => // sz; rewrite ltnS subSS => /subnKC ->{j}.
by rewrite ltnNge leqnSn.
Qed.
Lemma reduced_tword_uniq s :
  s \is reduced -> uniq [seq tword (take i.+1 s) | i <- iota 0 (size s)].
Proof.
move/reduced_tword_inj => Hinj.
apply/(uniqPn 1) => [][i][j][ltij].
rewrite size_map size_iota => ltjs.
have ltis := (ltn_trans ltij ltjs).
rewrite !(nth_map 1%N) ?size_iota // !nth_iota // !add0n => Heq.
have /Hinj : i < j < size s by rewrite ltij ltjs.
by rewrite Heq eqxx.
Qed.
Lemma length_subproof w :
  exists n : nat, [exists t : n.-tuple 'I, (w \in W) ==> ('s_[t] == w)].
Proof.
case: (boolP (w \in W)) => [/memcoxP [s <-] | _]; first last.
  by exists 0; apply/existsP; exists (in_tuple [::]).
by exists (size s); apply/existsP; exists (in_tuple s) => /=.
Qed.
Definition length w := ex_minn (length_subproof w).

Lemma length_out w : w \notin W -> length w = 0.
Proof.
rewrite /length => Hw; case: ex_minnP => l /existsP [/= t].
rewrite (negbTE Hw) /= => _ H.
apply anti_leq; rewrite leq0n andbT; apply H.
by apply/existsP; exists (in_tuple [::]).
Qed.
Lemma lengthP w : w \in W -> exists2 s, 's[W]_[s] = w & length w = size s.
Proof.
rewrite /length => Hw; case: ex_minnP => l /existsP [/= t].
by rewrite Hw /= => /eqP <- _; exists t => //; rewrite size_tuple.
Qed.

Lemma lengthw s : length 's_[s] <= size s.
Proof.
rewrite /length; case: ex_minnP => l _ /(_ (size s)); apply.
apply/existsP; exists (in_tuple s) => /=.
by rewrite memcoxw eqxx.
Qed.
Lemma length1 : length 1 = 0.
Proof.
rewrite -(coxnil W); apply/eqP.
by rewrite -leqn0 (leq_trans (lengthw [::])).
Qed.
Lemma length0P w : w \in W -> length w = 0 -> w = 1.
Proof.
move/lengthP => [s <- Hlen].
by rewrite Hlen => /eqP/nilP->; rewrite big_nil.
Qed.

Lemma reduced_lengthE s : (s \is reduced) = (size s == length 's_[s]).
Proof.
apply/reducedP/eqP => [Hred | -> s' <-]; last exact: lengthw.
apply anti_leq; rewrite lengthw ?memcoxw // andbT.
by case: (lengthP (memcoxw s)) => t /Hred les ->.
Qed.
Lemma reduced_length s : s \is reduced -> size s = length 's_[s].
Proof. by rewrite reduced_lengthE => /eqP. Qed.

Lemma oddcox_subproof : satisfy (coxrels_of_mat 'M[W]) (fun => true).
Proof.
apply/satisfyP=> /= [[l r] /allpairsP[[i j] /= [_ _]]].
rewrite /coxrel; case: 'M_(_) => [n|] [->{l} ->{r}]; rewrite big_nil //.
rewrite big_flatten /= big_seq big1 //= => s.
rewrite mem_nseq => /andP[_ /eqP->].
by rewrite big_cons big_seq1.
Qed.
Definition oddcox : {morphism W >-> boolGroup} :=
  let: exist m _ := presm_spec (coxpresP W) oddcox_subproof in m.
Lemma oddcoxs i : oddcox 's_i = true.
Proof. by rewrite /oddcox; case: presm_spec. Qed.
Lemma oddcox_lenght w : w \in W -> oddcox w = odd (length w).
Proof.
move/lengthP => [s <- ->{w}].
rewrite morph_prod => [|i _]; last exact: memcoxs.
under eq_bigr do rewrite oddcoxs.
elim: s => [|s0 s IHs]; first by rewrite big_nil.
by rewrite big_cons {}IHs.
Qed.

Lemma lengths i : length 's_i = 1%N.
Proof.
rewrite -coxw1; apply anti_leq; have /= -> /= := lengthw [:: i].
rewrite lt0n; apply/negP => /eqP Heq.
have := erefl (oddcox 's_[[:: i]]).
by rewrite {1}oddcox_lenght ?memcoxw // Heq big_seq1 oddcoxs.
Qed.
Lemma lengthV w : length w^-1 = length w.
Proof.
case: (boolP (w \in W)) => win; last by rewrite !length_out // groupV.
suff {w win}lenle w' : w' \in W -> length w'^-1 <= length w'.
  by apply anti_leq; rewrite lenle //= -{1}(invgK w) lenle // groupV.
move: w' => w /lengthP [s <-{w} ->]; rewrite -coxwrev.
by rewrite -size_rev lengthw.
Qed.
Lemma lenghtM_leq v w : v \in W -> length (v * w) <= length v + length w.
Proof.
move=> vin; case: (boolP (w \in W)) => win; first last.
  by rewrite (length_out win) length_out // groupMl.
move/lengthP: vin => [s <- ->{v}].
move/lengthP: win => [t <- ->{w}].
by rewrite -big_cat /= -size_cat lengthw.
Qed.
Lemma lenghtM_geq v w :
  v * w \in W -> length v - length w <= length (v * w).
Proof.
move=> vin.
case: (leqP (length w) (length v)) => [lelen|/ltnW]; first last.
  by rewrite -subn_eq0 => /eqP ->.
rewrite -(leq_add2r (length w)) subnK //.
by rewrite -{1}(mulgK w v) -(lengthV w) lenghtM_leq.
Qed.
Lemma lenghtMC_geq v w :
  w * v \in W -> length v - length w <= length (w * v).
Proof.
move=> H; rewrite -(lengthV v) -(lengthV w) -(lengthV (w * v)) invMg.
by apply lenghtM_geq; rewrite -invMg groupV.
Qed.

Lemma length_coxsg i w :
  w \in W ->
  length ('s_i * w) = (length w).+1 \/ length ('s_i * w) = (length w).-1.
Proof.
move=> win.
case: (ltngtP (length ('s_i * w)) (length w)) => Hlen; first last.
  exfalso; have:= morphM oddcox (memcoxs i) win.
  by rewrite oddcoxs !oddcox_lenght ?groupM // Hlen; case: odd.
- left; apply anti_leq; rewrite Hlen andbT.
  by rewrite -add1n -(lengths i) lenghtM_leq // memcoxs.
- right; apply anti_leq.
  case Hlenw : (length w) Hlen => [|lw]//= /ltnSE -> /=.
  rewrite -ltnS -{}Hlenw -addn1 addnC -leq_subLR -(lengths i).
  exact/lenghtMC_geq/groupM.
Qed.

Structure coxrefl : predArgType :=
  CoxRefl { coxreflval :> gT; _ : coxreflval \in reflexions}.
Canonical coxrefl_subType := Eval hnf in [subType for coxreflval].
Definition coxrefl_eqMixin := Eval hnf in [eqMixin of coxrefl by <:].
Canonical coxrefl_eqType := EqType coxrefl coxrefl_eqMixin.
Definition coxrefl_choiceMixin := Eval hnf in [choiceMixin of coxrefl by <:].
Canonical coxrefl_choiceType := ChoiceType coxrefl coxrefl_choiceMixin.
Definition coxrefl_countMixin := Eval hnf in [countMixin of coxrefl by <:].
Canonical coxrefl_countType := CountType coxrefl coxrefl_countMixin.
Canonical coxrefl_subCountType := Eval hnf in [subCountType of coxrefl].
Definition coxrefl_finMixin := Eval hnf in [finMixin of coxrefl by <:].
Canonical coxrefl_finType := FinType coxrefl coxrefl_finMixin.
Canonical coxrefl_subFinType := Eval hnf in [subFinType of coxrefl].

Lemma coxreflP (t : coxrefl) : coxreflval t \in reflexions.
Proof. by case: t. Qed.

Definition coxrefli i := CoxRefl (coxs_refls i).
Definition coxreflJs (t : coxrefl) i :=
  CoxRefl (conjs_refls i (coxreflP t)).
Definition coxreflJw (t : coxrefl) (s : seq 'I) :=
  CoxRefl (conj_refls (memcoxw s) (coxreflP t)).

Lemma coxrefliE i : val (coxrefli i) = 's_i.
Proof. by []. Qed.
Lemma coxreflJsE t i : val (coxreflJs t i) = t ^ 's_i.
Proof. by []. Qed.
Lemma coxreflJwE t s : val (coxreflJw t s) = t ^ 's_[s].
Proof. by []. Qed.

Lemma reflb_eqE (p1 p2 : coxrefl * bool) :
  (p1 == p2) = (val p1.1 == val p2.1) && (p1.2 == p2.2).
Proof. by case: p1 p2 => [t1 e1] [t2 e2]; rewrite xpair_eqE -val_eqE. Qed.

Definition actreflb i :=
  [fun p : coxrefl * bool => (coxreflJs p.1 i, p.2 * ('s_i == val p.1))].

Lemma actreflbK i : involutive (actreflb i).
Proof.
move=> /= [t e] /=; congr (_, _).
  by apply val_inj; rewrite /= -conjgM mulss conjg1.
rewrite eq_conjg coxsV conjgg -mulgA.
by case: eqP => _; rewrite mulg1.
Qed.
Definition permreflb i : {perm coxrefl * bool} := perm (can_inj (actreflbK i)).

Lemma permreflbK i : permreflb i ^+ 2 = 1.
Proof. by apply/permP => p; rewrite !permE /= !permE actreflbK. Qed.

Local Notation ntw s t :=
  (count_mem t [seq tword (take i.+1 s) | i <- iota 0 (size s)]).
Lemma permreflbsE s (t : coxrefl) (e : bool) :
  (\prod_(i <- s) permreflb i) (t, e) = (coxreflJw t s, e * odd (ntw s (val t))).
Proof.
apply/eqP; rewrite reflb_eqE; elim/last_ind: s => /= [|s sn IHs].
  by rewrite !big_nil perm1 conjg1 /= mulg1 !eqxx.
rewrite -cats1 !big_cat /= !big_seq1.
rewrite permM ![permreflb sn _]permE /=.
move: IHs => /andP [/eqP-> /eqP->].
rewrite -conjgM -mulgA eqxx /=; apply/eqP; congr (_ * _).
(** This is the recursion of Eq (1.15). *)
have takes n : n < size s -> take n.+1 (rcons s sn) = take n.+1 s.
  by move=> Hn; rewrite -cats1 takel_cat.
rewrite cats1 size_rcons -{1}addn1 iotaD add0n map_cat count_cat.
rewrite oddD /= addn0 oddb; congr (odd (count_mem (val t) _) * _).
  apply eq_in_map => i; rewrite mem_iota /= add0n => ltis.
  by rewrite takes.
rewrite -(size_rcons s sn) take_size /tword rev_rcons /=.
rewrite -cats1 !big_cat big_seq1 /= coxwrev.
by rewrite eq_conjg conjgE invgK mulgA.
Qed.

(** TODO: Is this still useful ?
Lemma Eq_1_15 i0 s (t : gT) :
  odd (n s t) =
  \prod_(0 <= i < (size s)) ('s_(nth i0 s i) == t ^ 's_[take i.+1 s]).
Proof.
elim/last_ind: s t => [|s sn IHs] t; first by rewrite /= big_nil.
have takes i : i < size s -> take i.+1 (rcons s sn) = take i.+1 s.
  by move=> Hi; rewrite -cats1 takel_cat.
have nths i : i < size s -> nth i0 (rcons s sn) i = nth i0 s i.
  by move=> Hi; rewrite -cats1 nth_cat Hi.
rewrite size_rcons -{1}addn1 iotaD add0n map_cat count_cat oddD /= addn0 oddb.
rewrite big_nat_recr /= //; congr (_ * _).
  rewrite big_nat; under eq_bigr do rewrite takes // nths //.
  rewrite -big_nat -IHs //; congr (odd (count_mem t _)).
  apply eq_in_map => i; rewrite mem_iota /= add0n => ltis.
  by rewrite takes.
rewrite -(size_rcons s sn) take_size nth_rcons ltnn eqxx /tword rev_rcons /=.
rewrite -[LHS](inj_eq (conjg_inj 's_[rcons s sn])); congr (_ == _).
rewrite conjgE big_cat /= -!mulgA mulKg.
by rewrite -cats1 big_cat big_seq1 /= coxwrev mulKg.
Qed.
*)

Lemma permreflb_coxrel : satisfy (coxrels_of_mat 'M) permreflb.
Proof.
apply/satisfyP=> /= [[l r] /allpairsP[[i j] /= [_ _]]].
rewrite /coxrel; case Hm: 'M_(_) => [m|] [->{l} ->{r}]; rewrite big_nil //.
apply/permP => [][t e]; rewrite perm1 permreflbsE.
apply/eqP; rewrite reflb_eqE => /=.
move/coxrelP in Hm; rewrite cox_flattennseq Hm conjg1 eqxx /=.
rewrite -{2}(mulg1 e); apply/eqP; congr (e * _); rewrite size_flatten.
have -> : shape (nseq m [:: i; j]) = nseq m 2 by elim: m {Hm} => //= m ->.
rewrite sumn_nseq mul2n.
transitivity (odd (count_mem (val t)
    [seq 's_[rcons (flatten (nseq k [:: i; j])) i] | k <- iota 0 m.*2])).
  congr (odd (count_mem _ _)); apply eq_in_map => k {Hm}.
  rewrite mem_iota /= add0n => ltk; rewrite /tword; congr 's_[_].
  move: ltk; rewrite -(odd_double_half k).
  have comalt l : i :: rev (flatten (nseq l [:: i; j])) =
         rcons (flatten (nseq l [:: i; j])) i.
    by elim: l => // l; rewrite -{1}addn1 nseqD flatten_cat rev_cat /= => ->.
  case: (odd k) (k./2) => [|] {}k; rewrite ?add0n ?add1n.
  - rewrite -doubleS leq_double => ltkm.
    rewrite [take _ _](_ : _ = flatten (nseq k.+1 [:: i; j])); first last.
      elim: k m ltkm => [|k IHk] /= [|m /ltnSE] //; first by rewrite /= take0.
      by move=> {}/IHk; rewrite /= -doubleS => ->.
    rewrite {ltkm} -addnn -addSn nseqD flatten_cat rcons_cat; congr (_ ++ _).
    by rewrite -addn1 nseqD /= flatten_cat rev_cat /= comalt.
  - rewrite ltn_double; case: m => // m /ltnSE lekm.
    rewrite [take _ _](_ : _ = rcons (flatten (nseq k [:: i; j])) i); first last.
      by elim: k m lekm => [|k IHk] /= [|m]// /ltnSE /IHk ->.
    rewrite {lekm} rev_rcons /= -cats1 -catA -addnn.
    rewrite nseqD flatten_cat rcons_cat; congr (_ ++ _).
    by rewrite cat1s comalt.
rewrite -addnn iotaD map_cat add0n count_cat oddD.
set X := (X in count_mem _ X); set Y := (Y in _ (+) odd (count_mem _ Y)).
suff -> : X = Y by case: odd.
rewrite {}/X {}/Y -{2}(addn0 m) iotaDl -map_comp; apply eq_map => k /=.
by rewrite nseqD flatten_cat rcons_cat big_cat cox_flattennseq /= Hm mul1g.
Qed.
Definition permreflbm : {morphism W >-> {perm coxrefl * bool}} :=
  let: exist m _ := presm_spec (coxpresP W) permreflb_coxrel in m.
Lemma permreflbmE i : permreflbm 's_i = permreflb i.
Proof. by rewrite /permreflbm;  case: presm_spec. Qed.
(** This is Eq 1.16 *)
Lemma permreflbsmE s (t : coxrefl) (e : bool) :
  permreflbm 's_[s] (t, e) = (coxreflJw t s, e * odd (ntw s (val t))).
Proof.
rewrite morph_prod => [|i _]; last exact: memcoxs.
under eq_bigr do rewrite permreflbmE.
exact: permreflbsE.
Qed.

Lemma permreflbm_inj : 'injm permreflbm.
Proof.
apply/subsetP => w; rewrite !inE => /andP[win]; apply contraLR => Hw.
move: win Hw => /lengthP [s <-{w}] /esym/eqP.
rewrite -reduced_lengthE => sred ntw1.
have {ntw1} : size s != 0 by apply/contra: ntw1 => /nilP ->; rewrite big_nil.
rewrite -lt0n => lt0s.
have Ht1 : tword (take 1 s) \in reflexions.
  case: s lt0s {sred} => // s0 s _ /=.
  by rewrite take0 /tword /= big_seq1 coxs_refls.
apply/negP => /eqP/permP/(_ (CoxRefl Ht1, false)).
rewrite perm1 permreflbsmE.
suff -> : ntw s (tword (take 1 s)) = 1%N by [].
rewrite (count_uniq_mem _ (reduced_tword_uniq sred)).
by apply/eqP; rewrite eqb1; apply: map_f; rewrite mem_iota /= add0n.
Qed.

Lemma permreflbm_coxrefl (t : coxrefl) e : permreflbm t (t, e) = (t, ~~ e).
Proof.
have /imset2P [i w _ /(memcoxP W) [s <-{w} eqt]]:= coxreflP t.
rewrite eqt.
elim/last_ind: s t e eqt => [|s sn IHs] t e.
  move=> eqt; apply/eqP; rewrite reflb_eqE /=; move: eqt.
  rewrite big_nil conjg1 permreflbmE permE /= => ->.
  by rewrite conjgE mulKg eqxx /= -addbT.
rewrite -cats1 big_cat /= conjgM conjgE big_seq1 coxsV mulgA => eqt.
rewrite -mulgA morphM ?(groupM, groupV) // ?memcoxs ?memcoxw //.
rewrite permreflbmE !permM permE /=.
rewrite morphM ?(groupM, groupV) // ?memcoxs ?memcoxw //.
rewrite permreflbmE !permM /= {}IHs; first last.
  by rewrite coxreflJsE eqt conjgE coxsV mulsK mulKs.
rewrite permE /=.
apply/eqP; rewrite reflb_eqE /= -conjgM mulss conjg1 eqxx /=.
rewrite eq_conjg coxsV conjgg -addNb -mulgA.
by case: ('s_sn == _); rewrite mulg1.
Qed.

Lemma strong_exchange s t :
  t \in reflexions -> length (t * 's_[s]) < length 's_[s] ->
  exists2 i, i < size s & t * 's_[s] = 's_[take i s ++ drop i.+1 s].
Proof.
Admitted.

End Reflections.
