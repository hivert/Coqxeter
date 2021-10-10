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
From mathcomp Require Import tuple bigop fingroup perm morphism alt gproduct.
Require Import present.


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope group_scope.

Local Reserved Notation "''s_' i" (at level 2, format "''s_' i").
Local Reserved Notation "''s_' [ w ] "
      (at level 2, w at level 100, format "''s_' [ w ]").
Local Reserved Notation "''M_' p" (at level 2, format "''M_' p").

Definition biggseq := (big_cons, big_nil, mulg1, mulgA).

Section GroupCompl.

Variables (gT : finGroupType) (W : {group gT}).

Lemma conjgg (x : gT) : x ^ x = x.
Proof. by rewrite conjgE mulKg. Qed.

Lemma eq_conjg (x y z : gT) : (x == y ^ z) = (x ^ (z ^-1) == y).
Proof. by rewrite -(inj_eq (conjg_inj z ^-1)) -conjgM mulgV conjg1. Qed.

End GroupCompl.


(** ** Alternating sequences *)
Section AltSeq.

Variable (T : Type).
Implicit Type (x y : T).

Fixpoint altseq x y n := if n is n'.+1 then x :: altseq y x n' else [::].

Lemma size_altseq x y n : size (altseq x y n) = n.
Proof. by elim: n x y => //= n IHn x y; rewrite IHn. Qed.

Lemma altseqSl x y n : altseq x y n.+1 = x :: altseq y x n.
Proof. by []. Qed.
Lemma altseqSr x y n :
  altseq x y n.+1 =
  if odd n then rcons (altseq x y n) y else rcons (altseq x y n) x.
Proof.
elim: n x y => [|n IHn] x y //=.
by rewrite -fun_if if_neg -IHn.
Qed.

Lemma rev_altseq x y n :
  rev (altseq x y n) = if odd n then altseq x y n else altseq y x n.
Proof.
elim: n x y => [|n IHn] x y //.
rewrite {1}altseqSr [rev _]fun_if !rev_rcons !IHn /=.
by case: (odd n) => /=.
Qed.

Lemma take_altseq x y m n :
  m <= n -> take m (altseq x y n) = altseq x y m.
Proof.
elim: m n x y => [| m IHm] [|n] x y lemn //=.
by rewrite IHm.
Qed.
Lemma drop_altseq x y m n :
  drop m (altseq x y n) =
  if odd m then altseq y x (n - m) else altseq x y (n - m).
Proof.
elim: m n x y => [| m IHm] [|n] x y //=; first by rewrite if_same.
by rewrite subSS {}IHm if_neg.
Qed.

End AltSeq.

Lemma map_altseq (T1 T2 : Type) (f : T1 -> T2) x y n :
  map f (altseq x y n) = altseq (f x) (f y) n.
Proof. by elim: n x y => [|n IHn] x y //=; rewrite IHn. Qed.


(** * Coxeter matrices *)
Section CoxeterMatrix.
Context {I : finType}.

Definition Coxeter_matrix :=
  [qualify a M : I * I -> nat | [&&
    [forall i : I, forall j : I, (i == j) == (M (i, j) == 1%N)] &
    [forall i : I, forall j : I, M (i, j) == M (j, i)] ]].
Definition coxrels_of_mat (M : I * I -> nat) : seq (seq I * seq I) :=
  [seq (altseq i j (M (i, j)).*2, [::]) | i <- enum I, j <- enum I].

Section Defs.
Variable (M : I * I -> nat).

Lemma Coxeter_matrixP :
  reflect ((forall i j : I, (i == j) = (M (i, j) == 1%N)) /\
           (forall i j : I, M (i, j) = M (j, i)))
          (M \is a Coxeter_matrix).
Proof.
apply (iffP andP) => [[] | [H1 H2]].
- move=> /forallP H1 /forallP H2; split => i j.
  + by have := H1 i => /forallP/(_ j)/eqP.
  + by have := H2 i => /forallP/(_ j)/eqP.
- by split; apply/forallP => i; apply/forallP => j //; apply/eqP.
Qed.

Hypothesis (iscox : M \is a Coxeter_matrix).

Lemma coxmdiagE i j : (i == j) = (M (i, j) == 1%N).
Proof. by move/Coxeter_matrixP : iscox => []. Qed.
Lemma coxmdiag i : M (i, i) = 1%N.
Proof. by have := coxmdiagE i i; rewrite eqxx => /esym/eqP. Qed.
Lemma coxmsym i j : M (i, j) = M (j, i).
Proof. by move/Coxeter_matrixP : iscox => []. Qed.

End Defs.

Variables (gT : finGroupType) (gen : I -> gT).

Local Notation "''s_' i" := (gen i).
Local Notation "''s_' [ w ] " := (\prod_(i <- w) 's_i).

Lemma cox_altseq_double i j n :
  's_[altseq i j n.*2] = ('s_i * 's_j) ^+ n.
Proof.
elim: n => [| n IHn] /=; first by rewrite expg0 big_nil.
by rewrite expgS !biggseq -{}IHn.
Qed.
Lemma cox_altseq_odd i j n :
  odd n -> 's_[altseq i j n] = ('s_i * 's_j) ^+ n./2 * 's_i.
Proof.
rewrite -{2}(odd_double_half n) => ->.
rewrite add1n altseqSr odd_double -cats1 big_cat /=.
by rewrite cox_altseq_double big_seq1.
Qed.

Variable (M : I * I -> nat).
Hypothesis (iscox : M \is a Coxeter_matrix).

Lemma sat_coxmatP :
  reflect (forall i j, ('s_i * 's_j) ^+ M (i, j) = 1)
          (satisfy (coxrels_of_mat M) gen).
Proof.
apply (iffP (satisfyP _ _)) => /=[sat i j | rel [r1 r2]].
- have:= sat (altseq i j (M (i, j)).*2, [::]).
  rewrite cox_altseq_double big_nil /=; apply.
  apply/allpairsP; exists (i, j) => /=.
  by split; [exact: mem_enum|exact: mem_enum|].
- move/allpairsP => [[i1 i2] [_ _[->{r1}->{r2}]]]/=.
  by rewrite cox_altseq_double big_nil.
Qed.

Hypothesis (sat : satisfy (coxrels_of_mat M) gen).

Lemma coxmat_rel i j : ('s_i * 's_j) ^+ M (i, j) = 1.
Proof. by move/sat_coxmatP: sat => ->. Qed.
Lemma coxmat_mulss i : 's_i * 's_i = 1.
Proof. by move/sat_coxmatP: sat => /(_ i i); rewrite coxmdiag. Qed.
Lemma coxmat_sV i : 's_i ^-1 = 's_i.
Proof. by rewrite -[LHS](mul1g) -(coxmat_mulss i) mulgK. Qed.
Lemma coxmat_mulKs i : cancel (mulg 's_i) (mulg 's_i).
Proof. by move=> x; rewrite mulgA coxmat_mulss mul1g. Qed.
Lemma coxmat_mulsK i : cancel (mulg^~ 's_i) (mulg^~ 's_i).
Proof. by move=> x; rewrite -mulgA coxmat_mulss mulg1. Qed.

Lemma coxmat_sC i j : M (i, j) = 2 -> commute 's_i 's_j.
Proof.
have := coxmat_rel i j => /[swap] ->.
rewrite /commute => /(congr1 (mulg ('s_ j * 's_ i))).
by rewrite mulg1 !mulgA coxmat_mulsK coxmat_mulss mul1g.
Qed.

End CoxeterMatrix.


Section Defs.

Variables (gT : finGroupType).

Record Coxeter_system (W : {group gT}) := CoxSys {
  coxind : finType;
  coxgen : coxind -> gT;
  coxmat : coxind * coxind -> nat;
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

Notation "''I[' g ]" := (@coxind _ _ (coxsys g)) (format "''I[' g ]").
Notation "''S[' g ]" := (@coxgen _ _ (coxsys g)) (format "''S[' g ]").
Notation "''s[' g ']_' i" := ('S[g] i) (at level 2).
Notation "''M[' g ']'" := (@coxmat _ _ (coxsys g))
                            (format "''M[' g ]", at level 2).
Notation "''M[' g ']_' p" := ('M[g] p) (at level 2).
Notation "''s[' g ']_' [ w ] " := (\prod_(i <- w) 's[g]_i) (at level 2).
Notation "''s_' i" := ('s[_]_i).
Notation "''s_' [ w ] " := (\prod_(i <- w) 's_i).
Notation "''M_' p" := ('M[_]_p).


Section Basic.

Variables (gT : finGroupType) (W : {coxgrp gT}).
Local Notation "''I'" := 'I[W].
Implicit Types (i : 'I) (s : seq 'I).


Definition rank := #|[set: 'I]|.
Definition coxirred := n_comp (fun i j => 'M[W]_(i, j) >= 3)%O predT == 1%N.

Lemma coxmatP : 'M[W] \is a Coxeter_matrix.
Proof. by case: W => [G []]. Qed.
Lemma coxpresP : ('S[W], coxrels_of_mat 'M[W]) \present (W : {group _}).
Proof. by case: W => [G []]. Qed.
Lemma coxsat : satisfy (coxrels_of_mat 'M[W]) 'S[W].
Proof. exact: present_sat coxpresP. Qed.
Hint Resolve coxsat : core.
Hint Resolve coxmatP : core.

Lemma coxnil : 's[W]_[[::]] = 1.
Proof. by rewrite big_nil. Qed.
Lemma coxw1 i : 's_[[:: i]] = 's_i.
Proof. by rewrite big_seq1. Qed.

Lemma memcoxs i : 's_i \in W.
Proof. by rewrite (present_gen coxpresP) mem_gen // imset_f. Qed.
Lemma memcoxw s : 's_[s] \in W.
Proof. by apply group_prod => i _; apply memcoxs. Qed.

Lemma memcoxwP w : w \in W -> {s | 's[W]_[s] = w}.
Proof. exact/(present_seqP coxpresP). Qed.
Lemma memcoxP w : reflect (exists s, 's_[s] = w) (w \in W).
Proof.
by apply (iffP idP) => [/memcoxwP|] [] s <-{w}; [exists s | exact: memcoxw].
Qed.

Lemma coxrelP i j :  ('s_i * 's_j) ^+ 'M_(i, j) = 1.
Proof. exact: coxmat_rel. Qed.
Lemma mulss i : 's_i * 's_i = 1.
Proof. exact: (coxmat_mulss coxmatP). Qed.
Lemma coxsV i : 's_i ^-1 = 's_i.
Proof. exact: (coxmat_sV coxmatP). Qed.
Lemma mulKs i : cancel (mulg 's_i) (mulg 's_i).
Proof. exact: (coxmat_mulKs coxmatP). Qed.
Lemma mulsK i : cancel (mulg^~ 's_i) (mulg^~ 's_i).
Proof. exact: (coxmat_mulsK coxmatP). Qed.
Lemma coxsC i j : 'M_(i, j) = 2 -> commute 's_i 's_j.
Proof. exact: (coxmat_sC coxmatP). Qed.

Lemma coxwrev s : 's_[rev s] = 's_[s] ^-1.
Proof.
elim: s => [|s0 s IHs]; first by rewrite !big_nil invg1.
by rewrite rev_cons -cats1 big_cat big_seq1 !big_cons /= {}IHs invMg coxsV.
Qed.

End Basic.
#[export] Hint Resolve coxsat coxmatP : core.
#[export] Hint Resolve memcoxs memcoxw : core.


Section Reflections.

Variables (gT : finGroupType) (W : {coxgrp gT}).
Local Notation I := 'I[W].
Local Notation word := (seq I).
Implicit Types (i : I) (s : word).

Definition reflexions := [set 's_i ^ w | i in I, w in W].

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
Lemma reflsV t : t \in reflexions -> t ^-1 = t.
Proof. by move=> /reflsK t2; apply (mulgI t); rewrite t2 mulgV. Qed.


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


(** * Length and reduced words *)
Fact length_subproof w :
  exists n : nat, [exists t : n.-tuple I, (w \in W) ==> ('s_[t] == w)].
Proof.
case: (boolP (w \in W)) => [/memcoxP [s <-] | _]; first last.
  by exists 0; apply/existsP; exists (in_tuple [::]).
by exists (size s); apply/existsP; exists (in_tuple s) => /=.
Qed.
Definition length w := ex_minn (length_subproof w).
Definition reduced := [qualify w : word | size w == length 's_[w]].

Lemma length_out w : w \notin W -> length w = 0.
Proof.
rewrite /length => Hw; case: ex_minnP => l /existsP [/= t].
rewrite (negbTE Hw) /= => _ H.
apply anti_leq; rewrite leq0n andbT; apply H.
by apply/existsP; exists (in_tuple [::]).
Qed.
Lemma length_size w s : 's_[s] = w -> length w <= size s.
Proof.
rewrite /length; case: ex_minnP => m _ + eqs; apply.
by apply/existsP; exists (in_tuple s); rewrite /= eqs eqxx implybT.
Qed.
Lemma lengthw s : length 's_[s] <= size s.
Proof. exact: length_size. Qed.

Lemma length1 : length 1 = 0.
Proof.
rewrite -(coxnil W); apply/eqP.
by rewrite -leqn0 (leq_trans (lengthw [::])).
Qed.

Lemma reducedE s : (s \is reduced) = (size s == length 's_[s]).
Proof. by []. Qed.
Fact redword_subproof w : {s | w \in W -> 's[W]_[s] = w & size s = length w}.
Proof.
suff : {s : (length w).-tuple I | (w \in W) ==> ('s[W]_[s] == w)}.
  by move=> [[s/= /eqP szs H]]; exists s; first by move/(implyP H)/eqP.
apply sigW; rewrite /length => /=; case: ex_minnP => l /existsP[/= t].
by move=> heq _; exists t.
Qed.
Definition redword w := let: exist2 s _ _ := redword_subproof w in s.
Lemma redwordE w : w \in W -> 's_[redword w] = w.
Proof. by rewrite /redword; case: redword_subproof. Qed.
Lemma size_redword w : size (redword w) = length w.
Proof. by rewrite /redword; case: redword_subproof. Qed.
Lemma redwordP w : redword w \is reduced.
Proof.
rewrite reducedE /redword; case: redword_subproof => s Hs.
case: (boolP (w \in W)) => /= [/Hs->->//| wnotin].
rewrite (length_out wnotin) => /eqP/nilP -> /=.
by rewrite big_nil length1.
Qed.
Lemma lengthP w : w \in W -> exists2 s, 's[W]_[s] = w & length w = size s.
Proof.
move=> win; exists (redword w); first exact: redwordE.
by rewrite size_redword.
Qed.
Lemma length0P w : w \in W -> length w = 0 -> w = 1.
Proof. by move/lengthP => [s <- ->] /eqP/nilP ->; rewrite big_nil. Qed.
Lemma reduced_length s : s \is reduced -> size s = length 's_[s].
Proof. by rewrite reducedE => /eqP. Qed.

Lemma reducedP w :
  reflect (forall w' : word, 's_[w'] = 's_[w] -> size w' >= size w)
          (w \is reduced).
Proof.
rewrite unfold_in; apply (iffP eqP) => [-> w'| le]; first exact: length_size.
apply/anti_leq; rewrite lengthw andbT.
by rewrite -size_redword le // redwordE // memcoxw.
Qed.
Lemma reduced_nil : [::] \is reduced.
Proof. exact/reducedP. Qed.

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


Lemma reduced_tword_neq (i j : nat) s :
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
Lemma reduced_tword_inj s :
  s \is reduced ->
  {in gtn (size s) &, injective (fun i : nat => tword (take i.+1 s)) }.
Proof.
move/reduced_tword_neq => H i j; rewrite !unfold_in /= => ltis ltjs eqtw.
case: (ltngtP i j) => // cmpij; exfalso.
- by have := H i j; rewrite eqtw eqxx cmpij ltjs /= => /(_ is_true_true).
- by have := H j i; rewrite eqtw eqxx cmpij ltis /= => /(_ is_true_true).
Qed.
Lemma reduced_tword_uniq s :
  s \is reduced -> uniq [seq tword (take i.+1 s) | i <- iota 0 (size s)].
Proof.
move/reduced_tword_inj => H.
apply/(uniqPn 1) => [][i][j][ltij].
rewrite size_map size_iota => ltjs.
have ltis := (ltn_trans ltij ltjs).
rewrite !(nth_map 1%N) ?size_iota // !nth_iota // !add0n => /H.
by move/(_ ltis)/(_ ltjs) => Heq; rewrite Heq ltnn in ltij.
Qed.


Lemma oddcox_subproof : satisfy (coxrels_of_mat 'M[W]) (fun => true).
Proof.
apply/satisfyP=> /= [[l r] /allpairsP[[i j] /= [_ _ [->{l} ->{r}]]]].
by rewrite cox_altseq_double big_nil expg1n.
Qed.
Definition oddcox : {morphism W >-> boolGroup} :=
  let: exist m _ := presm_spec (coxpresP W) oddcox_subproof in m.
Lemma oddcoxs i : oddcox 's_i = true.
Proof. by rewrite /oddcox; case: presm_spec. Qed.
Lemma oddcox_lenght w : w \in W -> oddcox w = odd (length w).
Proof.
rewrite -size_redword => /redwordE {1}<-.
rewrite morph_prod => [|i _]; last exact: memcoxs.
under eq_bigr do rewrite oddcoxs.
elim: (redword w) => [|s0 s IHs]; first by rewrite big_nil.
by rewrite big_cons {}IHs.
Qed.

Lemma lengths i : length 's_i = 1%N.
Proof.
rewrite -coxw1; apply anti_leq; have /= -> /= := lengthw [:: i].
rewrite lt0n; apply/negP => /eqP Heq.
have := erefl (oddcox 's_[[:: i]]).
by rewrite {1}oddcox_lenght ?memcoxw // Heq big_seq1 oddcoxs.
Qed.
Lemma reduced1 i : [:: i] \is reduced.
Proof. by rewrite reducedE big_seq1 lengths. Qed.


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


(** * Action by permutation on signed reflexions *)
Structure coxrefl : predArgType :=
  CoxRefl { coxreflval :> gT; _ : coxreflval \in reflexions }.
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
Hint Resolve coxreflP : core.
Lemma coxreflW (t : coxrefl) : coxreflval t \in W.
Proof. exact: reflsW. Qed.
Hint Resolve coxreflW : core.

Lemma coxreflK (t : coxrefl) : t * t = 1.
Proof. by rewrite reflsK. Qed.
Lemma coxreflV (t : coxrefl) : t ^-1 = t :> gT.
Proof. by rewrite reflsV. Qed.

Definition coxrefli i := CoxRefl (coxs_refls i).
Definition coxreflJs (t : coxrefl) i :=
  CoxRefl (conjs_refls i (coxreflP t)).
Definition coxreflJw (t : coxrefl) (s : seq I) :=
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

Definition ntw s t :=
  (count_mem t [seq tword (take i.+1 s) | i <- iota 0 (size s)]).
(** This is eta of Equation 1.17 *)
Definition oddntw w (t : coxrefl) := odd (ntw (redword w) (val t)).

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
rewrite /ntw cats1 size_rcons -{1}addn1 iotaD add0n map_cat count_cat.
rewrite oddD /= addn0 oddb; congr (odd (count_mem (val t) _) * _).
  apply eq_in_map => i; rewrite mem_iota /= add0n => ltis.
  by rewrite takes.
rewrite -(size_rcons s sn) take_size /tword rev_rcons /=.
rewrite -cats1 !big_cat big_seq1 /= coxwrev.
by rewrite eq_conjg conjgE invgK mulgA.
Qed.

Lemma permreflb_coxrel : satisfy (coxrels_of_mat 'M[W]) permreflb.
Proof.
apply/satisfyP=> /= [[l r] /allpairsP[[i j] /= [_ _ [->{l} ->{r}]]]].
apply/permP => /= [][t e]; rewrite big_nil perm1 permreflbsE.
apply/eqP; rewrite reflb_eqE => /=.
rewrite cox_altseq_double coxrelP conjg1 eqxx /=.
rewrite -{2}(mulg1 e); apply/eqP; congr (e * _); rewrite /ntw size_altseq.
transitivity (odd (count_mem (val t)
    [seq 's_[altseq i j k.*2.+1] | k <- iota 0 'M_(i, j).*2])).
  congr (odd (count_mem _ _)); apply eq_in_map => k.
  rewrite mem_iota /= add0n => ltk; rewrite /tword; congr 's_[_].
  rewrite take_altseq // rev_altseq /= if_neg fun_if.
  have eqk : k = k.*2.+1 - k.+1 by rewrite subSS -addnn addnK.
  rewrite {3 4}eqk -drop_altseq -{2}(cat_take_drop k (altseq _ _ k.*2)).
  by rewrite take_altseq // -addnn leq_addl.
rewrite -addnn iotaD map_cat add0n count_cat oddD.
set X := (X in count_mem _ X); set Y := (Y in _ (+) odd (count_mem _ Y)).
suff -> : X = Y by case: odd.
rewrite {}/X {}/Y -{2}(addn0 'M_(i, j)) iotaDl -map_comp; apply eq_map => k /=.
rewrite -!altseqSl !altseqSr !odd_double -!cats1 !big_cat /=; congr (_ * _).
rewrite doubleD -(cat_take_drop 'M_(i, j).*2 (altseq i j (_ + _))).
rewrite take_altseq ?leq_addr // drop_altseq odd_double addKn big_cat /=.
by rewrite !cox_altseq_double coxrelP mul1g.
Qed.
Definition permreflbm : {morphism W >-> {perm coxrefl * bool}} :=
  let: exist m _ := presm_spec (coxpresP W) permreflb_coxrel in m.
Lemma permreflbmE i : permreflbm 's_i = permreflb i.
Proof. by rewrite /permreflbm;  case: presm_spec. Qed.
(** This is Eq 1.16 *)
Lemma permreflbmsE s (t : coxrefl) (e : bool) :
  permreflbm 's_[s] (t, e) = (coxreflJw t s, e * odd (ntw s (val t))).
Proof.
rewrite morph_prod => [|i _]; last exact: memcoxs.
under eq_bigr do rewrite permreflbmE.
exact: permreflbsE.
Qed.
Lemma oddntwE w (t : coxrefl) s :
  's_[s] = w -> odd (ntw s (val t)) = oddntw w t.
Proof.
move=> eqw; rewrite /oddntw.
have:= permreflbmsE s t false.
have := memcoxw s; rewrite eqw => /redwordE {1}<-.
by rewrite permreflbmsE !mul1g => [] [_ -> /=].
Qed.
(** This is Eq 1.18 *)
Lemma permreflbmwE w (t : coxrefl) (e : bool) :
  w \in W ->
  permreflbm w (t, e) = (coxreflJw t (redword w), e * oddntw w t).
Proof. by move=> win; rewrite -{1}(redwordE win) permreflbmsE. Qed.


Lemma permreflbm_inj : 'injm permreflbm.
Proof.
apply/subsetP => w; rewrite !inE => /andP[win]; apply contraLR => Hw.
move: win Hw => /lengthP [s <-{w}] /esym/eqP.
rewrite -reducedE => sred ntw1.
have {ntw1} : size s != 0 by apply/contra: ntw1 => /nilP ->; rewrite big_nil.
rewrite -lt0n => lt0s.
have Ht1 : tword (take 1 s) \in reflexions.
  case: s lt0s {sred} => // s0 s _ /=.
  by rewrite take0 /tword /= big_seq1 coxs_refls.
apply/negP => /eqP/permP/(_ (CoxRefl Ht1, false)).
rewrite perm1 permreflbmsE.
suff -> : ntw s (tword (take 1 s)) = 1%N by [].
rewrite /ntw (count_uniq_mem _ (reduced_tword_uniq sred)).
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

Lemma odd_has T (s : seq T) (P : pred T) : odd (count P s) -> has P s.
Proof. by rewrite has_count; case: count. Qed.

Lemma lengthM_oddntw w (t : coxrefl) :
  w \in W -> (length (t * w) < length w) = oddntw w t.
Proof.
have impl w' t' : w' \in W -> oddntw w' t' -> (length (t' * w') < length w').
  rewrite /oddntw /ntw => win /odd_has/hasP/= [tw /mapP[/= i]].
  rewrite mem_iota add0n /= => ltis ->{tw} /eqP<-.
  rewrite -{2}(redwordE win) Eq1_11 //; apply (leq_ltn_trans (lengthw _)).
  rewrite size_cat (size_takel (ltnW ltis)) size_drop.
  move: ltis; rewrite size_redword; case: (length w') => // l /ltnSE leil.
  by rewrite ltnS subSS subnKC.
move=> win; apply/idP/idP; last exact: impl.
apply contraLR => /negPf oddtwf; rewrite -leqNgt; apply ltnW.
have tin := coxreflW t.
have twin : t * w \in W by rewrite groupM.
have tVwin : t^-1 * w \in W by rewrite groupM // groupV.
have := permreflbmwE t false tVwin.
rewrite coxreflV morphM ?groupV //.
rewrite permM permreflbm_coxrefl /=.
rewrite permreflbmwE // oddtwf mul1g mulg1 => [][_ /esym/impl]/(_ twin).
by rewrite mulgA coxreflK mul1g.
Qed.

Theorem strong_exchange_property s (t : coxrefl) :
  length (t * 's_[s]) < length 's_[s] ->
  exists2 i, i < size s & t * 's_[s] = 's_[take i s ++ drop i.+1 s].
Proof.
have sin := memcoxw s.
rewrite (lengthM_oddntw _ sin) -(oddntwE _ (erefl _)).
rewrite /ntw => /odd_has/hasP/= [tw /mapP[/= i]].
rewrite mem_iota add0n /= => ltis ->{tw} /eqP<-.
by rewrite Eq1_11 //; exists i.
Qed.

(** This is (a) <-> (c) of corollary 1.4.4 *)
Corollary refl_reduced s (t : coxrefl) :
  s \is reduced ->
  (length (t * 's_[s]) < length 's_[s]) <->
  exists2 i, i < size s & tword (take i.+1 s) = t :> gT.
Proof.
move=> sred; split => /= [|[i ltis <-{t}]].
- move/strong_exchange_property => [i ltis].
  by rewrite -Eq1_11 // => /mulIg ->; exists i.
- rewrite Eq1_11 //; apply (leq_ltn_trans (lengthw _)).
  rewrite size_cat (size_takel (ltnW ltis)) size_drop.
  rewrite -(reduced_length sred); case: (size s) ltis => // l /ltnSE leil.
  by rewrite ltnS subSS subnKC.
Qed.

Definition Tlft w := [set t : coxrefl | length (t * w) < length(w)].
Definition Trgt w := [set t : coxrefl | length (w * t) < length(w)].

Lemma TlftV w : Tlft (w ^-1) = Trgt w.
Proof.
rewrite /Tlft /Trgt; apply/setP => t; rewrite !inE lengthV.
by rewrite -(lengthV (t * w^-1)) invMg invgK coxreflV.
Qed.

Corollary cardTlft w : #|Tlft w| = length w.
Proof.
rewrite /Tlft; case: (boolP (w \in W)) => win; first last.
  rewrite length_out //; apply/eqP; rewrite cards_eq0 -subset0.
  by apply/subsetP => t; rewrite !inE.
have [s <-{w win} lens] := lengthP win; rewrite [RHS]lens.
have/esym/eqP := lens; rewrite -reducedE => reds.
pose trefl (i : 'I_(size s)) := CoxRefl (tword_refl (ltn_ord i)).
have trefl_inj : injective trefl.
  move=> i j /(congr1 val) /= => /reduced_tword_inj Heq.
  by apply/val_inj => /=; rewrite Heq // unfold_in /=.
have /= := card_imset setT trefl_inj.
rewrite [X in _ = X]cardE /= enum_setT -enumT /= size_enum_ord => <-.
congr #|pred_of_set _|; apply setP => t; rewrite !inE.
apply/idP/imsetP => [/=| [[i ltis _ /(congr1 val) /= eqt]]];
                      rewrite refl_reduced //.
- by move=> [i ltis eqt]; exists (Ordinal ltis) => //; apply val_inj.
- by exists i.
Qed.

Proposition deletion_property_take_drop s :
  length 's_[s] < size s ->
  exists (i j : nat), i < j < size s /\
  's_[s] = 's_[take i s ++ drop i.+1 (take j s) ++ drop j.+1 s].
Proof.
case Hs : s  => [//| i0 s']; rewrite -{s'}Hs => ltls.
have exnred : exists n, drop n s \isn't reduced.
  by exists 0; rewrite drop0 reducedE (gtn_eqF ltls).
have boundnred n : drop n s \isn't reduced -> n < (size s).
  apply contraR; rewrite -ltnNge => /drop_oversize ->.
  exact: reduced_nil.
have boundnredW n : drop n s \isn't reduced -> n <= (size s).
  by move/boundnred/ltnW.
case: (ex_maxnP exnred boundnredW) => b bnred bmax {boundnredW exnred}.
have ltbs := boundnred b bnred.
have {}bmax : drop b.+1 s \is reduced.
  by apply/negP => /negP/bmax; rewrite ltnn.
have:= congr1 (fun s => 's[W]_[s]) (drop_nth i0 ltbs).
rewrite big_cons => eqsdr.
case: (length_coxsg (nth i0 s b) (memcoxw (drop b.+1 s))) => [|Heq].
  rewrite -eqsdr -(reduced_length bmax) size_drop -subSn // subSS => Heq.
  by move: bnred; rewrite reducedE size_drop -{}Heq eqxx.
have {Heq} :
    length ('s_(nth i0 s b) * 's_[drop b.+1 s]) < length 's_[drop b.+1 s].
  rewrite Heq; case Hlen: (length 's_[drop b.+1 s]) => //; exfalso.
  move: bmax; rewrite reducedE Hlen => /nilP Hrd.
  by move: bnred; rewrite (drop_nth i0 ltbs) Hrd reduced1.
have sti := coxs_refls (nth i0 s b).
rewrite -['s_(nth i0 s b)]/(val (CoxRefl sti)).
move/strong_exchange_property => [j ltjs] /=.
rewrite -eqsdr drop_drop take_drop addSn => eqdr.
exists b, (j + b.+1); split.
  rewrite {1}addnS ltnS leq_addl /=.
  by move: ltjs; rewrite size_drop ltn_subRL addnC.
by rewrite -{1}(cat_take_drop b s) big_cat /= eqdr !big_cat /=.
Qed.
Proposition deletion_property_cat s :
  length 's_[s] < size s ->
  exists (A B C : seq I) (i j : I),
    s = A ++ i :: B ++ j :: C /\ 's_[s] = 's_[A ++ B ++ C].
Proof.
case Hs: s => [//| s0 s']; rewrite -{s'}Hs.
move/deletion_property_take_drop => [i][j][/andP[ltij ltjs] eqs].
exists (take i s), (drop i.+1 (take j s)), (drop j.+1 s).
exists (nth s0 s i), (nth s0 s j); split; last exact: eqs.
rewrite -drop_nth //.
have:= take_drop (j - i.+1) i.+1 s; rewrite subnK // => <-.
have:= drop_drop s (j - i.+1) i.+1; rewrite subnK // => <-.
by rewrite cat_take_drop -drop_nth ?(ltn_trans ltij ltjs) // cat_take_drop.
Qed.

(** This is proposition 1.4.8 (i) *)
Proposition ex_subreduced s :
  exists s', [/\ s' \is reduced,
              's_[s] = 's_[s'],
              subseq s' s &
              odd (size s) = odd (size s')].
Proof.
have [n ltsn] := ubnP (size s); elim: n s ltsn => // n IHn s /ltnSE ltsn.
case: (boolP (s \is reduced)) => [sred|snred]; first by exists s.
move: snred; rewrite reducedE neq_ltn ltnNge lengthw /=.
move/deletion_property_cat => [A][B][C][i][j][eqs eqss].
have /IHn [s' [s'red eqs' subs' odds']]: size (A ++ B ++ C) < n.
  apply: (leq_trans _ ltsn); rewrite eqs !size_cat /= !size_cat /=.
  by rewrite !addnS ltnS.
exists s'; split.
- exact: s'red.
- by rewrite eqss eqs'.
- apply: (subseq_trans subs'); rewrite eqs subseq_cat2l.
  apply: (subseq_trans _ (subseq_cons _ _)); rewrite subseq_cat2l.
  exact: subseq_cons.
- by rewrite -odds' eqs !size_cat /= !size_cat /= !addnS !oddS negbK.
Qed.

End Reflections.
