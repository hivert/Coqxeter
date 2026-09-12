(** * Free Groups *)
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
From HB Require Import structures.
From mathcomp Require Import boot.

Require Import ssrcompl.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope group_scope.

Reserved Notation "{ 'freeg' T }" (format "{ 'freeg'  T }").
Reserved Notation "''g_' i" (at level 2, format "''g_' i").


(** ** A Type with a fixed point free involution *)
HB.mixin Record isInvolutive T of Equality T := {
  invol : T -> T;
  involK : involutive invol;
  involN : forall t, t != invol t;
}.
#[short(type="involType")]
HB.structure Definition Involutive := {
    T of isInvolutive T & Choice T
  }.

Lemma involF (T : involType) (t : T) : (t == invol t) = false.
Proof. exact: negbTE (involN _). Qed.


(** ** Reduction of word when invol is the inversion. *)
Fixpoint fgreduce {T : involType} (s : seq T) :=
  if s is x :: s' then
    let sres := fgreduce s' in
    if x == invol (head x sres) then behead sres else x :: sres
  else [::].
Definition fgreduced {T : involType} := [qualify s : seq T | fgreduce s == s].


Section Fgreduce.

Context {T : involType}.
Implicit Type (x y z : T) (s t u v : seq T).

(** To allows for automatic resolution with done *)
Let invK := (@involK T).
Let invN := (@involN T).
Let invF := (@involF T).

Lemma fgreducedP {s} : reflect (fgreduce s = s) (s \is fgreduced).
Proof. exact/eqP. Qed.
Lemma fgreduced0 : [::] \is @fgreduced T.
Proof. exact/fgreducedP. Qed.
Lemma fgreduced1 x : [:: x] \is fgreduced.
Proof. by apply/fgreducedP; rewrite /= invF. Qed.

Lemma size_fgreduce s : size (fgreduce s) <= size s ?= iff (s \in fgreduced).
Proof.
rewrite qualifE; elim: s => [//|x0 s /= IHs].
case: (fgreduce s) IHs => [_ |x1 s'] /=.
  rewrite invF; split; first by rewrite ltnS.
  by rewrite eqSS; apply/eqP/eqP => [/esym/eqP/nilP->|[<-//]].
case: (altP (x0 =P invol x1)) => /= [->{x0}|_].
  move=> [lts _]; have lts1 := leq_trans lts (leqnSn _).
  split; first exact: ltnW.
  rewrite ltn_eqF //; apply/esym/(introF idP) => /eqP/(congr1 size)/=/eqP.
  by rewrite ltn_eqF.
move=> [lts Heq]; split; first by rewrite ltnS.
by rewrite eqSS {}Heq eqseq_cons eqxx /=.
Qed.
Lemma odd_size_fgreduce s : odd (size (fgreduce s)) = odd (size s).
Proof.
elim: s => //= x0 s.
case: (fgreduce s) => [|x1 s'] /=; first by rewrite invF /= => <-.
by case: eqP => _ <- //=; rewrite negbK.
Qed.

Lemma fgreduced_consK x s : x :: s \is fgreduced -> s \is fgreduced.
Proof.
have [ltss eqss] := size_fgreduce s.
have [_ <- /=] := size_fgreduce (x :: s).
case: (x == _) => /=; last by rewrite eqSS eqss.
by rewrite size_behead ltn_eqF // ltnS (leq_trans (leq_pred _) ltss).
Qed.
Lemma fgreduced_cons x s :
  (x :: s \is fgreduced) = (s \is fgreduced) && (x != invol (head x s)).
Proof.
apply/idP/andP => [ xsred|[]]; first last.
  by rewrite !qualifE /= => /eqP -> /negbTE ->.
split; first exact: (fgreduced_consK xsred).
have [_] := size_fgreduce (x :: s); rewrite xsred => /eqP /=.
have /fgreducedP -> := fgreduced_consK xsred.
case: eqP => // _ /eqP.
by rewrite size_behead ltn_eqF // ltnS (leq_trans (leq_pred _)).
Qed.

Lemma fgreduceP s : fgreduce s \is fgreduced.
Proof.
have [b] := ubnPleq (size s); elim: b s => [|b IHb] s.
  by rewrite leqn0 => /nilP ->.
rewrite leq_eqVlt => /orP[/eqP|/ltnSE]; last exact: IHb.
case: s => // x s /= [eqsz]; rewrite -{b}eqsz in IHb.
move/(_ _ (leqnn _)): IHb.
case: (fgreduce s) => [|x1 s'] {s} Hred; first by rewrite /= invF fgreduced1.
rewrite [head _ _]/= [behead _]/=.
case: (altP (x =P invol x1)) => [_ | Hneq]; first exact: fgreduced_consK Hred.
by rewrite fgreduced_cons Hred /=.
Qed.
Lemma fgreduce_id s : fgreduce (fgreduce s) = fgreduce s.
Proof. by have /eqP := fgreduceP s. Qed.

Lemma fgreduce_eqinv u x v :
  fgreduce (u ++ [:: x, invol x & v]) = fgreduce (u ++ v).
Proof.
elim: u => /= [|x0 u -> //].
rewrite (inj_eq (can_inj invK)).
case: (altP (x =P head _ _)) => [|_ /=]; last by rewrite invK eqxx.
case Hsv: (fgreduce v) => [|y0 sv] /=; first by move=> {1}->; rewrite eqxx.
move => ->{x}; case: sv Hsv => [|y1 sv Heq] /=; first by rewrite invF.
have := fgreduceP v; rewrite Heq fgreduced_cons => /andP [_].
by rewrite [head _ _]/= => /negbTE ->.
Qed.

Lemma fgreducedPn s :
  reflect (exists u x v, s = u ++ [:: x, invol x & v])
          (s \isn't fgreduced).
Proof.
rewrite qualifE; apply (iffP idP) => [|[u][x][v] ->{s}]; first last.
  rewrite fgreduce_eqinv; apply/negP => /eqP/(congr1 size)/eqP.
  rewrite size_cat /= !addnS -size_cat ltn_eqF // ltnS.
  exact: (leq_trans (size_fgreduce _)).
elim: s => //= x0 s IHs.
case: (altP (fgreduce s =P s)) => [{IHs} ->| {}/IHs [u][x][v]eqs _].
  case: s => [|x1 s']; first by rewrite /= invF eqxx.
  case: (altP (x0 =P invol x1)) => [->{x0}|]; last by rewrite eqxx.
  by exists [::], (invol x1), s' => /=; rewrite invK.
by exists (x0 :: u), x, v; rewrite eqs.
Qed.

Lemma rev_inv_patt u x v :
  rev (u ++ [:: x, invol x & v]) = rev v ++ [:: invol x, x & rev u].
Proof. by rewrite rev_cat 2!rev_cons -!cats1 -!catA !cat1s. Qed.

Lemma fgreduced_rev s : (rev s \is fgreduced) = (s \is fgreduced).
Proof.
suff impl s' : s' \is fgreduced -> rev s' \is fgreduced.
  by apply/idP/idP => /impl //; rewrite revK.
move: s' => {}s; apply contraLR => /fgreducedPn [u][x][v].
rewrite -{2}(revK s) => ->; apply/fgreducedPn; rewrite rev_inv_patt.
by exists (rev v), (invol x), (rev u); rewrite invK.
Qed.
Lemma fgreduce_rev s : fgreduce (rev s) = rev (fgreduce s).
Proof.
have [b] := ubnPleq (size s); elim: b s => [s | b IHb s].
  by rewrite leqn0 => /nilP ->.
case: (boolP (s \is fgreduced)) => [sred _ |].
  by rewrite (fgreducedP sred); apply/fgreducedP; rewrite fgreduced_rev.
move/fgreducedPn => [u][x][v] -> /=.
rewrite size_cat /= !addnS ltnS -size_cat => /ltnW{}/IHb eqred.
by rewrite rev_inv_patt -{2}(invK x) !fgreduce_eqinv -rev_cat.
Qed.

Lemma fgreduced_catKl u v : u ++ v \is fgreduced -> v \is fgreduced.
Proof. by elim: u => //= x u IHu /fgreduced_consK. Qed.
Lemma fgreduced_catKr u v : u ++ v \is fgreduced -> u \is fgreduced.
Proof.
rewrite -fgreduced_rev rev_cat => /fgreduced_catKl.
by rewrite fgreduced_rev.
Qed.
Lemma fgreduce_catl u v : fgreduce (u ++ fgreduce v) = fgreduce (u ++ v).
Proof. by elim: u => [//=| x u /= ->]; first exact: fgreduce_id. Qed.
Lemma fgreduce_catr u v : fgreduce (fgreduce u ++ v) = fgreduce (u ++ v).
Proof.
rewrite -[LHS]revK -fgreduce_rev rev_cat -(fgreduce_rev u) fgreduce_catl.
by rewrite -fgreduce_rev -rev_cat revK.
Qed.

Lemma inv_patt u x v :
  map invol (u ++ [:: x, invol x & v]) =
  map invol u ++ [:: invol x, x & map invol v].
Proof. by rewrite map_cat /= invK. Qed.

Lemma fgreduced_inv s : (map invol s \is fgreduced) = (s \is fgreduced).
Proof.
suff impl s' : s' \is fgreduced -> map invol s' \is fgreduced.
  by apply/idP/idP => /impl //; rewrite -map_comp (eq_map (g := id)) ?map_id.
move: s' => {}s; apply contraLR => /fgreducedPn [u][x][v] Heq.
rewrite -(map_id s) -(eq_map (f := invol \o invol)) // map_comp Heq inv_patt.
rewrite -{2}(invK x); apply/fgreducedPn.
by exists [seq invol i | i <- u], (invol x), [seq invol i | i <- v].
Qed.
Lemma fgreduce_inv s : fgreduce (map invol s) = map invol (fgreduce s).
Proof.
have [b] := ubnPleq (size s); elim: b s => [s | b IHb s].
  by rewrite leqn0 => /nilP ->.
case: (boolP (s \is fgreduced)) => [s_red _ |].
  by rewrite (fgreducedP s_red); apply/fgreducedP; rewrite fgreduced_inv.
move/fgreducedPn => [u][x][v] -> /=.
rewrite size_cat /= !addnS ltnS -size_cat => /ltnW{}/IHb eqred.
by rewrite inv_patt -{2}(invK x) !fgreduce_eqinv -map_cat.
Qed.

Lemma fgreduce_inv_rev_cat s : fgreduce (map invol (rev s) ++ s) = [::].
Proof.
elim: s => //= x s IHs.
by rewrite rev_cons map_rcons -cats1 -catA cat1s -{2}(invK x) fgreduce_eqinv.
Qed.

Lemma fgreduce_cat_inv_rev s : fgreduce (s ++ map invol (rev s)) = [::].
Proof.
elim/last_ind: s => //= s x IHs.
by rewrite rev_rcons /= -cats1 -catA cat1s fgreduce_eqinv.
Qed.

End Fgreduce.


(** ** A type for the letter of the words (ie: g_i, g_i^-1) of a free group *)
Section FreeGenDef.

Context (T : choiceType).
Variant fgen : predArgType := FreeGen of T | InvGen of T.

Definition sum_of_fgen (m : fgen) : T + T :=
  match m with FreeGen p => inl _ p | InvGen n => inr _ n end.

Definition fgen_of_sum (m : T + T) :=
  match m with inl p => FreeGen p | inr n => InvGen n end.

Lemma sum_of_fgenK : cancel sum_of_fgen fgen_of_sum.
Proof. by case. Qed.
Lemma fgen_of_sumK : cancel fgen_of_sum sum_of_fgen.
Proof. by case. Qed.

HB.instance Definition _ := Equality.copy fgen (can_type sum_of_fgenK).
HB.instance Definition _ := Choice.copy fgen (can_type sum_of_fgenK).

Definition invfg (f : fgen) :=
  match f with FreeGen g => InvGen g | InvGen g => FreeGen g end.
Fact invfgK : involutive invfg.
Proof. by case. Qed.
Fact invfgN p : p != invfg p.
Proof. by case: p. Qed.
HB.instance Definition _ := isInvolutive.Build fgen invfgK invfgN.

End FreeGenDef.

HB.instance Definition _ (T : countType) :=
  Countable.copy (fgen T) (can_type (@sum_of_fgenK T)).
HB.instance Definition _ (T : finType) :=
  Finite.copy (fgen T) (can_type (@sum_of_fgenK T)).


(** ** A type for the reduced word in a free group *)
Section FreeGroup.

Variable (T : choiceType).

(** Making [fgval] below a Coercion leads to very confusing statements.    *)
(** In particular, because of the inverse coercion [freeg_of_gen] below.   *)
(** For example writing [a :: s] for [a : fgen T] and [s : {freeg T }], *)
(** One cannot see the difference between [a :: fgval s] and               *)
(** [fgval (freeg_of_gen a) :: fgval s]                                    *)
Record freeg : predArgType :=
  FreeG { fgval : seq (fgen T); freegP : fgval \is fgreduced }.

HB.instance Definition _ := [isSub of freeg for fgval].
HB.instance Definition _ := [Equality of freeg by <:].
HB.instance Definition _ := [Choice of freeg by <:].

Definition freeg_of_gen (a : fgen T) : freeg :=
  FreeG (@fgreduced1 (fgen T : involType) a).

End FreeGroup.
#[export] Hint Resolve freegP : core.
Notation "{ 'freeg' T }" := (freeg T) : form_scope.
Notation "''g_' i" := (freeg_of_gen (FreeGen i)).

HB.instance Definition _ (T : countType) := [Countable of {freeg T} by <:].


(** ** Group structure of the free group *)
Section FreeGroupOperations.

Context {T : choiceType}.
Implicit Type (i j k : T) (a b c : fgen T) (u v w : {freeg T}).

Definition onefreeg : {freeg T} := FreeG fgreduced0.

Fact mulfreeg_subproof u v : fgreduce (val u ++ val v) \is fgreduced.
Proof. exact: fgreduceP. Qed.
Definition mulfreeg u v : {freeg T} := FreeG (mulfreeg_subproof u v).

Fact invfreeg_subproof u : map invol (rev (val u)) \is fgreduced.
Proof. by rewrite fgreduced_inv fgreduced_rev freegP. Qed.
Definition invfreeg u : {freeg T} := FreeG (invfreeg_subproof u).

Fact mulfreegA : associative mulfreeg.
Proof.
move=> u v w; apply val_inj => /=.
by rewrite fgreduce_catl fgreduce_catr catA.
Qed.
Fact mul1freeg : left_id onefreeg mulfreeg.
Proof. by case=> [u u_red]; apply val_inj => /=; exact/fgreducedP. Qed.
Fact mulfreeg1 : right_id onefreeg mulfreeg.
Proof.
by case=> [u u_red]; apply val_inj => /=; rewrite cats0; exact/fgreducedP.
Qed.
Fact invfreegK : involutive invfreeg.
Proof.
move=> u; apply val_inj => /=.
rewrite -map_rev revK -map_comp (eq_map (g := id)) ?map_id // => a /=.
exact: involK.
Qed.
Fact invfreeg_antimorph :
  {morph invfreeg : u v / mulfreeg u v >-> mulfreeg v u}.
Proof.
move=> u v; apply val_inj => /=.
by rewrite -map_cat -rev_cat fgreduce_inv fgreduce_rev.
Qed.
Fact mulVfreeg : left_inverse onefreeg invfreeg mulfreeg.
Proof. by move=> u; apply val_inj => /=; rewrite fgreduce_inv_rev_cat. Qed.
HB.instance Definition _ :=
  isStarMonoid.Build {freeg T} mulfreegA mul1freeg invfreegK invfreeg_antimorph.
HB.instance Definition _ :=
  StarMonoid_isGroup.Build {freeg T} mulVfreeg.

End FreeGroupOperations.



(** Group properties and universal properties *)
Section Theory.

Context {T : choiceType}.
Implicit Type (i j k : T) (a b c : fgen T) (u v w : {freeg T}).


Lemma invgenE i : (freeg_of_gen (InvGen i)) = ('g_i)^-1.
Proof. by apply/esym/mulg1_eq; apply val_inj; rewrite /invol /= eqxx. Qed.

Lemma mulfreeg_consE a v :
  a :: val v \is fgreduced -> val (freeg_of_gen a * v) = a :: val v.
Proof. by move/fgreducedP. Qed.

Lemma freeg_ind_reduced (P : {freeg T} -> Type) :
  P 1 ->
  (forall a u, a :: val u \is fgreduced -> P u -> P (freeg_of_gen a * u)) ->
  forall u, P u.
Proof.
move=> P1 Pind [s]; elim: s => [|a s IHs] red.
  suff -> : FreeG red = 1 :> {freeg T} by [].
  exact: val_inj.
have s_red := fgreduced_consK red.
have -> : FreeG red = freeg_of_gen a * FreeG s_red.
  by apply val_inj; rewrite mulfreeg_consE.
by apply: Pind; last exact: IHs.
Qed.

Lemma freeg_ind (P : {freeg T} -> Type) :
  P 1 -> (forall a u, P u -> P (freeg_of_gen a * u)) -> forall u, P u.
Proof. by move=> /freeg_ind_reduced /[swap] H; apply => a u _ /H. Qed.

Lemma freegE u : u = \prod_(i <- val u) (freeg_of_gen i).
Proof.
elim/freeg_ind_reduced: u => [| a u au_red {1}->]; first by rewrite big_nil.
by rewrite mulfreeg_consE // big_cons.
Qed.

Section UniversalProperty.

Variable (gT : groupType) (f : T -> gT).

Definition univgen a :=
  match a with | FreeGen i => f i | InvGen i => (f i)^-1 end.
Definition univmor u := \prod_(a <- val u) univgen a.

Lemma univgen_inv a : univgen (invol a) = (univgen a)^-1.
Proof. by case: a => //= a; rewrite invgK. Qed.

Lemma morph_fgreduce (w : seq (fgen T)) :
  \prod_(a <- fgreduce w) univgen a = \prod_(a <- w) univgen a.
Proof.
have [b] := ubnPleq (size w); elim: b w => [|b IHb] w.
  by rewrite leqn0 => /nilP ->.
rewrite leq_eqVlt => /orP[/eqP|/ltnSE]; last exact: IHb.
case: w => // a w /= [eqsz]; rewrite -{b}eqsz in IHb.
rewrite big_cons.
case: (altP (a =P _)) => [eqa|/negbTE]; last by rewrite big_cons IHb.
rewrite -(IHb _ (leqnn _)).
case: (fgreduce w) eqa => [/eqP|b v /= ->{a}]; first by rewrite involF.
by rewrite big_cons univgen_inv mulKg.
Qed.

Fact univmor_is_monoid_morphism : monoid_morphism univmor.
Proof.
split=> [|u v]; first by rewrite /univmor big_nil.
by rewrite /univmor /= morph_fgreduce -big_cat.
Qed.
HB.instance Definition _ :=
  isUMagmaMorphism.Build {freeg T} gT univmor univmor_is_monoid_morphism.

Lemma univmorE i : univmor 'g_i = f i.
Proof. by rewrite /univmor /= big_seq1. Qed.

Lemma univmor_uniq (phi : UMagmaMorphism.type {freeg T} gT) :
  (forall i, phi 'g_i = f i) -> phi =1 univmor.
Proof.
move=> eqphi; elim/freeg_ind => [|a u IHu]; first by rewrite !gmulf1.
rewrite !gmulfM /= {}IHu; congr (_ * _) => {u}.
case: a => a; first by rewrite eqphi univmorE.
by rewrite !invgenE !gmulfV /= eqphi univmorE.
Qed.

End UniversalProperty.

End Theory.
