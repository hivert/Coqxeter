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
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype choice fintype.
From mathcomp Require Import ssrnat seq finfun finset tuple.
From mathcomp Require Import bigop fingroup perm morphism alt gproduct.
From mathcomp Require Import ssralg zmodp div.

Require Import ssrcompl.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.

Import GroupScope.


Module InvolutiveType.

Section ClassDef.

Structure mixin_of (T : eqType) := Mixin {
  inv : T -> T;
  _ : involutive inv;
  _ : forall t, t != inv t;
}.

Set Primitive Projections.
Record class_of T := Class {
                         base : Choice.class_of T;
                         mixin : mixin_of (Equality.Pack base)
                       }.
Unset Primitive Projections.
Local Coercion base : class_of >-> Choice.class_of.

Structure type := Pack { sort; _ : class_of sort }.
Local Coercion sort : type >-> Sortclass.

Variables (T : Type) (cT : type).
Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack T c.

Definition pack :=
  fun b bT & phant_id (Choice.class bT) b => fun m => Pack (@Class T b m).

(* Inheritance *)
Definition eqType := @Equality.Pack cT class.
Definition choiceType := @Choice.Pack cT class.

End ClassDef.

Module Exports.

Coercion base : class_of >-> Choice.class_of.
Coercion sort : type >-> Sortclass.
Coercion mixin : class_of >-> mixin_of.

Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.

Notation invType := type.
Notation InvMixin := Mixin.
Notation InvType T m := (@pack T _ _ id m).
Notation "[ 'invMixin' 'of' T ]" := (class _ : mixin_of T)
  (at level 0, format "[ 'invMixin'  'of'  T ]") : form_scope.
Notation "[ 'invType' 'of' T 'for' cT ]" := (@clone T cT _ id)
  (at level 0, format "[ 'invType'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'invType' 'of' T ]" := (@clone T _ _ id)
  (at level 0, format "[ 'invType'  'of'  T ]") : form_scope.

End Exports.

End InvolutiveType.
Export InvolutiveType.Exports.

Definition invol {T : invType} : T -> T :=
  InvolutiveType.inv (InvolutiveType.class T).

Section Theory.

Variable T : invType.

Lemma invK : involutive (@invol T).
Proof. by case T => [T0 [B []]]. Qed.
Lemma invN t : t != (@invol T) t.
Proof. by move: t; case T => [T0 [B []]]. Qed.
Lemma invF t : (t == (@invol T) t) = false.
Proof. exact: negbTE (invN _). Qed.

End Theory.
#[export] Hint Resolve invK invN : core.


Fixpoint fgreduce {T : invType} (s : seq T) :=
  if s is x :: s' then
    let sres := fgreduce s' in
    if x == invol (head x sres) then behead sres else x :: sres
  else [::].
Definition fgreduced {T : invType} := [qualify s : seq T | fgreduce s == s].

Section Fgreduce.

Context {T : invType}.
Implicit Type (x y z : T) (s t u v : seq T).

Let invK := (@invK T).
Let invN := (@invN T).
Let invF := (@invF T).

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
  x :: s \is fgreduced = (s \is fgreduced) && (x != invol (head x s)).
Proof.
apply/idP/andP => [ xssimpl|[]]; first last.
  by rewrite !qualifE /= => /eqP -> /negbTE ->.
split; first exact: (fgreduced_consK xssimpl).
have [_] := size_fgreduce (x :: s); rewrite xssimpl => /eqP /=.
have /fgreducedP -> := fgreduced_consK xssimpl.
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
case: (fgreduce s) => [|x1 s'] {s} Hsimpl; first by rewrite /= invF fgreduced1.
rewrite [head _ _]/= [behead _]/=.
case: (altP (x =P invol x1)) => [_ | Hneq]; first exact: fgreduced_consK Hsimpl.
by rewrite fgreduced_cons Hsimpl /=.
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

Lemma rev_inv_spat u x v :
  rev (u ++ [:: x, invol x & v]) = rev v ++ [:: invol x, x & rev u].
Proof. by rewrite rev_cat 2!rev_cons -!cats1 -!catA !cat1s. Qed.

Lemma fgreduced_rev s : (rev s \is fgreduced) = (s \is fgreduced).
Proof.
suff impl s' : s' \is fgreduced -> rev s' \is fgreduced.
  by apply/idP/idP => /impl //; rewrite revK.
move: s' => {}s; apply contraLR => /fgreducedPn [u][x][v].
rewrite -{2}(revK s) => ->; apply/fgreducedPn; rewrite rev_inv_spat.
by exists (rev v), (invol x), (rev u); rewrite invK.
Qed.
Lemma fgreduce_rev s : fgreduce (rev s) = rev (fgreduce s).
Proof.
have [b] := ubnPleq (size s); elim: b s => [s | b IHb s].
  by rewrite leqn0 => /nilP ->.
case: (boolP (s \is fgreduced)) => [ssimpl _ |].
  by rewrite (fgreducedP ssimpl); apply/fgreducedP; rewrite fgreduced_rev.
move/fgreducedPn => [u][x][v] -> /=.
rewrite size_cat /= !addnS ltnS -size_cat => /ltnW{}/IHb eqsimpl.
by rewrite rev_inv_spat -{2}(invK x) !fgreduce_eqinv -rev_cat.
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

Lemma inv_spat u x v :
  map invol (u ++ [:: x, invol x & v]) =
  map invol u ++ [:: invol x, x & map invol v].
Proof. by rewrite map_cat /= invK. Qed.

Lemma fgreduced_inv s : (map invol s \is fgreduced) = (s \is fgreduced).
Proof.
suff impl s' : s' \is fgreduced -> map invol s' \is fgreduced.
  by apply/idP/idP => /impl //; rewrite -map_comp (eq_map (f2 := id)) ?map_id.
move: s' => {}s; apply contraLR => /fgreducedPn [u][x][v] Heq.
rewrite -(map_id s) -(eq_map (f1 := invol \o invol)) // map_comp Heq inv_spat.
rewrite -{2}(invK x); apply/fgreducedPn.
by exists [seq invol i | i <- u], (invol x), [seq invol i | i <- v].
Qed.
Lemma fgreduce_inv s : fgreduce (map invol s) = map invol (fgreduce s).
Proof.
have [b] := ubnPleq (size s); elim: b s => [s | b IHb s].
  by rewrite leqn0 => /nilP ->.
case: (boolP (s \is fgreduced)) => [ssimpl _ |].
  by rewrite (fgreducedP ssimpl); apply/fgreducedP; rewrite fgreduced_inv.
move/fgreducedPn => [u][x][v] -> /=.
rewrite size_cat /= !addnS ltnS -size_cat => /ltnW{}/IHb eqsimpl.
by rewrite inv_spat -{2}(invK x) !fgreduce_eqinv -map_cat.
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

Declare Scope freeg_scope.
Delimit Scope freeg_scope with FG.

Reserved Notation "''g_' i" (at level 2, format "''g_' i").
Reserved Notation "''g^-1_' i" (at level 2, format "''g^-1_' i").
Reserved Notation "'FGen<<' T '>>'" (at level 8, format "'FGen<<' T '>>'").
Reserved Notation "'FreeG<<' T '>>'" (at level 8, format "'FreeG<<' T '>>'").

Section FreeGenDef.

Context {T : choiceType}.
Variant fgen : predArgType := FreeGen of T | InvGen of T.

Definition fgen_of of phant T := fgen.
Local Notation fgenT := (fgen_of (Phant T)).
Identity Coercion type_of_fgen : fgen_of >-> fgen.

Definition sum_of_fgen (m : fgenT) : T + T :=
  match m with FreeGen p => inl _ p | InvGen n => inr _ n end.

Definition fgen_of_sum (m : T + T) :=
  match m with inl p => FreeGen p | inr n => InvGen n end.

Lemma sum_of_fgenK : cancel sum_of_fgen fgen_of_sum.
Proof. by case. Qed.

Definition fgen_eqMixin := CanEqMixin sum_of_fgenK.
Canonical fgen_eqType := Eval hnf in EqType fgenT fgen_eqMixin.
Definition fgen_choiceMixin := CanChoiceMixin sum_of_fgenK.
Canonical fgen_choiceType :=
  Eval hnf in ChoiceType fgenT fgen_choiceMixin.

End FreeGenDef.

Notation "'FGen<<' T >>" := (fgen_of (Phant T)).
Notation "''g_' i" := (FreeGen i : FGen<< _ >>) : freeg_scope.
Notation "''g^-1_' i" := (InvGen i : FGen<< _ >>) : freeg_scope.

Definition fgen_countMixin (T : countType) :=
  CanCountMixin (@sum_of_fgenK T).
Canonical fgen_countType (T : countType) :=
  Eval hnf in CountType FGen<<T>> (fgen_countMixin T).
Definition fgen_finMixin (T : finType) :=
  CanFinMixin (@sum_of_fgenK T).
Canonical fgen_finType (T : finType) :=
  Eval hnf in FinType FGen<<T>> (fgen_finMixin T).

Lemma eqfgenE (T : choiceType) (m n : T) : ('g_m == 'g_n)%FG = (m == n).
Proof. by []. Qed.


Section Fgen.

Variable (T : choiceType).

Definition invfg (f : FGen<<T>>) :=
  match f with FreeGen g => InvGen g | InvGen g => FreeGen g end.
Lemma invfgK : involutive invfg.
Proof. by case. Qed.
Lemma invfgN p : p != invfg p.
Proof. by case: p. Qed.

Definition fgen_invMixin := InvMixin invfgK invfgN.
Canonical fgen_invType := InvType FGen<<T>> fgen_invMixin.

End Fgen.


Section FreeGroup.

Variable (T : choiceType).

Record freeg_elem : predArgType :=
  FreeGElem {
      fgval : seq (FGen<<T>>);
      _ : fgval \is fgreduced
  }.
Definition freeg_elem_of of phant T := freeg_elem.
Local Notation freeg := (freeg_elem_of (Phant T)).
Identity Coercion type_of_freeg_elem : freeg_elem_of >-> freeg_elem.

Canonical freeg_subType := Eval hnf in [subType for fgval].
Definition freeg_eqMixin := Eval hnf in [eqMixin of freeg by <:].
Canonical freeg_eqType := Eval hnf in EqType freeg freeg_eqMixin.
Definition freeg_choiceMixin := Eval hnf in [choiceMixin of freeg by <:].
Canonical freeg_choiceType := Eval hnf in ChoiceType freeg freeg_choiceMixin.

Implicit Type (w : freeg).

Lemma freegP w : fgval w \is fgreduced.
Proof. by case: w. Qed.

End FreeGroup.
#[export] Hint Resolve freegP : core.
Notation "'FreeG<<' T >>" := (freeg_elem_of (Phant T)).

Coercion freeg_of_gen (T : choiceType) (ph : phant T)
         (a : fgen_of ph) : freeg_elem_of ph :=
  FreeGElem (@fgreduced1 (fgen_invType T) a).


Section CountType.

Variable (T : countType).

Definition freeg_countMixin := Eval hnf in [countMixin of FreeG<<T>> by <:].
Canonical freeg_countType := Eval hnf in CountType FreeG<<T>> freeg_countMixin.
Canonical freeg_subCountType := Eval hnf in [subCountType of FreeG<<T>>].

End CountType.


Section FreeGroupOperations.

Context {T : choiceType}.
Implicit Type (i j k : T) (a b c : FGen<<T>>) (u v w : FreeG<<T>>).

Definition onefreeg : FreeG<<T>> := FreeGElem fgreduced0.

Fact mulfreeg_subproof u v : fgreduce (val u ++ val v) \is fgreduced.
Proof. exact: fgreduceP. Qed.
Definition mulfreeg u v : FreeG<<T>> := FreeGElem (mulfreeg_subproof u v).

Fact invfreeg_subproof u : map invol (rev (val u)) \is fgreduced.
Proof. by rewrite fgreduced_inv fgreduced_rev freegP. Qed.
Definition invfreeg u : FreeG<<T>> := FreeGElem (invfreeg_subproof u).

Lemma mulfreegA : associative mulfreeg.
Proof.
move=> u v w; apply val_inj => /=.
by rewrite fgreduce_catl fgreduce_catr catA.
Qed.

Lemma mul1freeg : left_id onefreeg mulfreeg.
Proof. by case=> [u simplu]; apply val_inj => /=; exact/fgreducedP. Qed.

Lemma mulfreeg1 : right_id onefreeg mulfreeg.
Proof.
by case=> [u simplu]; apply val_inj => /=; rewrite cats0; exact/fgreducedP.
Qed.

Lemma invfreegK : involutive invfreeg.
Proof.
move=> u; apply val_inj => /=.
rewrite -map_rev revK -map_comp (eq_map (f2 := id)) ?map_id // => a /=.
exact: invK.
Qed.

Lemma invfreeg_antimorph :
  {morph invfreeg : u v / mulfreeg u v >-> mulfreeg v u}.
Proof.
move=> u v; apply val_inj => /=.
by rewrite -map_cat -rev_cat fgreduce_inv fgreduce_rev.
Qed.

Lemma mulVfreeg : left_inverse onefreeg invfreeg mulfreeg.
Proof. by move=> u; apply val_inj => /=; rewrite fgreduce_inv_rev_cat. Qed.

Canonical freeg_law := Monoid.Law mulfreegA mul1freeg mulfreeg1.

End FreeGroupOperations.

Notation "1" := onefreeg : freeg_scope.
Infix "*" := mulfreeg : freeg_scope.
Notation "w ^-1" := (invfreeg w) : freeg_scope.

Local Open Scope freeg_scope.

Notation "\prod_ ( i <- r | P ) F" :=
  (\big[mulfreeg/1]_(i <- r | P%B) F%FG) : freeg_scope.
Notation "\prod_ ( i <- r ) F" :=
  (\big[mulfreeg/1]_(i <- r) F%FG) : freeg_scope.
Notation "\prod_ ( m <= i < n | P ) F" :=
  (\big[mulfreeg/1]_(m <= i < n | P%B) F%FG) : freeg_scope.
Notation "\prod_ ( m <= i < n ) F" :=
  (\big[mulfreeg/1]_(m <= i < n) F%FG) : freeg_scope.
Notation "\prod_ ( i | P ) F" :=
  (\big[mulfreeg/1]_(i | P%B) F%FG) : freeg_scope.
Notation "\prod_ i F" :=
  (\big[mulfreeg/1]_i F%FG) : freeg_scope.
Notation "\prod_ ( i : t | P ) F" :=
  (\big[mulfreeg/1]_(i : t | P%B) F%FG) (only parsing) : freeg_scope.
Notation "\prod_ ( i : t ) F" :=
  (\big[mulfreeg/1]_(i : t) F%FG) (only parsing) : freeg_scope.
Notation "\prod_ ( i < n | P ) F" :=
  (\big[mulfreeg/1]_(i < n | P%B) F%FG) : freeg_scope.
Notation "\prod_ ( i < n ) F" :=
  (\big[mulfreeg/1]_(i < n) F%FG) : freeg_scope.
Notation "\prod_ ( i 'in' A | P ) F" :=
  (\big[mulfreeg/1]_(i in A | P%B) F%FG) : freeg_scope.
Notation "\prod_ ( i 'in' A ) F" :=
  (\big[mulfreeg/1]_(i in A) F%FG) : freeg_scope.


Section Theory.

Context {T : choiceType}.
Implicit Type (i j k : T) (a b c : FGen<<T>>) (u v w : FreeG<<T>>).

Lemma mulfreeg_consE a v :
  a :: val v \is fgreduced -> val (a * v) = a :: val v.
Proof. by rewrite /= => /fgreducedP. Qed.
Lemma mulfreegE u v :
  val u ++ val v \is fgreduced -> val (u * v) = val u ++ val v.
Proof. by rewrite /= => /fgreducedP. Qed.

Lemma freeg_ind (P : FreeG<<T>> -> Type) :
  P 1 ->
  (forall a u, a :: val u \is fgreduced -> P u -> P (a * u)) ->
  forall u, P u.
Proof.
move=> P1 Pind [s]; elim: s => [|a s IHs] Hsimpl.
  suff -> : FreeGElem Hsimpl = 1 by [].
  exact: val_inj.
have simpls := fgreduced_consK Hsimpl.
have -> : FreeGElem Hsimpl = a * FreeGElem simpls.
  by apply val_inj; rewrite mulfreeg_consE.
by apply: Pind; last exact: IHs.
Qed.

Lemma freegE u : u = \prod_(i <- val u) i.
Proof.
elim/freeg_ind: u => [| a u simplau {1}->]; first by rewrite big_nil.
by rewrite mulfreeg_consE // big_cons.
Qed.

Section UniversalProperty.

Variable (gT : finGroupType) (f : T -> gT).

Definition fgenind a :=
  match a with | FreeGen i => f i | InvGen i => ((f i)^-1)%g end.
Definition fgind u := (\prod_(a <- val u) fgenind a)%g.

Lemma fgenind_inv a : fgenind (invol a) = ((fgenind a)^-1)%g.
Proof. by case: a => //= a; rewrite invgK. Qed.

Lemma morph_fgreduce (w : seq FGen<<T>>) :
  (\prod_(a <- fgreduce w) fgenind a)%g = (\prod_(a <- w) fgenind a)%g.
Proof.
have [b] := ubnPleq (size w); elim: b w => [|b IHb] w.
  by rewrite leqn0 => /nilP ->.
rewrite leq_eqVlt => /orP[/eqP|/ltnSE]; last exact: IHb.
case: w => // a w /= [eqsz]; rewrite -{b}eqsz in IHb.
rewrite big_cons.
case: (altP (a =P _)) => [eqa|/negbTE]; last by rewrite big_cons IHb.
rewrite -(IHb _ (leqnn _)).
case: (fgreduce w) eqa => [/eqP|b v /= ->{a}]; first by rewrite invF.
by rewrite big_cons fgenind_inv mulKg.
Qed.

Lemma fgind1 : fgind 1 = 1%g.
Proof. by rewrite /fgind big_nil. Qed.

Lemma fgmorphM : {morph fgind : u v / u * v >-> (u * v)%g}.
Proof. by rewrite /fgind => u v; rewrite /= morph_fgreduce -big_cat. Qed.

Lemma fgmorphV : {morph fgind : u / u^-1 >-> (u^-1)%g}.
Proof.
rewrite /fgind => u /=.
apply/esym/eqP; rewrite eq_invg_mul -big_cat /= -morph_fgreduce.
by rewrite fgreduce_cat_inv_rev big_nil.
Qed.

Lemma fgmorphE i : fgind 'g_i = f i.
Proof. by rewrite /fgind /= big_seq1. Qed.

End UniversalProperty.

End Theory.
