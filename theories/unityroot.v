From HB Require Import structures.
From Stdlib Require Import ZifyClasses ZArith.
From mathcomp Require Import boot order.
From mathcomp Require Import algebra ssrint ssralg ssrnum algC closed_field.
From mathcomp Require Import poly separable polydiv cyclotomic.
From mathcomp Require Import ring_tactic field_tactic ssrZ zify arithmetic_tactic.


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope order_scope.
Local Open Scope ring_scope.

Import Order.TTheory GRing.Theory Num.Theory Num.Def.

Open Scope ring_scope.


Local Definition rpred_simpl :=
  (rpredD, rpredB, rpred1, rpred0, rpredN, rpredM, rpredV, algRvalP).

Hint Resolve algRvalP : core.


Lemma neq20 : 2 != 0 :> algC.
Proof. by have /pcharf0P -> := Cpchar. Qed.
Hint Resolve neq20 : core.


Section RingTheory.

Variable (R : pzRingType).
Implicit Type (x y z : R).

Lemma exprD1 n z : z ^+ n - 1 = (z - 1) * \sum_(0 <= i < n) z ^+ i.
Proof.
rewrite mulrDl mulN1r mulr_sumr.
under eq_bigr do rewrite -exprS.
by rewrite -sumrB telescope_sumr.
Qed.

End RingTheory.


Section RootOfUnity.

Variable (R : comNzRingType) (n : nat).

Fact unity_root_mul_closed : @mulr_closed R (@root_of_unity R n).
Proof.
split=> [|x y]; rewrite -!topredE /= !unity_rootE ?expr1n //.
by rewrite exprMn => /eqP-> /eqP-> /[!mulr1].
Qed.
HB.instance Definition _ :=
  GRing.isMulClosed.Build R (@root_of_unity R n) unity_root_mul_closed.

End RootOfUnity.


Section RootOfUnityUnitRing.

Variable (R : comUnitRingType) (n : nat).

Fact unity_root_inv_closed : @invr_closed R (@root_of_unity R n).
Proof.
by move=> x; rewrite -!topredE /= !unity_rootE exprVn => /eqP-> /[!invr1].
Qed.
HB.instance Definition _ :=
  GRing.isInvClosed.Build R (@root_of_unity R n) unity_root_inv_closed.

End RootOfUnityUnitRing.


Lemma mono_le_algRval : {mono algRval : x y / x <= y}. Proof. by []. Qed.
Lemma mono_lt_algRval : {mono algRval : x y / x < y}. Proof. by []. Qed.
Lemma sgr_algRval (r : algR) : sgr (algRval r) = sgr r.
Proof. by rewrite !sgr_def -val_eqE rmorphMn rmorphXn. Qed.
Lemma sgr_mulr (R : numDomainType) (x y : R) : y > 0 -> sgr (x * y) = sgr x.
Proof.
move=> lt0y; rewrite !sgr_def pmulr_llt0 // mulf_eq0.
by rewrite (negbTE (lt0r_neq0 lt0y)) orbF.
Qed.


Section NumField.
Variable (R : numFieldType).

Lemma oppr_ltr (x : R) : x \is real_num -> (-x < x) = (0 < x).
Proof.
rewrite -comparable0r=> /comparable_ltgtP[/gt0_cp[_ ->] // | | <-].
  by move=> /[dup] H; rewrite -{1}(opprK x) oppr_lt0 => /(lt_trans H)/lt_gtF.
by rewrite oppr0 ltxx.
Qed.
Lemma oppr_ler (x : R) : x \is real_num -> (-x <= x) = (0 <= x).
Proof. by move/oppr_ltr => Heq; rewrite !le_eqVlt eqNr eq_sym; congr orb. Qed.

End NumField.


Section GeometricPoly.

Context {R : numClosedFieldType}.
Implicit Type (x y z : R).

Lemma unity_root_conj n (x : R) : n.-unity_root x^* = n.-unity_root x.
Proof.
rewrite !unity_rootE -rmorphXn /= -[in LHS]conjC1 inj_eq //.
exact: (can_inj (@conjCK R)).
Qed.

Lemma conjC_horner (p : {poly R}) (x : R) :
  (p.[x])^* = (\poly_(i < size p) (p`_i)^*).[x^*].
Proof.
rewrite horner_poly horner_coef raddf_sum /=; apply eq_bigr => i _.
by rewrite rmorphM rmorphXn /=.
Qed.

Lemma real_conjC_root (p : {poly R}) (x : R) :
  (forall i, p`_i \is real_num) -> root p x^* = root p x.
Proof.
rewrite /root => Hreal.
suff {1}-> : p = \poly_(i < size p) (p`_i)^* by rewrite -conjC_horner conjC_eq0.
rewrite -{1}(coefK p) !poly_def; apply: eq_bigr => i _.
by rewrite (conj_Creal (Hreal i)).
Qed.


Variables (n : nat).
Hypothesis (gtn0 : (0 < n)%N).

Definition geompol : {poly R} := \poly_(i < n) 1.

Lemma size_geompol : size geompol = n.
Proof. exact/size_poly_eq/oner_neq0. Qed.
Lemma lead_geompol : lead_coef geompol = 1.
Proof. by rewrite lead_coef_poly // oner_neq0. Qed.

Lemma geompolE : geompol = \sum_(0 <= i < n) 'X^i.
Proof.
rewrite /geompol poly_def big_mkord; apply: eq_bigr => /= i _.
by rewrite scale1r.
Qed.

Lemma conjC_root_geompol x : root geompol x^* = root geompol x.
Proof. by apply: real_conjC_root => i; rewrite coef_poly; case: ltnP. Qed.

Lemma root_geompolE x : (root geompol x) = (n.-unity_root x) && (x != 1).
Proof.
rewrite geompolE; apply/idP/andP => [Hr | [ + /negbTE neq1]].
  split; first by rewrite /root_of_unity exprD1 rootM orbC Hr.
  apply/contraL: Hr => /eqP ->; apply/negP => /rootP; rewrite horner_sum.
  under eq_bigr do rewrite hornerXn expr1n.
  by rewrite sumr_const_nat subn0 => /eqP; rewrite pnatr_eq0 -leqn0 leqNgt gtn0.
rewrite /root_of_unity exprD1 rootM => /orP[|//].
by rewrite root_XsubC neq1.
Qed.
Lemma separable_geompol : separable_poly geompol.
Proof.
have /separable_Xn_sub_1 : n%:R != 0 :> R by rewrite pnatr_eq0 -lt0n.
by apply: dvdp_separable; rewrite geompolE exprD1 dvdp_mulIr.
Qed.

End GeometricPoly.


Implicit Type (y z : algC) (t : algR).


Definition unitcircle : pred algC := [pred z | `|z| ^+ 2 == 1].

Lemma unitcircleE z : (z \in unitcircle) = (`|z| ^+ 2 == 1).
Proof. by []. Qed.
Lemma unitcircleP z : reflect (`|z| ^+ 2 = 1) (z \in unitcircle).
Proof. exact: (iffP eqP). Qed.
Lemma unitcircle_neq0 z : z \in unitcircle -> z != 0.
Proof.
move/unitcircleP => Heq; apply/negP => /eqP eqz.
move: Heq; rewrite eqz normr0 expr2 mulr0 => /esym/eqP.
by rewrite oner_eq0.
Qed.
Lemma unitcircle1 : 1 \in unitcircle.
Proof. by rewrite unitcircleE normr1 expr1n. Qed.
Lemma unitcirclei : 'i \in unitcircle.
Proof. by rewrite unitcircleE normCi expr1n. Qed.
Lemma unitcircleN z : (-z \in unitcircle) = (z \in unitcircle).
Proof. by rewrite !unitcircleE normrN. Qed.

Lemma unitcircleM y z :
  y \in unitcircle -> z \in unitcircle -> (y * z) \in unitcircle.
Proof.
move=> /unitcircleP ny /unitcircleP nz.
by apply/unitcircleP; rewrite normrM exprMn ny nz mulr1.
Qed.
Lemma unitcircleV z : (z ^-1 \in unitcircle) = (z \in unitcircle).
Proof. by rewrite !unitcircleE normfV exprVn invr_eq1. Qed.
Lemma unitcircleXn z n : z \in unitcircle -> z ^+ n \in unitcircle.
Proof.
move=> cz; elim: n => [|n IHn]; first by rewrite expr0 unitcircle1.
by rewrite exprS unitcircleM ?cz.
Qed.
Lemma unitcircleXn1 z n : z ^+ n.+1 \in unitcircle -> z \in unitcircle.
Proof.
by rewrite !unitcircleE normrX exprAC pexpr_eq1 // -realEsqr normr_real.
Qed.

Lemma unitcircleXNn z n : z \in unitcircle -> (z ^- n) \in unitcircle.
Proof. by rewrite unitcircleV => cz; exact/unitcircleXn. Qed.

Lemma unity_root_unitcircle n z :
  (0 < n)%N -> n.-unity_root z -> z \in unitcircle.
Proof.
rewrite /root_of_unity /root !hornerE subr_eq0 => gtn0.
move/eqP/(congr1 normr)/eqP; rewrite normr1 normrX pexpr_eq1 // => /eqP nz.
by apply/unitcircleP; rewrite nz expr1n.
Qed.

Lemma in_unitycircleV z : z \in unitcircle -> z^-1 = z^*.
Proof.
move=> /[dup] /unitcircleP zu /unitcircle_neq0/[dup] nz0 /lregP; apply.
by rewrite divff // -normCK zu.
Qed.

Definition param t : algC :=
  ((t ^+ 2 - 1) / (t ^+ 2 + 1) : algC) + 'i * ((2 * t) / (t ^+ 2 + 1) : algC).

Lemma Re_paramP t : (t ^+ 2 - 1) / (t ^+ 2 + 1) \is real_num.
Proof. by apply: rpredM; rewrite /= ?rpredB /=. Qed.
Lemma Im_paramP t :  2 * t / (t ^+ 2 + 1) \is real_num.
Proof. by apply: rpredM; rewrite /= ?rpredD /=. Qed.

Lemma Re_paramE t : 'Re (param t) = (t ^+ 2 - 1) / (t ^+ 2 + 1).
Proof. exact: (Re_rect (Re_paramP t) (Im_paramP t)). Qed.
Lemma Im_paramE t : 'Im (param t) = (2 * t) / (t ^+ 2 + 1).
Proof. exact: (Im_rect (Re_paramP t) (Im_paramP t)). Qed.

Lemma sqp1_gt0 t : (t ^+ 2 + 1 : algC) > 0.
Proof.
apply: (lt_le_trans ltr01); rewrite -{1}(add0r 1); apply: lerD => //.
by rewrite -realEsqr.
Qed.
Lemma sqp1_ne0 t : (t ^+ 2 + 1 : algC) !=  0.
Proof. exact: (lt0r_neq0 (sqp1_gt0 t)). Qed.
Lemma addCi_ne0 t : \val t + 'i != 0.
Proof.
apply/negP => /eqP/(congr1 (fun z => 'Im z))/eqP; rewrite raddfD /=.
have /Creal_ImP -> := algRvalP t.
by rewrite add0r raddf0 Im_i oner_eq0.
Qed.
Lemma subCi_ne0 t : \val t - 'i != 0.
Proof. by rewrite -conjC_eq0 raddfB /= conjCi opprK conj_Creal ?addCi_ne0. Qed.

Lemma paramE t : param t = (\val t + 'i) / (\val t - 'i).
Proof.
rewrite /param.
have tin0 : \val t - 'i != 0.
  apply/negP => /eqP/(congr1 (fun z => 'Im z))/eqP; rewrite raddfB /=.
  have /Creal_ImP -> := algRvalP t.
  by rewrite add0r raddf0 Im_i oppr_eq0 oner_eq0.
field: (@sqrCi algC) by rewrite //= sqp1_ne0.
Qed.

Lemma param_inv_subproof z : 'Im z / (1 - 'Re z) \is real_num.
Proof.
apply: rpredM => /=; first exact: Creal_Im.
by rewrite rpredV rpredB //= real1.
Qed.
Definition param_inv z : algR := in_algR (param_inv_subproof z).

Lemma param_inv1 : param_inv 1 = 0.
Proof. by apply val_inj; rewrite /= (Creal_ReP _ _) //= subrr invr0 mulr0. Qed.
Lemma param_inv_conjC z : param_inv (z^*) = - param_inv z.
Proof. by apply val_inj; rewrite /= Re_conj Im_conj mulNr. Qed.

Lemma param_on_cycle t : param t \in unitcircle.
Proof.
rewrite /param unitcircleE normC2_rect ?algRvalP //.
by apply/eqP; field by rewrite sqp1_ne0.
Qed.

Lemma paramK : cancel param param_inv.
Proof.
move=> t; apply val_inj; rewrite /= Re_paramE Im_paramE.
have den1 := sqp1_ne0 t.
have den2 : t ^+ 2 + 1 - (t ^+ 2 + -1) != 0 :> algC.
  by rewrite /= [X in X != 0](_ : _ = 2); first ring.
field by done.
Qed.

Lemma param_invK : {in predI unitcircle (predC1 1), cancel param_inv param}.
Proof.
move=> z; rewrite !inE => /andP[/unitcircleP].
rewrite {2 4}(algCrect z) normC2_Re_Im /param /param_inv /=.
move: ('Re z) ('Im z) (Creal_Re z) (Creal_Im z) => {z} a b aR bR uc neq1.
rewrite -[1 + 1]/2.
have {}neq1 : 1 - a != 0.
  rewrite subr_eq0 eq_sym; apply/contra: neq1 => /eqP a1; subst a.
  suff /eqP -> : b == 0 by rewrite mulr0 addr0.
  by move/eqP: uc; rewrite expr1n eq_sym addrC -subr_eq subrr eq_sym sqrf_eq0.
set pa : algC := (X in X + _ = _); set pb : algC := (X in _ + 'i * X = _).
suff [-> ->] : pa = a /\ pb = b by [].
split; rewrite {}/pa {}/pb !mulrA.
  rewrite ![_ * b]mulrC mulrA -mulrA -invfM -!expr2.
  move/eqP : uc; rewrite eq_sym addrC -subr_eq => /eqP <- {b bR}.
  have -> : (1 - a ^+ 2) / (1 - a) ^+ 2 = (1 + a) / (1 - a) by field.
  have idt : 1 + a + (1 - a) != 0.
    by rewrite /= [X in X != 0](_ : _ = 2); first ring.
  field by done.
rewrite ![_ * b]mulrC !mulrA -mulrA -invfM -!expr2.
suff -> : (1 - a) * (b ^+ 2 / (1 - a) / (1 - a) + 1) = 2 by rewrite mulfK.
rewrite mulrDr mulr1 mulrC divfK //.
move/eqP : uc; rewrite eq_sym addrC -subr_eq => /eqP <- {b bR}.
field.
Qed.
Lemma param_inv_inj : {in predI unitcircle (predC1 1) &, injective param_inv}.
Proof. exact/can_in_inj/param_invK. Qed.


Lemma Re_unitcircle z : z \in unitcircle -> 'Re z <= 1 ?= iff (z == 1).
Proof.
move/unitcircleP; rewrite (algCrect z) normC2_Re_Im.
move: ('Re z) ('Im z) (Creal_Re z) (Creal_Im z) => {z} a b aR bR.
rewrite Re_rect // Im_rect // => eq; split.
  apply/negP=> /negP; rewrite -!real_ltNge ?rpredN ?real1 //.
  move/(exprn_egt1 2); rewrite /= -eq gtrDl real_ltNge // ?rpredX //.
  by rewrite -realEsqr bR.
rewrite [RHS]eqC !Re_rect // !Im_rect //.
rewrite (Creal_ReP _ (@real1 _)) (Creal_ImP _ (@real1 _)).
case: eqP => //= eqa; move: eq; rewrite {a aR}eqa.
by rewrite expr1n addrC => /eqP; rewrite -subr_eq0 addrK sqrf_eq0 => ->.
Qed.
Lemma Im_unitcircle z : z \in unitcircle -> 'Im z <= 1 ?= iff (z == 'i).
Proof.
move=> zu; rewrite -(divfK (@neq0Ci _) z) ImMir -{4}(mul1r 'i).
have /rregP/inj_eq -> := @neq0Ci algC.
apply: Re_unitcircle.
by rewrite invCi unitcircleM // unitcircleN unitcirclei.
Qed.

Lemma sgr_param_inv z :
  z \in unitcircle -> sgr (param_inv z : algC) = sgr ('Im z).
Proof.
move=> /Re_unitcircle; rewrite (algCrect z).
move: ('Re z) ('Im z) (Creal_Re z) (Creal_Im z) => {z} a b aR bR.
rewrite /= Re_rect // Im_rect // => [[]].
rewrite le_eqVlt orbC => /orP[/[swap] _ | /eqP->{a aR}].
  by rewrite -subr_gt0 -invr_gt0 => /sgr_mulr ->.
rewrite eqxx addrC -subr_eq0 addrK.
have /lregP/inj_eq <- := @neq0Ci algC.
rewrite mulr0 mulrA mulCii mulNr mul1r oppr_eq0 => /esym/eqP->.
by rewrite mul0r.
Qed.
Lemma param_inv_gt0 z : z \in unitcircle -> (param_inv z > 0) = ('Im z > 0).
Proof.
move/sgr_param_inv; rewrite -sgr_gt0 sgr_algRval -mono_lt_algRval /= => ->.
have := sgr_gt0 (in_algR (Creal_Im z)).
by rewrite -mono_lt_algRval /= -mono_lt_algRval /= -sgr_algRval /=.
Qed.
Lemma param_inv_ge0 z : z \in unitcircle -> (param_inv z >= 0) = ('Im z >= 0).
Proof.
move/sgr_param_inv; rewrite -sgr_ge0 sgr_algRval -mono_le_algRval /= => ->.
have := sgr_ge0 (in_algR (Creal_Im z)).
by rewrite -mono_le_algRval /= -mono_le_algRval /= -sgr_algRval /=.
Qed.

Lemma param_divE (a b : algR) :
  b != a -> param a / param b = param ((a * b + 1) / (b - a)).
Proof.
rewrite !paramE -subr_eq0 /= => neba.
have di := addCi_ne0; have si := subCi_ne0;
have den : \val a * b + 1 + - 'i * (\val b - a) != 0.
  rewrite /= mulNr -mulrN eqC Im_rect ?rpred_simpl //.
  rewrite andbC !raddf0 oppr_eq0.
  by have  /negbTE -> : \val b - \val a != 0 by apply: neba.
field: (@sqrCi algC) by rewrite //=.
Qed.

Lemma param_div (a b : algR) :
  b != a -> param_inv (param a / param b) = (a * b + 1) / (b - a).
Proof. by move/param_divE ->; rewrite paramK. Qed.

Lemma lt_param_div (a b : algR) :
  b < a -> b < param_inv (param b / param a).
Proof.
move=> ltba; rewrite -subr_gt0.
have neqab : a != b by rewrite real_neqr_lt //= ltba orbT.
rewrite param_div //.
rewrite -{3}[b](mulfK (x := a - b)) ?subr_eq0 //.
have {}ltba : 0 < a - b by rewrite subr_gt0.
rewrite -mulrBl mulr_gt0 // ?invr_gt0 // mulrBr.
rewrite opprB addrC addrA subrK.
exact: sqp1_gt0.
Qed.

Lemma param_incr t1 t2 : 0 <= t1 < t2 -> 'Re (param t1) < 'Re (param t2).
Proof.
rewrite !Re_paramE => /andP[le0t1 lt12]; rewrite -subr_gt0.
have le0t2 := ltW (le_lt_trans le0t1 lt12).
rewrite [X in 0 < X](_ : _ = 2*(\val t2^+2 - t1^+2)/(t1^+2 + 1)/(t2^+2 + 1)).
  field by apply: sqp1_ne0.
repeat apply: mulr_gt0 => //; rewrite ?invr_gt0 ?sqp1_gt0 //=.
by rewrite subr_gt0 ltr_sqr.
Qed.


Definition leparam := relpre param_inv >=%R.
Definition ltparam := relpre param_inv >%R.

Lemma leparam_refl : reflexive leparam.
Proof. by move=> a; exact: lexx. Qed.
Lemma leparam_trans : transitive leparam.
Proof. by apply/relpre_trans => a b c /= /(le_trans _) /[apply]. Qed.
Lemma ltparam_trans : transitive ltparam.
Proof. by apply/relpre_trans => a b c /= /(lt_trans _) /[apply]. Qed.


Section Zeta.

Variables (n : nat) (gtn0 : (0 < n)%N).

Definition geomroots :=
  sort leparam (sval (closed_field_poly_normal (geompol n))).
Definition zeta := nth 1 geomroots 0.

Lemma size_geomroots : size geomroots = n.-1.
Proof.
rewrite size_sort /=.
case: closed_field_poly_normal => /= s; rewrite lead_geompol // scale1r.
move=> /(congr1 (fun p : {poly algC} => size p)).
by rewrite size_prod_XsubC size_geompol => -> /=.
Qed.

Lemma geomroots_uniq : uniq geomroots.
Proof.
rewrite sort_uniq.
case: closed_field_poly_normal => /= s; rewrite lead_geompol // scale1r => Heq.
by rewrite -(separable_prod_XsubC s) -Heq separable_geompol.
Qed.

Lemma mem_geomrootsE x : (x \in geomroots) = (root (geompol n) x).
Proof.
rewrite /root /geomroots.
case: closed_field_poly_normal => /= s; rewrite lead_geompol // scale1r => ->.
rewrite mem_sort horner_prod prodf_seq_eq0 /=.
apply/idP/hasP => /=[xins | [y yins]].
  by exists x; rewrite // !hornerE subrr.
by rewrite !hornerE subr_eq0 => /eqP->.
Qed.
Lemma mem_geomroots_unity x : (x \in geomroots) = (n.-unity_root x) && (x != 1).
Proof. by rewrite -root_geompolE // mem_geomrootsE. Qed.

Lemma geomrootsP : all (n.-unity_root) geomroots.
Proof. by apply/allP => /= x; rewrite mem_geomroots_unity => /andP[]. Qed.
Lemma geomroots_unitcircle1 : all (predI unitcircle (predC1 1)) geomroots.
Proof.
apply/allP => /= x; rewrite mem_geomroots_unity.
by move=> /andP[/(unity_root_unitcircle gtn0) + -> /[!andbT]].
Qed.

Lemma geomroots_lesorted : sorted leparam geomroots.
Proof. by apply: sort_sorted => x y; rewrite /ltparam /= real_leVge //=. Qed.
Lemma geomroots_ltsorted : sorted ltparam geomroots.
Proof.
suff: sorted <%R [seq param_inv i | i <- rev geomroots].
  by rewrite map_rev rev_sorted sorted_map /=.
rewrite lt_sorted_uniq_le; apply/andP; split.
  rewrite map_inj_in_uniq ?rev_uniq ?geomroots_uniq //.
  move=> x y; rewrite !mem_rev.
  move=> /(allP geomroots_unitcircle1) H1 /(allP geomroots_unitcircle1) H2.
  exact: param_inv_inj.
rewrite map_rev rev_sorted sorted_map.
set rp := (X in sorted X).
by suff /eq_sorted -> : rp =2 leparam by apply: geomroots_lesorted.
Qed.

Lemma geomrootsXE : geomroots = [seq zeta ^+ i | i <- iota 1 n.-1].
Proof.
apply: (eq_from_nth (x0 := 1)).
  by rewrite size_map size_iota size_geomroots.
move=> i ltin.
rewrite (nth_map 0%N) ?size_iota -?size_geomroots // nth_iota // add1n.
move: i ltin; apply: ltn_ind => [][|b] IH ltb.
  by rewrite expr1; apply: set_nth_default.
have {}IH m : (m < b.+1)%N -> nth 1 geomroots m = zeta ^+ m.+1.
  by move=> /[dup]/ltn_trans/(_ ltb)/IH.
have lt0 : (0 < size geomroots)%N by apply: (ltn_trans _ ltb).
have rootin i : (i < size geomroots)%N
                -> nth 1 geomroots i \in predI unitcircle (predC1 1).
  by move=> lti; apply/(allP geomroots_unitcircle1)/mem_nth.
pose r := nth 1 geomroots b.+1 / zeta.
have eqzeta : nth 1 geomroots b.+1 = r * zeta.
  rewrite divfK // /zeta; apply/negP => /eqP Habs.
  move/(all_nthP 1 geomrootsP): lt0; rewrite {}Habs.
  by rewrite unity_rootE expr0n (negbTE (lt0n_neq0 gtn0)) /= eq_sym oner_eq0.
have rin : r \in geomroots.
  rewrite mem_geomroots_unity; apply/andP; split.
    by apply: rpred_div => //; apply/(all_nthP 1 geomrootsP).
  by apply/negP => /eqP/divr1_eq/eqP; rewrite nth_uniq // geomroots_uniq.
have ltz : ltparam zeta (nth 1 geomroots b.+1).
  by apply: (sorted_ltn_nth ltparam_trans 1 geomroots_ltsorted);
       rewrite //= inE size_geomroots // (ltn_trans _ ltb).
have {ltz rootin}ltr : ltparam r (nth 1 geomroots b.+1).
  by move/lt_param_div: ltz ; rewrite !param_invK ?rootin // => ltp.
have eqb1 : index (nth 1 geomroots b.+1) geomroots = b.+1.
  by apply: index_uniq; rewrite ?geomroots_uniq // size_geomroots.
have {ltr eqb1}ltind : (index r geomroots < b.+1)%N.
  apply/contraLR: ltr; rewrite -leqNgt -{1}eqb1.
  have : nth 1 geomroots b.+1 \in geomroots by apply: mem_nth.
  move/(sorted_leq_index leparam_trans leparam_refl geomroots_lesorted).
  move/(_ _ rin)/[apply].
  by rewrite /leparam /ltparam /= -leNgt.
have:= IH _ ltind; rewrite (nth_index _ rin) => eqr.
move: ltind; rewrite ltnS leq_eqVlt => /orP[/eqP eqind | ltind].
  by rewrite eqzeta eqr eqind -exprSr.
exfalso.
have: nth 1 geomroots b.+1 = nth 1 geomroots (index r geomroots).+1.
  by rewrite {1}eqzeta {1}eqr -exprSr -IH.
move/eqP; rewrite (nth_uniq _ _ _ geomroots_uniq) //=.
  exact/(leq_ltn_trans ltind)/ltnW.
by move: ltind; rewrite eqSS => /[swap]/eqP-> /[!ltnn].
Qed.

(* Stated here as a local lemma to avoid breaking the section *)
Local Lemma zeta1tmp : n = 1%N -> zeta = 1.
Proof. by move=> eqn; rewrite /zeta nth_default // size_geomroots eqn. Qed.
Lemma zeta_in_geomroots : n != 1 -> zeta \in geomroots.
Proof.
move=> neqn1; rewrite /zeta mem_nth // size_geomroots.
by case: n gtn0 neqn1 => // -[|].
Qed.
Lemma zetaP : n.-unity_root zeta.
Proof.
case: (altP (n =P 1)) => [/zeta1tmp -> | neqn1].
  by apply/unity_rootP; rewrite expr1n.
by have:= zeta_in_geomroots neqn1; rewrite mem_geomroots_unity // => /andP[].
Qed.
Lemma zeta_neq1 : n != 1 -> zeta != 1.
Proof. by move/zeta_in_geomroots; rewrite mem_geomroots_unity => /andP[]. Qed.


Lemma zeta_unitcircle : zeta \in unitcircle.
Proof. exact: unity_root_unitcircle gtn0 zetaP. Qed.
Lemma zeta_neq0 : zeta != 0.
Proof. exact/unitcircle_neq0/zeta_unitcircle. Qed.
Lemma zeta_primitive : n.-primitive_root zeta.
Proof.
rewrite /primitive_root_of_unity gtn0 /=; apply/forallP => /= -[i ltin /=].
case: (altP (i.+1 =P n)) => [{i ltin}-> | neq1in]; first by rewrite zetaP.
apply/eqP/(introF idP).
rewrite /root_of_unity /root !hornerE subr_eq0 => /eqP Heq.
suff : 1 \in geomroots by rewrite mem_geomroots_unity // eqxx /= andbF.
rewrite -{}Heq geomrootsXE //; apply: map_f.
by rewrite mem_iota /= add1n prednK // ltn_neqAle neq1in.
Qed.
Lemma Xn_sub_1_prodE : 'X^n - 1 = \prod_(i < n) ('X - (zeta ^+ i)%:P).
Proof. by rewrite -(factor_Xn_sub_1 zeta_primitive) big_mkord. Qed.

Lemma unity_zetaXE z :
  n.-unity_root z -> z != 1 -> exists2 i, (0 < i < n)%N & z = zeta ^+ i.
Proof.
move=> zu zn1.
have : z \in geomroots by rewrite mem_geomroots_unity zu zn1.
rewrite geomrootsXE => /mapP[/= i].
by rewrite mem_iota add1n prednK // => lt0in ->; exists i.
Qed.

(* Stated here as a local lemma to avoid breaking the section *)
Local Lemma zeta2tmp : n = 2%N -> zeta = -1.
Proof.
move=> eqn.
have /zeta_in_geomroots : n != 1 by rewrite eqn.
rewrite mem_geomrootsE // eqn.
have -> : geompol 2 = 'X + 1 :> {poly algC}.
  by rewrite geompolE /index_iota /= big_cons big_seq1 addrC expr0 expr1.
by rewrite root_XaddC => /eqP.
Qed.

Lemma nth_geomroots i : (0 < i < n)%N -> nth 1 geomroots i.-1 = zeta ^+ i.
Proof.
case/andP=> lt01 ltin; rewrite geomrootsXE.
have lti1n1 : (i.-1 < n.-1)%N by rewrite -ltnS !prednK.
by rewrite (nth_map 1) ?size_iota // nth_iota // add1n prednK.
Qed.

Lemma zetaXn_geomroots i : (0 < i < n)%N -> zeta ^+ i \in geomroots.
Proof.
case/andP=> lt0i ltin.
by rewrite geomrootsXE map_f // mem_iota /= lt0i /= add1n prednK.
Qed.
Lemma zetaXn_unitcircle1 i :
  (0 < i < n)%N -> predI unitcircle (predC1 1) (zeta ^+ i).
Proof. by move/zetaXn_geomroots/(allP geomroots_unitcircle1). Qed.
Lemma zetaXn_unitcircle i : (0 < i < n)%N -> unitcircle (zeta ^+ i).
Proof. by move/zetaXn_unitcircle1 => /andP[]. Qed.
Lemma zetaXn_neq1 i : (0 < i < n)%N -> zeta ^+ i != 1.
Proof. by move/zetaXn_unitcircle1 => /andP[]. Qed.

Lemma ltparam_zetaXn :
  {in [pred i | (0 < i < n)%N] &,
        { homo (GRing.exp zeta) : i j / (i < j)%N >-> ltparam i j }}.
Proof.
move=> i j /[!inE]/andP[lt0i ltin]/andP[lt0j ltjn] ltij.
rewrite -!nth_geomroots ?lt0i ?ltin ?lt0j ?ltjn //=.
by apply: (sorted_ltn_nth ltparam_trans 1 geomroots_ltsorted);
  rewrite ?inE ?size_geomroots -ltnS !prednK // (ltn_trans ltij).
Qed.

Lemma zetax_halfn j : j.*2 = n -> zeta ^+ j = -1.
Proof.
move=> eqj2.
have:= zetaP; rewrite unity_rootE -eqj2 -addnn exprD -expr2 sqrf_eq1.
move=> /orP[] /eqP //.
suff: (0 < j < n)%N by move=> /zetaXn_neq1/[swap]-> /= /[!eqxx].
have:= gtn0; rewrite -{}eqj2.
by case: j => // j _ /=; rewrite -addnn addnS ltnS addSn ltnS leq_addr.
Qed.

Lemma Re_zetaXn_le i j :
  (i <= j < n)%N -> 'Im (zeta ^+ j) >= 0 -> 'Im (zeta ^+ i) >= 0.
Proof.
rewrite -!param_inv_ge0 ?unitcircleXn ? zeta_unitcircle //.
rewrite leq_eqVlt; case: eqP => [{j}<- // | _ /=].
case: i => [_ _ | i]; first by rewrite expr0 param_inv1.
move=> /andP[/[dup]ltij /ltn_trans + /[dup]] => /[apply] ltin ltjn.
have := ltparam_zetaXn _ _ ltij; rewrite !inE ltin ltjn !andbT.
move/(_ (ltn0Sn i) (ltn_trans (ltn0Sn i) ltij)) => /= /ltW /[swap].
by move=> /le_trans/[apply].
Qed.

Lemma conj_zetaX i : (i < n)%N -> conjC (zeta ^+ i) = zeta ^+ (n - i).
Proof.
move=> ltin.
have zetaX_neq0 : zeta ^+ i != 0 by rewrite expf_eq0 andbC (negbTE zeta_neq0).
have zetaX_uc := unitcircleXn i zeta_unitcircle.
apply: (lregP zetaX_neq0 _).
rewrite -!exprD (subnKC (ltnW ltin)) -normCK (unity_rootP zetaP).
by rewrite (unitcircleP _ zetaX_uc).
Qed.

Lemma Im_zetaXn_gt0 i : (0 < i < uphalf n)%N -> 0 < 'Im (zeta ^+ i).
Proof.
case/andP=> lt0i ltin2.
have ltin : (i < n)%N.
  by apply: (leq_trans ltin2); rewrite leq_uphalf_double -addnn leq_addr.
rewrite -(oppr_ltr (Creal_Im _)) -Im_conj conj_zetaX //.
have /ltparam_zetaXn ltp : (0 < i < n)%N by rewrite lt0i ltin.
have {}/ltp ltp : (0 < n - i < n)%N.
  by rewrite subn_gt0 ltin /= ltn_psubLR // -{1}(add0n n) ltn_add2r.
have {}/ltp : (i < n - i)%N by rewrite ltn_subRL addnn -gtn_uphalf_double.
rewrite /ltparam /= -conj_zetaX // -mono_lt_algRval /= Re_conj.
suff : 'Re (zeta ^+ i) < 1.
  by rewrite -subr_gt0 -invr_gt0 => /ltr_pM2r ->.
rewrite lt_neqAle andbC.
have [-> -> /=] := Re_unitcircle (unitcircleXn i zeta_unitcircle).
suff : zeta ^+ i \in geomroots by rewrite mem_geomroots_unity => /andP[].
by apply: zetaXn_geomroots; rewrite lt0i ltin.
Qed.
Lemma Im_zetaXn_lt0 i : (n./2 < i < n)%N -> 'Im (zeta ^+ i) < 0.
Proof.
rewrite ltn_half_double => /andP[ltn2i ltin].
rewrite -oppr_gt0 -Im_conj conj_zetaX //.
apply: Im_zetaXn_gt0; rewrite subn_gt0 ltin /=.
rewrite gtn_uphalf_double doubleB ltn_subLR ?leq_double ?(ltnW ltin) //.
by rewrite -addnn ltn_add2r.
Qed.

Lemma Im_zeta_gt0 : (2 < n)%N -> 0 < 'Im zeta.
Proof.
move=> gtn2.
rewrite -(expr1 zeta); apply: Im_zetaXn_gt0.
by rewrite ltnSn /= gtn_uphalf_double -addnn add1n.
Qed.

Lemma Im_zeta_ge0 : 0 <= 'Im zeta.
Proof.
move: gtn0; rewrite leq_eqVlt eq_sym => /orP[/eqP eqn1 | lt1n].
  by rewrite zeta1tmp //= (Creal_ImP _ (@real1 _)).
have:= lt1n; rewrite leq_eqVlt eq_sym => /orP[/eqP eqn2 | lt2n].
  by rewrite zeta2tmp // raddfN  /= (Creal_ImP _ (@real1 _)) oppr0.
exact: (ltW (Im_zeta_gt0 lt2n)).
Qed.

Lemma Re_zetaXnlt i j :
  (i < j <= n./2)%N -> 'Re (zeta ^+ i) > 'Re (zeta ^+ j).
Proof.
case/andP=> ltij.
rewrite geq_half_double => lej2n.
have ltjn : (j < n)%N.
  move: lej2n; rewrite -addnn => /(leq_trans _); apply.
  by rewrite -{1}(add0n j) ltn_add2r (leq_ltn_trans _ ltij).
case: i ltij => [lt0j | i].
  rewrite expr0 (Creal_ReP _ (@real1 _)) lt_neqAle andbC.
  have /Re_unitcircle[-> -> /=]:= unitcircleXn j zeta_unitcircle.
  by apply: zetaXn_neq1; rewrite lt0j ltjn.
move: (i.+1) (ltn0Sn i) => {}i lt0i ltij.
have ltn2n : (uphalf n <= n)%N by rewrite leq_uphalf_double -addnn leq_addr.
have lt0in : (0 < i < n)%N by rewrite lt0i /= (ltn_trans ltij).
have lt0jn : (0 < j < n)%N.
  by rewrite (ltn_trans lt0i ltij) (leq_trans ltjn).
rewrite -(param_invK (zetaXn_unitcircle1 lt0in)).
rewrite -(param_invK (zetaXn_unitcircle1 lt0jn)).
apply: param_incr; apply/andP; split; last exact: ltparam_zetaXn.
rewrite param_inv_ge0 ?unitcircleXn // ?zeta_unitcircle //.
move: lej2n; rewrite leq_eqVlt => /orP[/eqP /zetax_halfn ->|].
  by rewrite raddfN /= (Creal_ImP _ (@real1 _)) oppr0.
rewrite -gtn_uphalf_double => ltjup.
by apply/ltW/Im_zetaXn_gt0; rewrite (ltn_trans lt0i ltij).
Qed.
Lemma Re_zetaXnle i j :
  (i <= j <= n./2)%N -> 'Re (zeta ^+ i) >= 'Re (zeta ^+ j).
Proof.
case/andP=> /[swap] ltjn2; rewrite leq_eqVlt => /orP[/eqP-> // | ltij].
by apply/ltW/Re_zetaXnlt; rewrite ltij.
Qed.

Lemma Re_root_min z : n.-unity_root z -> z != 1 -> 'Re z <= 'Re zeta.
Proof.
move=> /unity_zetaXE/[apply] - [i lt0in {z}->].
wlog ltin2 : i lt0in / (i <= n./2)%N.
  move=> Hwlog; case: (leqP i n./2) => [/(Hwlog _ lt0in) //|].
  rewrite ltn_half_double => ltn2i.
  have /andP[lt0i ltin] := lt0in.
  rewrite -Re_conj conj_zetaX //; apply: Hwlog.
    rewrite subn_gt0 ltin /= ltn_subLR ?(ltnW ltin) //.
    by rewrite -{1}(add0n n) ltn_add2r.
  by rewrite geq_half_double doubleB leq_subLR -addnn leq_add2r (ltnW _).
rewrite -{2}(expr1 zeta); apply/Re_zetaXnle.
by case/andP: lt0in => ->.
Qed.

Lemma eq_zeta z :
  n.-unity_root z -> z != 1 -> 'Im z >= 0 ->
  (forall y, n.-unity_root y -> y != 1 -> 'Re y <= 'Re z) -> z = zeta.
Proof.
have := gtn0; rewrite leq_eqVlt => /orP[ /eqP/esym -> + + _ _| lt1n].
  by rewrite unity_rootE expr1 => /eqP -> /[!eqxx].
move=> zu zn1 Imz Remax.
have [i lt0in eqz] := unity_zetaXE zu zn1.
have eqRe : 'Re z = 'Re zeta.
  apply/le_anti;
  rewrite (Remax _ zetaP (zeta_neq1 _)) ?andbT ?(gtn_eqF lt1n) //.
  by rewrite Re_root_min.
have /eqP : 'Im z ^+2 = 'Im zeta ^+ 2.
  rewrite -[LHS](addrK ('Re z ^+ 2)); apply/eqP; rewrite subr_eq; apply/eqP.
  rewrite [LHS]addrC [RHS]addrC [in RHS]eqRe -!normC2_Re_Im.
  rewrite (unitcircleP _ zeta_unitcircle).
  by rewrite (unitcircleP _ (unity_root_unitcircle gtn0 zu)).
rewrite eqf_sqr => /orP[]// /eqP eqIm.
  by apply/eqP; rewrite eqC eqRe eqIm !eqxx.
have {}Imz : 'Im z = 0.
  by apply le_anti; rewrite Imz eqIm oppr_le0 Im_zeta_ge0.
apply/eqP; rewrite eqC eqRe eqxx Imz /=.
by move/eqP: eqIm; rewrite -eqr_oppLR Imz oppr0.
Qed.

Lemma Im_gt0_eq_zeta z :
  n.-unity_root z -> z != 1 -> 'Im z >= 0 ->
  (forall y, n.-unity_root y -> y != 1 -> Im y >= 0 -> 'Re y <= 'Re z)
  -> z = zeta.
Proof.
move=> zu zn1 Imz Remax; apply: eq_zeta => // y yun yn1.
have:= Creal_Im y; rewrite -comparabler0 => /orP[]; last exact: Remax.
rewrite -oppr_ge0 -Im_conj -(Re_conj y); apply: Remax.
  by rewrite unity_root_conj.
by rewrite -conjC1 (inj_eq (can_inj (@conjCK _))).
Qed.

End Zeta.

Notation "''zeta_' i" := (zeta i) (at level 1, format "''zeta_' i").


Lemma zetaM m n : (0 < m * n)%N -> 'zeta_(m * n) ^+ m = 'zeta_n.
Proof.
move=> /[dup] lt0mn; rewrite muln_gt0 => /andP[lt0m lt0n].
have:= lt0n; rewrite leq_eqVlt eq_sym => /orP[/eqP -> | lt1n].
  by rewrite muln1 [RHS]zeta1tmp //; apply/unity_rootP/zetaP.
apply: Im_gt0_eq_zeta => //.
- by apply/unity_rootP; rewrite -exprM; apply/unity_rootP/zetaP.
- by apply/zetaXn_neq1; rewrite // lt0m /= ltn_Pmulr //.
- move: lt1n; rewrite leq_eqVlt eq_sym => /orP[/eqP -> | lt2n].
    rewrite zetax_halfn ?muln2 ?double_gt0 //.
    by rewrite raddfN /= (Creal_ImP _ (@real1 _)) oppr0.
  apply/ltW/Im_zetaXn_gt0; rewrite // lt0m /= gtn_uphalf_double.
  by rewrite -muln2 ltn_mul2l lt0m lt2n.
move=> y yun neqy1.
have /(unity_zetaXE lt0mn) : (m * n).-unity_root y.
  by apply/unity_rootP; rewrite mulnC exprM (unity_rootP yun) expr1n.
case/(_  neqy1) => k /andP[lt0k ltkmn] /[dup]eqy -> le0Im.
case: (leqP k (m * n)./2) => [lekmn2 | ltmn2k]; first last.
  exfalso.
  have /(Im_zetaXn_lt0 lt0mn) : ((m * n)./2 < k < m * n)%N by rewrite ltmn2k.
  by move/(le_lt_trans le0Im); rewrite ltxx.
apply: Re_zetaXnle; rewrite // lekmn2 andbT.
apply: (dvdn_leq lt0k); rewrite -(dvdn_pmul2r lt0n).
rewrite (prim_order_dvd (zeta_primitive lt0mn)).
by rewrite exprM -eqy -unity_rootE yun.
Qed.

Lemma Re_zeta_lt m n : (1 < m < n)%N -> 'Re 'zeta_m < 'Re 'zeta_n.
Proof.
case/andP=> lt1m ltmn; have lt0m := ltn_trans (ltnSn 0) lt1m.
have lt0n := ltn_trans lt0m ltmn.
have le0mn : (0 < m * n)%N by rewrite muln_gt0 lt0m lt0n.
have := le0mn; rewrite mulnC -(zetaM le0mn) => /zetaM <- /[!(mulnC n)].
apply: Re_zetaXnlt; rewrite // ltmn /=.
by rewrite geq_half_double -muln2 mulnC leq_pmul2r.
Qed.


Lemma zeta1 : 'zeta_1 = 1.  Proof. exact: zeta1tmp. Qed.
Lemma zeta2 : 'zeta_2 = -1. Proof. exact: zeta2tmp. Qed.
Lemma zeta3 : 'zeta_3 = -1 / 2 + 'i * (sqrtC 3 / 2).
Proof.
set j : algC := (RHS).
have addjjC : - (j + conjC j) = 1.
  apply/eqP; rewrite eqr_oppLR; apply/eqP.
  rewrite -[LHS](mulfK neq20) mulrDl -{2}(@conj_Creal _ 2) // -rmorphM /=.
  by rewrite -ReE /j mulrA -mulrDl divfK // Re_rect // ?rpred_simpl // sqrtC_real.
have prodjjC : j * conjC j = 1.
  rewrite -normCK /j normC2_rect ?rpred_simpl ?sqrtC_real //.
  field: (@sqrtCK algC 3).
have {addjjC prodjjC}gpol3E : geompol 3%N = ('X - j%:P) * ('X - j^*%:P).
  rewrite geompolE /index_iota /= 2!big_cons big_seq1 expr0 expr1.
  rewrite -polyC1 -prodjjC -/j -{1}['X]mulr1 -polyC1 -addjjC -/j.
  rewrite rmorphM raddfN raddfD /=; ring.
have {gpol3E} root3 (z : algC) : root (geompol 3%N) z = (z == j) || (z == j^*).
  by rewrite gpol3E rootM !root_XsubC.
have : 'zeta_3 \in geomroots 3 by apply zeta_in_geomroots.
rewrite mem_geomrootsE // root3 => /orP[/eqP //| /eqP Habs].
exfalso; have : 'Im j > 0.
  rewrite /j Im_rect ?rpred_simpl // ?sqrtC_real //.
  by apply: divr_gt0 => //; rewrite sqrtC_gt0.
by rewrite -oppr_lt0 -Im_conj -Habs real_ltNge // Im_zeta_ge0.
Qed.
Lemma zeta4 : 'zeta_4 = 'i.
Proof.
have /eqP : 'zeta_4 ^+ 2 = 'i ^+ 2.
  by rewrite -[4%N]/(2 * 2)%N zetaM // zeta2 sqrCi.
rewrite eq_sym eqf_sqr => /orP[/eqP -> // | /eqP Habs].
exfalso; have : 'Im ('i : algC) > 0 by rewrite Im_i.
by rewrite Habs raddfN /= oppr_gt0 real_ltNge // Im_zeta_ge0.
Qed.
Lemma Re_zeta_gt0 n : (4 < n)%N -> 0 < 'Re 'zeta_n.
Proof. by move=> gtn4; rewrite -Re_i -zeta4 Re_zeta_lt. Qed.
Lemma zeta6 : 'zeta_6 = 1 / 2 + 'i * (sqrtC 3 / 2).
Proof.
transitivity (- 'zeta_3 ^*); first last.
  rewrite zeta3 rmorphD !rmorphM /= [(2^-1)^*](CrealP _) ?rpred_simpl //.
  rewrite raddfD raddfN /=  conjC1 -mulNr !opprK.
  by rewrite conjCi mulNr opprK (CrealP (sqrtC_real _)).
rewrite -in_unitycircleV ?zeta_unitcircle //.
apply: (rregP (@zeta_neq0 3 _)) => //.
rewrite mulNr [in RHS]mulrC divff ?(@zeta_neq0 3 _) //.
have /zetaM <- : (0 < 2 * 3)%N by [].
rewrite -[X in X * _]expr1 -[6%N]/(2 * 3)%N -exprD -[(1 + 2)%N]/3%N.
by rewrite mulnC zetaM // zeta2.
Qed.
Lemma zeta8 : 'zeta_8 = sqrtC 2 / 2 + 'i * (sqrtC 2 / 2).
Proof.
set r : algC := (RHS).
have /eqP : r ^+ 2 = 'zeta_8 ^+ 2.
  rewrite -[8%N]/(2 * 4)%N zetaM // zeta4 /r.
  by rewrite expr2 mulC_rect; field : (@sqrtCK algC 2).
rewrite eqf_sqr => /orP[/eqP -> // | /eqP Habs].
exfalso; have : 'Im r > 0.
  rewrite /r Im_rect ?rpred_simpl // ?sqrtC_real //.
  by apply: divr_gt0 => //; rewrite sqrtC_gt0.
by rewrite Habs raddfN /= oppr_gt0 real_ltNge // Im_zeta_ge0.
Qed.
Lemma zeta12 : 'zeta_12 = sqrtC 3 / 2 + 'i / 2.
Proof.
set r : algC := (RHS).
have /eqP : r ^+ 2 = 'zeta_12 ^+ 2.
  rewrite -[12%N]/(2 * 6)%N zetaM // zeta6 /r.
  by rewrite expr2 mulC_rect; field : (@sqrtCK algC 3).
rewrite eqf_sqr => /orP[/eqP -> // | /eqP Habs].
exfalso; have : 'Im r > 0.
  by rewrite /r Im_rect ?rpred_simpl // ?sqrtC_real // invr_gt0 //.
by rewrite Habs raddfN /= oppr_gt0 real_ltNge // Im_zeta_ge0.
Qed.

Lemma zeta5 : 'zeta_5 = (sqrtC 5 - 1) / 4 + 'i * (sqrtC (10 + 2 * sqrtC 5) / 4).
Proof.
have z5n0 : 'zeta_5 != 0 by rewrite zeta_neq0.
have : 'zeta_5 \in geomroots 5 by apply zeta_in_geomroots.
rewrite mem_geomrootsE // geompolE /index_iota /= 4!big_cons big_seq1.
rewrite /root !hornerE /= expr0 expr1 => /eqP zeq.
have {zeq} : ('zeta_5 ^+ 2 + 'zeta_5 ^- 2) + ('zeta_5 + 'zeta_5 ^- 1) + 1 = 0.
  have := z5n0; rewrite -sqrf_eq0 => /lregP; apply.
  by rewrite mulr0 -{}zeq !mulrDr -!exprD; field by assumption.
set r : algC := 'zeta_5 + 'zeta_5 ^- 1 => req.
have eqrC : r = 2 * 'Re 'zeta_5.
  by rewrite ReE mulrC divfK // /r in_unitycircleV // expr1 zeta_unitcircle.
have rreal : r \is real_num by rewrite eqrC rpredM ?realn.
have gtr0 : r > 0 by rewrite eqrC mulr_gt0 // Re_zeta_gt0.
pose P : {poly algC} := Poly [:: -1; 1; 1].
have {}req : root P r.
  apply/eqP; move: req.
  have -> : 'zeta_5 ^+ 2 + 'zeta_5 ^- 2 = r ^+ 2 - 2 by rewrite /r; field.
  rewrite /P !hornerE /r /= => <-; ring.
have szP : size P = 3%N.
  rewrite /P /Poly /= !size_cons_poly oppr_eq0 oner_eq0 !andbF /=.
  by rewrite size_polyC eqxx /=.
have {szP} /(NumClosedMonic.deg2_poly_factor szP) eqP : P \is monic.
  by rewrite monicE lead_coefE szP /= /P coef_Poly.
move: req; rewrite {}eqP /P !coef_Poly /= {P}.
rewrite rootM !root_XsubC expr1n mulrN1 opprK -[1 + 4]/5 => /orP[] /eqP eqr.
  exfalso; move: gtr0; apply/negP; rewrite -!real_leNgt //.
  by rewrite {}eqr -opprD mulNr oppr_le0 divr_ge0 // addr_ge0 // sqrtC_ge0.
have eq4 : 4 = 2 * 2 :> algC by ring.
have {r eqr gtr0 rreal eqrC} rez5 : 'Re 'zeta_5 = (sqrtC 5 - 1) / 4.
  by rewrite eq4 invfM // mulrA addrC -eqr eqrC -mulrA mulrC divfK.
rewrite (algCrect 'zeta_5) rez5 -mulrA; congr (_ + 'i * _).
have /eqP : ('Im 'zeta_5) ^+ 2 = (sqrtC (10 + 2 * sqrtC 5) / 4) ^+ 2.
  have /eqP := normC2_Re_Im 'zeta_5.
  rewrite (unitcircleP _ (zeta_unitcircle _)) // addrC -subr_eq => /eqP <-.
  by rewrite expr_div_n sqrtCK rez5; field: (@sqrtCK algC 5).
rewrite eqf_sqr => /orP[] /eqP // Habs; exfalso.
have gts0 : 0 < 10 + 2 * sqrtC 5 :> algC.
  by rewrite addr_gt0 // mulr_gt0 // sqrtC_gt0.
have : 'Im 'zeta_5 >= 0 by rewrite Im_zeta_ge0.
rewrite {}Habs; apply/negP; rewrite -!real_ltNge // ?rpred_simpl //=.
  exact: (sqrtC_real (ltW gts0)).
by rewrite oppr_lt0 mulr_gt0 ?invr_gt0 // sqrtC_gt0.
Qed.
