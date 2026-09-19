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


Local Lemma neq20 : 2 != 0 :> algC.
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


Section ConjRoot.

Context {R : numClosedFieldType}.
Implicit Type (x y z : R).

Lemma unity_root_conj n (x : R) : n.-unity_root x^* = n.-unity_root x.
Proof.
rewrite !unity_rootE -rmorphXn /= -[in LHS]conjC1 inj_eq //.
exact: (can_inj (@conjCK R)).
Qed.

End ConjRoot.


Definition unit_circle : pred algC := [pred z : algC | `|z| ^+ 2 == 1].
Local Abbreviation unit_circleC1 := (predI unit_circle (predC1 1)).


Section UnitCircle.

Implicit Type (y z : algC) (t : algR).

Lemma unit_circleE z : (z \in unit_circle) = (`|z| ^+ 2 == 1).
Proof. by []. Qed.
Lemma unit_circleP z : reflect (`|z| ^+ 2 = 1) (z \in unit_circle).
Proof. exact: (iffP eqP). Qed.
Lemma unit_circle_neq0 z : z \in unit_circle -> z != 0.
Proof.
move/unit_circleP => Heq; apply/negP => /eqP eqz.
move: Heq; rewrite eqz normr0 expr2 mulr0 => /esym/eqP.
by rewrite oner_eq0.
Qed.
Lemma unit_circle1 : 1 \in unit_circle.
Proof. by rewrite unit_circleE normr1 expr1n. Qed.
Lemma unit_circleCi : 'i \in unit_circle.
Proof. by rewrite unit_circleE normCi expr1n. Qed.
Lemma unit_circleN z : (-z \in unit_circle) = (z \in unit_circle).
Proof. by rewrite !unit_circleE normrN. Qed.

Lemma unit_circleM y z :
  y \in unit_circle -> z \in unit_circle -> (y * z) \in unit_circle.
Proof.
move=> /unit_circleP ny /unit_circleP nz.
by apply/unit_circleP; rewrite normrM exprMn ny nz mulr1.
Qed.
Lemma unit_circleV z : (z ^-1 \in unit_circle) = (z \in unit_circle).
Proof. by rewrite !unit_circleE normfV exprVn invr_eq1. Qed.
Lemma unit_circleXn z n : z \in unit_circle -> z ^+ n \in unit_circle.
Proof.
move=> cz; elim: n => [|n IHn]; first by rewrite expr0 unit_circle1.
by rewrite exprS unit_circleM ?cz.
Qed.
Lemma unit_circleXn1 z n : z ^+ n.+1 \in unit_circle -> z \in unit_circle.
Proof.
by rewrite !unit_circleE normrX exprAC pexpr_eq1 // -realEsqr normr_real.
Qed.

Lemma unit_circleXNn z n : z \in unit_circle -> (z ^- n) \in unit_circle.
Proof. by rewrite unit_circleV => cz; exact/unit_circleXn. Qed.

Lemma unity_root_unit_circle n z :
  (0 < n)%N -> n.-unity_root z -> z \in unit_circle.
Proof.
rewrite /root_of_unity /root !hornerE subr_eq0 => gtn0.
move/eqP/(congr1 normr)/eqP; rewrite normr1 normrX pexpr_eq1 // => /eqP nz.
by apply/unit_circleP; rewrite nz expr1n.
Qed.

Lemma in_unit_circleV z : z \in unit_circle -> z^-1 = z^*.
Proof.
move=> /[dup] /unit_circleP zu /unit_circle_neq0/[dup] nz0 /lregP; apply.
by rewrite divff // -normCK zu.
Qed.

Lemma Re_unit_circle z : z \in unit_circle -> 'Re z <= 1 ?= iff (z == 1).
Proof.
move/unit_circleP; rewrite (algCrect z) normC2_Re_Im.
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
Lemma Im_unit_circle z : z \in unit_circle -> 'Im z <= 1 ?= iff (z == 'i).
Proof.
move=> zu; rewrite -(divfK (@neq0Ci _) z) ImMir -{4}(mul1r 'i).
have /rregP/inj_eq -> := @neq0Ci algC.
apply: Re_unit_circle.
by rewrite invCi unit_circleM // unit_circleN unit_circleCi.
Qed.


(** We parametrize the unit circle / {1} through the stereographic projection *)
(** to the imaginary axis.                                                    *)
(* \val = algRval is the injection algR -> algC *)
Lemma stereo_proj_subproof z : 'Im z / (1 - 'Re z) \is real_num.
Proof.
apply: rpredM => /=; first exact: Creal_Im.
by rewrite rpredV rpredB //= real1.
Qed.
Definition unit_circle_param t : algC :=
  \val ((t ^+ 2 - 1) / (t ^+ 2 + 1)) + 'i * \val ((2 * t) / (t ^+ 2 + 1)).
Definition stereo_proj z : algR := in_algR (stereo_proj_subproof z).

Lemma Re_unit_circle_paramE t :
  'Re (unit_circle_param t) = (t ^+ 2 - 1) / (t ^+ 2 + 1).
Proof. exact/Re_rect/algRvalP. Qed.
Lemma Im_unit_circle_paramE t :
  'Im (unit_circle_param t) = (2 * t) / (t ^+ 2 + 1).
Proof. exact/Im_rect/algRvalP. Qed.

Lemma sqp1_gt0 t : \val (t ^+ 2 + 1) > 0.
Proof.
apply: (lt_le_trans ltr01); rewrite -{1}(add0r 1); apply: lerD => //.
by rewrite -realEsqr.
Qed.
Lemma sqp1_ne0 t : \val (t ^+ 2 + 1) !=  0.
Proof. exact: (lt0r_neq0 (sqp1_gt0 t)). Qed.
Lemma addCi_ne0 t : \val t + 'i != 0.
Proof.
apply/negP => /eqP/(congr1 (fun z => 'Im z))/eqP; rewrite raddfD /=.
have /Creal_ImP -> := algRvalP t.
by rewrite add0r raddf0 Im_i oner_eq0.
Qed.
Lemma subCi_ne0 t : \val t - 'i != 0.
Proof. by rewrite -conjC_eq0 raddfB /= conjCi opprK conj_Creal ?addCi_ne0. Qed.

Lemma unit_circle_paramE t : unit_circle_param t = (\val t + 'i) / (\val t - 'i).
Proof.
rewrite /unit_circle_param.
have tin0 : \val t - 'i != 0.
  apply/negP => /eqP/(congr1 (fun z => 'Im z))/eqP; rewrite raddfB /=.
  have /Creal_ImP -> := algRvalP t.
  by rewrite add0r raddf0 Im_i oppr_eq0 oner_eq0.
field: (@sqrCi algC) by rewrite //= sqp1_ne0.
Qed.

Lemma stereo_proj1 : stereo_proj 1 = 0.
Proof. by apply val_inj; rewrite /= (Creal_ReP _ _) //= subrr invr0 mulr0. Qed.
Lemma stereo_proj_conjC z : stereo_proj (z^*) = - stereo_proj z.
Proof. by apply val_inj; rewrite /= Re_conj Im_conj mulNr. Qed.

Lemma unit_circle_paramP t : unit_circle_param t \in unit_circle.
Proof.
rewrite /unit_circle_param unit_circleE normC2_rect ?algRvalP //.
by apply/eqP; field by rewrite sqp1_ne0.
Qed.

Lemma unit_circle_paramK : cancel unit_circle_param stereo_proj.
Proof.
move=> t; apply val_inj; rewrite /= Re_unit_circle_paramE Im_unit_circle_paramE.
have den1 := sqp1_ne0 t.
have den2 : t ^+ 2 + 1 - (t ^+ 2 + -1) != 0 :> algC.
  by rewrite /= [X in X != 0](_ : _ = 2); first ring.
field by done.
Qed.

Lemma stereo_projK : {in unit_circleC1, cancel stereo_proj unit_circle_param}.
Proof.
move=> z; rewrite !inE => /andP[/unit_circleP].
rewrite {2 4}(algCrect z) normC2_Re_Im /unit_circle_param /stereo_proj /=.
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
Lemma stereo_proj_inj : {in unit_circleC1 &, injective stereo_proj}.
Proof. exact/can_in_inj/stereo_projK. Qed.

Lemma sgr_stereo_proj z :
  z \in unit_circle -> sgr (\val (stereo_proj z)) = sgr ('Im z).
Proof.
move=> /Re_unit_circle; rewrite (algCrect z).
move: ('Re z) ('Im z) (Creal_Re z) (Creal_Im z) => {z} a b aR bR.
rewrite /= Re_rect // Im_rect // => [[]].
rewrite le_eqVlt orbC => /orP[/[swap] _ | /eqP->{a aR}].
  by rewrite -subr_gt0 -invr_gt0 => /sgr_mulr ->.
  rewrite eqxx addrC -subr_eq0 addrK.
have /lregP/inj_eq <- := @neq0Ci algC.
rewrite mulr0 mulrA mulCii mulNr mul1r oppr_eq0 => /esym/eqP->.
by rewrite mul0r.
Qed.
Lemma stereo_proj_gt0 z :
  z \in unit_circle -> (stereo_proj z > 0) = ('Im z > 0).
Proof.
move/sgr_stereo_proj; rewrite -sgr_gt0 sgr_algRval -mono_lt_algRval /= => ->.
have := sgr_gt0 (in_algR (Creal_Im z)).
by rewrite -mono_lt_algRval /= -mono_lt_algRval /= -sgr_algRval /=.
Qed.
Lemma stereo_proj_ge0 z :
  z \in unit_circle -> (stereo_proj z >= 0) = ('Im z >= 0).
Proof.
move/sgr_stereo_proj; rewrite -sgr_ge0 sgr_algRval -mono_le_algRval /= => ->.
have := sgr_ge0 (in_algR (Creal_Im z)).
by rewrite -mono_le_algRval /= -mono_le_algRval /= -sgr_algRval /=.
Qed.

Lemma unit_circle_param_divE (a b : algR) :
  b != a ->
  unit_circle_param a / unit_circle_param b
  = unit_circle_param ((a * b + 1) / (b - a)).
Proof.
rewrite !unit_circle_paramE -subr_eq0 /= => neba.
have di := addCi_ne0; have si := subCi_ne0;
have den : \val a * b + 1 + - 'i * (\val b - a) != 0.
  rewrite /= mulNr -mulrN eqC Im_rect ?rpred_simpl //.
  rewrite andbC !raddf0 oppr_eq0.
  by have  /negbTE -> : \val b - \val a != 0 by apply: neba.
field: (@sqrCi algC) by rewrite //=.
Qed.

Lemma stereo_proj_div (y z : algC) :
  unit_circleC1 y -> unit_circleC1 z -> y != z ->
  stereo_proj (y / z)
  = (stereo_proj y * stereo_proj z + 1) / (stereo_proj z - stereo_proj y).
Proof.
move=> /[dup] yu /stereo_projK {2}<- /[dup] zu /stereo_projK {2}<- Hdiff.
rewrite unit_circle_param_divE ?unit_circle_paramK //.
by apply/contra: Hdiff => /eqP/stereo_proj_inj->.
Qed.

Lemma lt_stereo_proj_div (y z : algC) :
  unit_circleC1 y -> unit_circleC1 z ->
  stereo_proj y < stereo_proj z -> stereo_proj y < stereo_proj (y / z).
Proof.
move=> /stereo_proj_div/[apply]/[swap] ltpryz ->.
  by apply/contraL: ltpryz => /eqP->; rewrite ltxx.
move: (_ y) (_ z) ltpryz => b a ltba; rewrite -subr_gt0.
have neqab : a != b by rewrite real_neqr_lt //= ltba orbT.
rewrite -{3}[b](mulfK (x := a - b)) ?subr_eq0 //.
have {}ltba : 0 < a - b by rewrite subr_gt0.
rewrite -mulrBl mulr_gt0 // ?invr_gt0 // mulrBr.
rewrite opprB addrC addrA subrK.
exact: sqp1_gt0.
Qed.

Lemma Re_stereo_proj_incr y z :
  unit_circleC1 y -> unit_circleC1 z ->
  0 <= stereo_proj y < stereo_proj z -> 'Re y < 'Re z.
Proof.
move=> yu zu.
rewrite -{3}(stereo_projK yu) -{2}(stereo_projK zu) !Re_unit_circle_paramE.
move: (_ y) (_ z) => a b /andP[le0a ltab]; rewrite -subr_gt0.
have le0b := ltW (le_lt_trans le0a ltab).
rewrite [X in 0 < X](_ : _ = 2*(\val b^+2 - a^+2)/(a^+2 + 1)/(b^+2 + 1)).
  field by apply: sqp1_ne0.
repeat apply: mulr_gt0 => //; rewrite ?invr_gt0 ?sqp1_gt0 //=.
by rewrite subr_gt0 ltr_sqr.
Qed.


Definition ge_stereo_proj := relpre stereo_proj >=%R.
Definition gt_stereo_proj := relpre stereo_proj >%R.

Lemma ge_stereo_proj_refl : reflexive ge_stereo_proj.
Proof. by move=> a; exact: lexx. Qed.
Lemma ge_stereo_proj_trans : transitive ge_stereo_proj.
Proof. by apply/relpre_trans => a b c /= /(le_trans _) /[apply]. Qed.
Lemma gt_stereo_proj_trans : transitive gt_stereo_proj.
Proof. by apply/relpre_trans => a b c /= /(lt_trans _) /[apply]. Qed.

End UnitCircle.


(** Hide some implementation details *)
Module Type UnityRootSig.

Parameter zeta : nat -> algC.

Axiom zetaP : forall n, (0 < n)%N -> n.-unity_root (zeta n).
Axiom unity_root_zetaXE :
  forall n : nat, (0 < n)%N ->
  forall z : algC, n.-unity_root z -> z != 1 ->
    exists2 i : nat, (0 < i < n)%N & z = zeta n ^+ i.
Axiom zetaXn_unit_circleC1 :
  forall n i, (0 < i < n)%N -> zeta n ^+ i \in unit_circleC1.
Axiom gt_stereo_proj_zetaXn :
  forall n, {in [pred i | (0 < i < n)%N] &,
         {homo GRing.exp (zeta n) : i j / (i < j)%N >-> gt_stereo_proj i j}}.

End UnityRootSig.

Module UnityRoot : UnityRootSig.
Section Zeta.

Variables (n : nat) (gtn0 : (0 < n)%N).
Implicit Type (x y z : algC).

Let neqn0 : (n%:R != 0 :> algC). Proof. by rewrite pnatr_eq0 -lt0n. Qed.

Definition unity_roots :=
  sort ge_stereo_proj
    (filter (predC (pred1 1)) (sval (closed_field_poly_normal ('X ^+ n - 1)))).
Definition zeta := nth 1 unity_roots 0.

Lemma unity_roots_uniq : uniq unity_roots.
Proof.
rewrite sort_uniq.
case: closed_field_poly_normal => /= s.
rewrite (monicP (monicXnsubC 1 gtn0)) scale1r => Heq.
apply: filter_uniq.
by rewrite -(separable_prod_XsubC s) -Heq separable_Xn_sub_1.
Qed.

Lemma mem_unity_roots x : (x \in unity_roots) = (n.-unity_root x) && (x != 1).
Proof.
rewrite mem_sort.
case: closed_field_poly_normal => /= s.
rewrite (monicP (monicXnsubC 1 gtn0)) scale1r => Heq.
by rewrite mem_filter /= andbC -root_prod_XsubC -Heq.
Qed.

Lemma size_unity_roots : size unity_roots = n.-1.
Proof.
rewrite size_sort /=.
case: closed_field_poly_normal => /= s.
rewrite (monicP (monicXnsubC 1 gtn0)) scale1r => Heq.
have suniq : uniq s by rewrite -separable_prod_XsubC -Heq separable_Xn_sub_1.
have /(congr1 (fun p : {poly algC} => size p)) := Heq.
rewrite size_prod_XsubC size_XnsubC // => -[->].
rewrite size_filter -(count_predC (pred1 1)) count_uniq_mem //.
suff -> : 1 \in s by rewrite add1n.
by rewrite -root_prod_XsubC -Heq /root !hornerE expr1n subrr.
Qed.

Lemma unity_rootsP : all (n.-unity_root) unity_roots.
Proof. by apply/allP => /= x; rewrite mem_unity_roots => /andP[]. Qed.
Lemma unity_roots_circleC1 : all unit_circleC1 unity_roots.
Proof.
apply/allP => /= x; rewrite mem_unity_roots.
by move=> /andP[/(unity_root_unit_circle gtn0) + -> /[!andbT]].
Qed.

Lemma unity_roots_lesorted : sorted ge_stereo_proj unity_roots.
Proof. by apply: sort_sorted => x y; rewrite real_leVge /=. Qed.
Lemma unity_roots_ltsorted : sorted gt_stereo_proj unity_roots.
Proof.
suff: sorted <%R [seq stereo_proj i | i <- rev unity_roots].
  by rewrite map_rev rev_sorted sorted_map /=.
rewrite lt_sorted_uniq_le; apply/andP; split.
  rewrite map_inj_in_uniq ?rev_uniq ?unity_roots_uniq //.
  move=> x y; rewrite !mem_rev.
  move=> /(allP unity_roots_circleC1) H1 /(allP unity_roots_circleC1) H2.
  exact: stereo_proj_inj.
rewrite map_rev rev_sorted sorted_map.
set rp := (X in sorted X).
by suff /eq_sorted -> : rp =2 ge_stereo_proj by apply: unity_roots_lesorted.
Qed.

Lemma unity_rootsXE : unity_roots = [seq zeta ^+ i | i <- iota 1 n.-1].
Proof.
apply: (eq_from_nth (x0 := 1)).
  by rewrite size_map size_iota size_unity_roots.
move=> i ltin.
rewrite (nth_map 0%N) ?size_iota -?size_unity_roots // nth_iota // add1n.
move: i ltin; apply: ltn_ind => [][|b] IH ltb.
  by rewrite expr1; apply: set_nth_default.
have {}IH m : (m < b.+1)%N -> nth 1 unity_roots m = zeta ^+ m.+1.
  by move=> /[dup]/ltn_trans/(_ ltb)/IH.
have lt0 : (0 < size unity_roots)%N by apply: (ltn_trans _ ltb).
have rootin i : (i < size unity_roots)%N
                -> nth 1 unity_roots i \in unit_circleC1.
  by move=> lti; apply/(allP unity_roots_circleC1)/mem_nth.
pose r : algC := nth 1 unity_roots b.+1 / zeta.
have eqzeta : nth 1 unity_roots b.+1 = r * zeta.
  rewrite divfK // /zeta; apply/negP => /eqP Habs.
  move/(all_nthP 1 unity_rootsP): lt0; rewrite {}Habs.
  by rewrite unity_rootE expr0n (negbTE (lt0n_neq0 gtn0)) /= eq_sym oner_eq0.
have rin : r \in unity_roots.
  rewrite mem_unity_roots; apply/andP; split.
    by apply: rpred_div => //; apply/(all_nthP 1 unity_rootsP).
  by apply/negP => /eqP/divr1_eq/eqP; rewrite nth_uniq // unity_roots_uniq.
have gtz : stereo_proj zeta > stereo_proj (nth 1 unity_roots b.+1).
  by apply: (sorted_ltn_nth gt_stereo_proj_trans 1 unity_roots_ltsorted);
       rewrite //= inE size_unity_roots // (ltn_trans _ ltb).
have {gtz rootin}gtr : stereo_proj r > stereo_proj (nth 1 unity_roots b.+1).
  by apply: lt_stereo_proj_div => //; apply: rootin.
have eqb1 : index (nth 1 unity_roots b.+1) unity_roots = b.+1.
  by apply: index_uniq; rewrite ?unity_roots_uniq // size_unity_roots.
have {gtr eqb1}ltind : (index r unity_roots < b.+1)%N.
  apply/contraLR: gtr; rewrite -leqNgt -{1}eqb1.
  have : nth 1 unity_roots b.+1 \in unity_roots by apply: mem_nth.
  move/(sorted_leq_index
          ge_stereo_proj_trans ge_stereo_proj_refl unity_roots_lesorted).
  move/(_ _ rin)/[apply].
  by rewrite /ge_stereo_proj /gt_stereo_proj /= -leNgt.
have:= IH _ ltind; rewrite (nth_index _ rin) => eqr.
move: ltind; rewrite ltnS leq_eqVlt => /orP[/eqP eqind | ltind].
  by rewrite eqzeta eqr eqind -exprSr.
exfalso.
have: nth 1 unity_roots b.+1 = nth 1 unity_roots (index r unity_roots).+1.
  by rewrite {1}eqzeta {1}eqr -exprSr -IH.
move/eqP; rewrite (nth_uniq _ _ _ unity_roots_uniq) //=.
  exact/(leq_ltn_trans ltind)/ltnW.
by move: ltind; rewrite eqSS => /[swap]/eqP-> /[!ltnn].
Qed.

(* Stated here as a local lemma to avoid breaking the section *)
Local Lemma zeta1 : n = 1%N -> zeta = 1.
Proof. by move=> eqn; rewrite /zeta nth_default // size_unity_roots eqn. Qed.
Lemma zeta_in_unity_roots : n != 1 -> zeta \in unity_roots.
Proof.
move=> neqn1; rewrite /zeta mem_nth // size_unity_roots.
by case: n gtn0 neqn1 => // -[|].
Qed.
Lemma zetaP : n.-unity_root zeta.
Proof.
case: (altP (n =P 1)) => [/zeta1 -> | neqn1].
  by apply/unity_rootP; rewrite expr1n.
by have:= zeta_in_unity_roots neqn1; rewrite mem_unity_roots // => /andP[].
Qed.

Lemma unity_root_zetaXE z :
  n.-unity_root z -> z != 1 -> exists2 i, (0 < i < n)%N & z = zeta ^+ i.
Proof.
move=> zu zn1.
have : z \in unity_roots by rewrite mem_unity_roots zu zn1.
rewrite unity_rootsXE => /mapP[/= i].
by rewrite mem_iota add1n prednK // => lt0in ->; exists i.
Qed.

End Zeta.

Lemma zetaXn_unit_circleC1 n i :
  (0 < i < n)%N -> zeta n ^+ i \in unit_circleC1.
case/andP=> lt0i ltin; have gt0n := ltn_trans lt0i ltin.
have : zeta n ^+ i \in unity_roots n.
  by rewrite unity_rootsXE //; apply: map_f; rewrite mem_iota; lia.
by move=> /(allP (unity_roots_circleC1 gt0n)).
Qed.
Lemma gt_stereo_proj_zetaXn n :
  {in [pred i | (0 < i < n)%N] &,
         {homo GRing.exp (zeta n) : i j / (i < j)%N >-> gt_stereo_proj i j}}.
Proof.
have nth_ur k : (0 < k < n)%N -> nth 1 (unity_roots n) k.-1 = (zeta n) ^+ k.
  case/andP=> lt0k ltkn; rewrite unity_rootsXE; first by lia.
  have lti1n1 : (k.-1 < n.-1)%N by lia.
  by rewrite (nth_map 1) ?size_iota // nth_iota // add1n prednK.
move=> i j /[!inE] lt0in lt0jn ltij; rewrite -!nth_ur //=.
have /unity_roots_ltsorted : (0 < n)%N by lia.
move/(sorted_ltn_nth gt_stereo_proj_trans).
by apply; rewrite ?inE ?size_unity_roots //; lia.
Qed.

End UnityRoot.
Export UnityRoot.
Notation "''zeta_' i" := (zeta i) (at level 1, format "''zeta_' i").


Lemma zetaXn_neq1 n i : (0 < i < n)%N -> zeta n ^+ i != 1.
Proof. by move=> /zetaXn_unit_circleC1 /[!inE] => /andP[]. Qed.


Section Zeta.

Variables (n : nat) (gtn0 : (n > 0)%N).

Lemma zeta_unit_circle : 'zeta_n \in unit_circle.
Proof. exact/(unity_root_unit_circle gtn0)/zetaP. Qed.

Lemma zeta_neq0 : 'zeta_n != 0.
Proof. exact/unit_circle_neq0/zeta_unit_circle. Qed.

Lemma zeta_primitive : n.-primitive_root 'zeta_n.
Proof.
rewrite /primitive_root_of_unity gtn0 /=; apply/forallP => /= -[i ltin /=].
case: (altP (i.+1 =P n)) => [{i ltin}-> | neq1in]; first by rewrite zetaP.
rewrite /root_of_unity /root !hornerE subr_eq0.
by rewrite (negbTE (zetaXn_neq1 _)) //= ltn_neqAle neq1in ltin.
Qed.

Lemma zetaX_halfn j : j.*2 = n -> 'zeta_n ^+ j = -1.
Proof.
move=> eqj2.
have:= zetaP gtn0; rewrite unity_rootE -{2}eqj2 -addnn exprD -expr2 sqrf_eq1.
move=> /orP[] /eqP //.
have /zetaXn_neq1/[swap]-> : (0 < j < n)%N by lia.
by rewrite eqxx.
Qed.

End Zeta.

Lemma zeta1 : 'zeta_1 = 1.
Proof. by have:= zetaP (ltnSn 0); rewrite unity_rootE expr1 => /eqP. Qed.

Lemma zeta_neq1 n : (n > 1)%N -> 'zeta_n != 1.
Proof. by move=> lt1n; rewrite -(expr1 'zeta_n) zetaXn_neq1. Qed.

Lemma zeta2 : 'zeta_2 = -1.
Proof.
have /zetaP : (0 < 2)%N by [].
rewrite unity_rootE -{1}(mulr1 1) -expr2 eqf_sqr => /orP[| /eqP //].
by rewrite (negbTE (zeta_neq1 _)).
Qed.

Lemma conj_zetaXn n i : (i < n)%N -> conjC ('zeta_n ^+ i) = 'zeta_n ^+ (n - i).
Proof.
move=> ltin; have gtn0 : (n > 0)%N by lia.
have zetaX_neq0 : 'zeta_n ^+ i != 0.
  by rewrite expf_eq0 andbC (negbTE (zeta_neq0 _)).
have zetaX_uc := unit_circleXn i (zeta_unit_circle gtn0).
apply: (lregP zetaX_neq0 _).
rewrite -!exprD (subnKC (ltnW ltin)) -normCK (unity_rootP (zetaP gtn0)).
by rewrite (unit_circleP _ zetaX_uc).
Qed.

Lemma Im_zetaXn_gt0 i n : (0 < i < uphalf n)%N -> 0 < 'Im ('zeta_n ^+ i).
Proof.
case/andP=> lt0i ltin2.
have ltin : (i < n)%N by lia.
have gtn0 : (n > 0)%N by lia.
suff : - 'Im ('zeta_n ^+ i) < 'Im ('zeta_n ^+ i).
  have := (Creal_Im ('zeta_n ^+ i)).
  rewrite -comparable0r=> /comparable_ltgtP[/gt0_cp[_ ->]// ||<-]; first last.
    by rewrite oppr0 ltxx.
  move=> /[dup] H; rewrite -{1}(opprK ('Im ('zeta_n ^+ i))) oppr_lt0.
  by move/(lt_trans H)/lt_gtF ->.
rewrite -Im_conj conj_zetaXn //.
have /gt_stereo_proj_zetaXn ltp : (0 < i < n)%N by lia.
have {}/ltp ltp : (0 < n - i < n)%N by lia.
have {}/ltp : (i < n - i)%N by lia.
rewrite /gt_stereo_proj /= -conj_zetaXn // -mono_lt_algRval /= Re_conj.
suff : 'Re ('zeta_n ^+ i) < 1 by rewrite -subr_gt0 -invr_gt0 => /ltr_pM2r ->.
rewrite lt_neqAle andbC.
have [-> -> /=] := Re_unit_circle (unit_circleXn i (zeta_unit_circle gtn0)).
by apply: zetaXn_neq1; lia.
Qed.
Lemma Im_zetaXn_lt0 n i : (n./2 < i < n)%N -> 'Im ('zeta_n ^+ i) < 0.
Proof.
rewrite ltn_half_double => /andP[ltn2i ltin].
have gtn0 : (n > 0)%N by lia.
rewrite -oppr_gt0 -Im_conj conj_zetaXn //.
by apply: Im_zetaXn_gt0; rewrite subn_gt0 ltin /=; lia.
Qed.

Lemma Im_zeta_gt0 n : (n > 2)%N -> 0 < 'Im 'zeta_n.
Proof. by move=> gtn2; rewrite -(expr1 'zeta_n); apply: Im_zetaXn_gt0; lia. Qed.

Lemma Im_zeta_ge0 n : (n > 0)%N -> 0 <= 'Im 'zeta_n.
Proof.
rewrite leq_eqVlt eq_sym => /orP[/eqP-> | lt1n].
  by rewrite zeta1 //= (Creal_ImP _ (@real1 _)).
have:= lt1n; rewrite leq_eqVlt eq_sym => /orP[/eqP-> | lt2n].
  by rewrite zeta2 // raddfN  /= (Creal_ImP _ (@real1 _)) oppr0.
exact: (ltW (Im_zeta_gt0 lt2n)).
Qed.

Lemma Re_zetaXn_lt i j n :
  (i < j <= n./2)%N -> 'Re ('zeta_n ^+ i) > 'Re ('zeta_n ^+ j).
Proof.
case/andP=> ltij.
rewrite geq_half_double => lej2n.
have gtn0 : (n > 0)%N by lia.
case: (altP (i =P 0)) ltij => [-> lt0j |].
  rewrite expr0 (Creal_ReP _ (@real1 _)) lt_neqAle andbC.
  have /Re_unit_circle[-> -> /=] := unit_circleXn j (zeta_unit_circle gtn0).
  by apply: zetaXn_neq1; lia.
rewrite -lt0n => lt0i ltij.
have lt0in : (0 < i < n)%N by lia.
have lt0jn : (0 < j < n)%N by lia.
apply: Re_stereo_proj_incr; try exact: zetaXn_unit_circleC1.
rewrite stereo_proj_ge0 ?unit_circleXn // ?zeta_unit_circle //.
rewrite [X in _ && X]gt_stereo_proj_zetaXn // andbT.
move: lej2n; rewrite leq_eqVlt => /orP[/eqP /zetaX_halfn -> //|].
  by rewrite raddfN /= (Creal_ImP _ (@real1 _)) oppr0.
rewrite -gtn_uphalf_double => ltjup.
by apply/ltW/Im_zetaXn_gt0; rewrite // (ltn_trans lt0i ltij).
Qed.
Lemma Re_zetaXn_le i j n :
  (i <= j <= n./2)%N -> 'Re ('zeta_n ^+ i) >= 'Re ('zeta_n ^+ j).
Proof.
case/andP=> /[swap] ltjn2; rewrite leq_eqVlt => /orP[/eqP-> // | ltij].
by apply/ltW/Re_zetaXn_lt; rewrite ltij.
Qed.

Lemma unity_root_Re_zeta_gt n z :
  (n > 0)%N -> n.-unity_root z -> z != 1 -> 'Re z <= 'Re 'zeta_n.
Proof.
move=> /[dup] gtn0 /unity_root_zetaXE/[apply]/[apply] - [i lt0in {z}->].
wlog ltin2 : i lt0in / (i <= n./2)%N.
  move=> Hwlog; case: (leqP i n./2) => [/(Hwlog _ lt0in) //|].
  rewrite ltn_half_double => ltn2i.
  have /andP[lt0i ltin] := lt0in.
  rewrite -Re_conj conj_zetaXn //; apply: Hwlog.
    rewrite subn_gt0 ltin /= ltn_subLR ?(ltnW ltin) //.
    by rewrite -{1}(add0n n) ltn_add2r.
  by rewrite geq_half_double doubleB leq_subLR -addnn leq_add2r (ltnW _).
rewrite -{2}(expr1 'zeta_n); apply/Re_zetaXn_le => //.
by case/andP: lt0in => ->.
Qed.


Lemma eq_zeta n z :
  (n > 0)%N -> n.-unity_root z -> z != 1 -> 'Im z >= 0 ->
  (forall y, n.-unity_root y -> y != 1 -> 'Re y <= 'Re z) -> z = 'zeta_n.
Proof.
move=> /[dup] gtn0; rewrite leq_eqVlt => /orP[/eqP/esym -> + + _ _ | lt1n].
  by rewrite unity_rootE // expr1 => /eqP -> /[!eqxx].
move=> zu zn1 Imz Remax.
have [i lt0in eqz] := unity_root_zetaXE gtn0 zu zn1.
have eqRe : 'Re z = 'Re 'zeta_n.
  apply/le_anti; rewrite unity_root_Re_zeta_gt //=.
  by rewrite (Remax _ (zetaP gtn0)) ?zeta_neq1 ?andbT ?(gtn_eqF lt1n).
have /eqP : 'Im z ^+2 = 'Im 'zeta_n ^+ 2.
  rewrite -[LHS](addrK ('Re z ^+ 2)); apply/eqP; rewrite subr_eq; apply/eqP.
  rewrite [LHS]addrC [RHS]addrC [in RHS]eqRe -!normC2_Re_Im.
  rewrite (unit_circleP _ (zeta_unit_circle _)) //.
  by rewrite (unit_circleP _ (unity_root_unit_circle gtn0 zu)).
rewrite eqf_sqr => /orP[]// /eqP eqIm.
  by apply/eqP; rewrite eqC eqRe eqIm !eqxx.
have {}Imz : 'Im z = 0.
  by apply le_anti; rewrite Imz eqIm oppr_le0 Im_zeta_ge0.
apply/eqP; rewrite eqC eqRe eqxx Imz /=.
by move/eqP: eqIm; rewrite -eqr_oppLR Imz oppr0.
Qed.

Lemma Im_gt0_eq_zeta n z :
  (n > 0)%N -> n.-unity_root z -> z != 1 -> 'Im z >= 0 ->
  (forall y, n.-unity_root y -> y != 1 -> Im y >= 0 -> 'Re y <= 'Re z)
  -> z = 'zeta_n.
Proof.
move=> gtn0 zu zn1 Imz Remax; apply: eq_zeta => // y yun yn1.
have:= Creal_Im y; rewrite -comparabler0 => /orP[]; last exact: Remax.
rewrite -oppr_ge0 -Im_conj -(Re_conj y); apply: Remax.
  by rewrite unity_root_conj.
by rewrite -conjC1 (inj_eq (can_inj (@conjCK _))).
Qed.


Lemma Xn_sub_1_prod_zetaE n :
  (0 < n)%N -> 'X^n - 1 = \prod_(i < n) ('X - ('zeta_n ^+ i)%:P).
Proof. by move/zeta_primitive/factor_Xn_sub_1 => <-; rewrite big_mkord. Qed.

Lemma zetaM m n : (0 < m * n)%N -> 'zeta_(m * n) ^+ m = 'zeta_n.
Proof.
move=> /[dup] lt0mn; rewrite muln_gt0 => /andP[lt0m lt0n].
have:= lt0n; rewrite leq_eqVlt eq_sym => /orP[/eqP -> | lt1n].
  by rewrite muln1 [RHS]zeta1 //; apply/unity_rootP/zetaP.
apply: Im_gt0_eq_zeta => //.
- by apply/unity_rootP; rewrite -exprM; apply/unity_rootP/zetaP.
- by apply/zetaXn_neq1; rewrite // lt0m /= ltn_Pmulr //.
- move: lt1n; rewrite leq_eqVlt eq_sym => /orP[/eqP -> | lt2n].
    rewrite zetaX_halfn ?muln2 ?double_gt0 //.
    by rewrite raddfN /= (Creal_ImP _ (@real1 _)) oppr0.
  apply/ltW/Im_zetaXn_gt0; rewrite // lt0m /= gtn_uphalf_double.
  by rewrite -muln2 ltn_mul2l lt0m lt2n.
move=> y yun neqy1.
have /(unity_root_zetaXE lt0mn) : (m * n).-unity_root y.
  by apply/unity_rootP; rewrite mulnC exprM (unity_rootP yun) expr1n.
case/(_  neqy1) => k /andP[lt0k ltkmn] /[dup]eqy -> le0Im.
case: (leqP k (m * n)./2) => [lekmn2 | ltmn2k]; first last.
  exfalso.
  have /Im_zetaXn_lt0 : ((m * n)./2 < k < m * n)%N by rewrite ltmn2k.
  by move/(le_lt_trans le0Im); rewrite ltxx.
apply: Re_zetaXn_le; rewrite // lekmn2 andbT.
apply: (dvdn_leq lt0k); rewrite -(dvdn_pmul2r lt0n).
rewrite (prim_order_dvd (zeta_primitive lt0mn)).
by rewrite exprM -eqy -unity_rootE yun.
Qed.

Lemma Re_zeta_lt m n : (1 < m < n)%N -> 'Re 'zeta_m < 'Re 'zeta_n.
Proof.
case/andP=> lt1m ltmn; have lt0m := ltn_trans (ltnSn 0) lt1m.
have lt0n : (0 < n)%N by lia.
have le0mn : (0 < m * n)%N by lia.
have:= le0mn; rewrite mulnC -(zetaM le0mn) => /zetaM <- /[!(mulnC n)].
apply: Re_zetaXn_lt; rewrite // ltmn /=.
by rewrite geq_half_double -muln2 mulnC leq_pmul2r.
Qed.

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
have {addjjC prodjjC}gpol3E : ('X - j%:P) * ('X - j^*%:P) = 'X^2 + 'X + 1.
  by rewrite -polyC1 -prodjjC -/j -{4}['X]mulr1 -polyC1 -addjjC; ring.
have {}gpol3E : 'X^3 - 1 = ('X - 1) * ('X - j%:P) * ('X - j^*%:P).
  by rewrite -mulrA gpol3E; ring.
have /zetaP : (0 < 3)%N by [].
rewrite /root_of_unity {}gpol3E !rootM !root_XsubC (negbTE (zeta_neq1 _)) //=.
case/orP => [/eqP //| /eqP Habs].
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
rewrite -in_unit_circleV ?zeta_unit_circle //.
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
have /zetaP : (0 < 5)%N by [].
rewrite /root_of_unity exprD1 rootM => /orP[].
  by rewrite root_XsubC (negbTE (zeta_neq1 _)).
rewrite /root /index_iota 4!big_cons big_seq1 !hornerE /= expr0 expr1 => /eqP zeq.
have {zeq} : ('zeta_5 ^+ 2 + 'zeta_5 ^- 2) + ('zeta_5 + 'zeta_5 ^- 1) + 1 = 0.
  have := z5n0; rewrite -sqrf_eq0 => /lregP; apply.
  by rewrite mulr0 -{}zeq !mulrDr -!exprD; field by assumption.
set r : algC := 'zeta_5 + 'zeta_5 ^- 1 => req.
have eqrC : r = 2 * 'Re 'zeta_5.
  by rewrite ReE mulrC divfK // /r in_unit_circleV // expr1 zeta_unit_circle.
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
  rewrite (unit_circleP _ (zeta_unit_circle _)) // addrC -subr_eq => /eqP <-.
  by rewrite expr_div_n sqrtCK rez5; field: (@sqrtCK algC 5).
rewrite eqf_sqr => /orP[] /eqP // Habs; exfalso.
have gts0 : 0 < 10 + 2 * sqrtC 5 :> algC.
  by rewrite addr_gt0 // mulr_gt0 // sqrtC_gt0.
have : 'Im 'zeta_5 >= 0 by rewrite Im_zeta_ge0.
rewrite {}Habs; apply/negP; rewrite -!real_ltNge // ?rpred_simpl //=.
  exact: (sqrtC_real (ltW gts0)).
by rewrite oppr_lt0 mulr_gt0 ?invr_gt0 // sqrtC_gt0.
Qed.
