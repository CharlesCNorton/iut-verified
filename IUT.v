(******************************************************************************)
(*                                                                            *)
(*                 Inter-Universal Teichmüller Theory                         *)
(*                                                                            *)
(*     Formalizes structures from Mochizuki's IUT (2012): Hodge theaters,     *)
(*     Frobenioids, the theta-link, and the R-identification diagram          *)
(*     central to the Scholze-Stix dispute over Corollary 3.12.               *)
(*                                                                            *)
(*     "I now do my mathematics with a proof assistant. I have a lot of       *)
(*     wishes in terms of getting this proof assistant to work better, but    *)
(*     at least I don't have to worry about mistakes any more."               *)
(*     - Vladimir Voevodsky, 2014                                             *)
(*                                                                            *)
(*     Author: Charles C. Norton                                              *)
(*     Date: January 8, 2026                                                  *)
(*     License: MIT                                                           *)
(*                                                                            *)
(******************************************************************************)

(* TODO: Formalization Roadmap

   1. Define sum_of_squares n := \sum_(1 <= j < n.+1) (j * j)
   2. Define sum_linear n := \sum_(1 <= j < n.+1) j
   3. Compute sum_of_squares 1 = 1
   4. Compute sum_of_squares 2 = 5
   5. Compute sum_of_squares 3 = 14
   6. Compute sum_linear 1 = 1
   7. Compute sum_linear 2 = 3
   8. Compute sum_linear 3 = 6
   9. Prove sum_of_squares n.+1 = sum_of_squares n + (n.+1) * (n.+1)
   10. Prove sum_linear n.+1 = sum_linear n + n.+1
   11. Prove 6 * sum_of_squares 0 = 0 * 1 * 1
   12. Prove 6 * sum_of_squares n = n * (n + 1) * (2 * n + 1) assuming IH
   13. Prove 6 * sum_of_squares n.+1 = (n.+1) * (n + 2) * (2 * n + 3) by algebra
   14. Prove 6 * sum_of_squares n = n * (n + 1) * (2 * n + 1) by induction
   15. Prove 2 * sum_linear 0 = 0 * 1
   16. Prove 2 * sum_linear n = n * (n + 1) assuming IH
   17. Prove 2 * sum_linear n.+1 = (n.+1) * (n + 2) by algebra
   18. Prove 2 * sum_linear n = n * (n + 1) by induction
   19. Define sum_diff n := sum_of_squares n - sum_linear n
   20. Prove sum_diff n = \sum_(1 <= j < n.+1) (j * j - j)
   21. Prove j * j - j = j * (j - 1) for j >= 1
   22. Prove j * (j - 1) >= 0 for j >= 1
   23. Prove j * (j - 1) > 0 for j >= 2
   24. Prove sum_diff 1 = 0
   25. Prove sum_diff 2 = 2
   26. Prove sum_diff n > 0 for n >= 2
   27. Prove sum_of_squares n > sum_linear n for n >= 2
   28. Define mochizuki_bound ell delta deg_q := (sum_of_squares ell)%:R * delta - deg_q
   29. Define scholze_stix_bound ell delta deg_q := (sum_linear ell)%:R * delta - deg_q
   30. Prove mochizuki_bound - scholze_stix_bound = (sum_diff ell)%:R * delta
   31. Prove delta > 0 -> sum_diff ell > 0 -> mochizuki_bound > scholze_stix_bound
   32. Prove ell >= 2 -> delta > 0 -> mochizuki_bound > scholze_stix_bound
   33. Define critical_delta ell deg_q := deg_q / (sum_linear ell)%:R
   34. Prove sum_linear ell > 0 for ell >= 1
   35. Prove critical_delta ell deg_q > 0 for ell >= 1, deg_q > 0
   36. Prove scholze_stix_bound ell (critical_delta ell deg_q) deg_q = 0
   37. Prove delta < critical_delta -> scholze_stix_bound < 0
   38. Prove delta <= critical_delta -> scholze_stix_bound <= 0
   39. Compute sum_of_squares 2 / sum_linear 2 = 5 / 3
   40. Prove sum_of_squares ell > sum_linear ell for ell >= 2
   41. Prove (sum_of_squares ell)%:R * critical_delta > deg_q for ell >= 2
   42. Prove mochizuki_bound ell (critical_delta ell deg_q) deg_q > 0 for ell >= 2
   43. Define RCopyNode := { rcn_id : nat }
   44. Define RIdentification := { ri_source; ri_target; ri_scale : R }
   45. Define ri_compose f g := mkRI (ri_source g) (ri_target f) (ri_scale f * ri_scale g)
   46. Define ri_identity n := mkRI n n 1
   47. Prove ri_scale (ri_compose f g) = ri_scale f * ri_scale g
   48. Prove ri_scale (ri_identity n) = 1
   49. Prove ri_compose f (ri_identity (ri_source f)) = f up to node equality
   50. Prove ri_compose (ri_identity (ri_target f)) f = f up to node equality
   51. Define FullSchStixDiagram with six nodes
   52. Extend with edge theta_link from R_theta_abs to R_q_abs
   53. Extend with conc_to_abs_theta : 'I_ell -> RIdentification
   54. Extend with conc_to_abs_q : RIdentification
   55. Extend with conc_to_arith_theta : 'I_ell -> RIdentification
   56. Extend with conc_to_arith_q : RIdentification
   57. Extend with arith_comparison : RIdentification
   58. Define extracted_scaling D j := ri_scale (conc_to_abs_theta D j)
   59. Define arithmetic_scaling D j := ri_scale (conc_to_arith_theta D j)
   60. Define is_jsquared_scaling D := forall j, extracted_scaling D j = ((val j).+1 ^ 2)%:R
   61. Define is_uniform_scaling D := forall j, extracted_scaling D j = 1
   62. Define is_j_scaling D := forall j, extracted_scaling D j = ((val j).+1)%:R
   63. Define path_upper D j := ri_scale (conc_to_abs_theta D j) * ri_scale (theta_link D)
   64. Define path_lower D j := ri_scale (conc_to_arith_theta D j) * ri_scale (arith_comparison D)
   65. Define diagram_commutes D := forall j, path_upper D j = path_lower D j
   66. Simplify: assume conc_to_abs_q and conc_to_arith_q have scale 1
   67. Redefine diagram_commutes D := forall j, path_upper D j = path_lower D j
   68. Prove diagram_commutes D -> path_upper j1 / path_upper j2 = path_lower j1 / path_lower j2
   69. Prove diagram_commutes D -> extracted_scaling j1 / j2 = arithmetic_scaling j1 / j2
   70. Define arithmetic_side_uniform D := forall j, arithmetic_scaling D j = 1
   71. Define arithmetic_side_jsquared D := forall j, arithmetic_scaling D j = ((val j).+1 ^ 2)%:R
   72. Define link_scale_one D := ri_scale (theta_link D) = 1
   73. Define arith_comp_one D := ri_scale (arith_comparison D) = 1
   74. Define consistent_identifications D := arithmetic_side_uniform /\ link_scale_one /\ arith_comp_one
   75. Prove diagram_commutes D -> arithmetic_side_uniform D -> path_upper D j = extracted_scaling D j
   76. Prove diagram_commutes D -> arithmetic_side_uniform D -> arith_comp_one D -> extracted_scaling D j = 1
   77. Prove diagram_commutes D -> consistent_identifications D -> is_uniform_scaling D
   78. Prove is_jsquared_scaling D -> extracted_scaling D (Ordinal H1) = 4 where H1 : 1 < ell
   79. Prove is_uniform_scaling D -> extracted_scaling D (Ordinal H1) = 1
   80. Prove 4%:R <> 1 :> R for R with char R > 3
   81. Prove is_jsquared_scaling D -> ~ is_uniform_scaling D for ell >= 2
   82. Prove diagram_commutes D -> consistent_identifications D -> ~ is_jsquared_scaling D
   83. Define effective_bound D delta deg_q := \sum_(j < ell) extracted_scaling D j * delta - deg_q
   84. Prove is_uniform_scaling D -> effective_bound D delta deg_q = ell%:R * delta - deg_q
   85. Prove is_uniform_scaling D -> effective_bound D = scholze_stix_bound
   86. Prove is_jsquared_scaling D -> effective_bound D = (sum_of_squares ell)%:R * delta - deg_q
   87. Prove is_jsquared_scaling D -> effective_bound D = mochizuki_bound
   88. Prove diagram_commutes D -> consistent D -> effective_bound D = scholze_stix_bound
   89. Prove diagram_commutes D -> consistent D -> delta <= critical -> effective_bound D <= 0
   90. Define Ind1_data := { ind1_auts : Type; ind1_action : ind1_auts -> R -> R }
   91. Define ind1_preserves_mult ind := forall a x y, action a (x * y) = action a x * action a y
   92. Define indeterminacy_region ind x := fun y => exists a, y = ind1_action ind a x
   93. Define region_contains ind x y := indeterminacy_region ind x y
   94. Define blurring_absorbs_jsquared ind := forall j x, region_contains ind x (((val j).+1 ^ 2)%:R * x)
   95. Prove blurring_absorbs_jsquared ind -> region_contains ind 1 ((ell ^ 2)%:R)
   96. Define region_diameter ind := sup { |y - x| : region_contains ind x y, |x| = 1 }
   97. Prove blurring_absorbs_jsquared ind -> region_diameter ind >= (ell^2 - 1)%:R
   98. Define blurred_mochizuki_bound ind delta deg_q := mochizuki_bound - region_diameter ind * delta
   99. Prove blurring_absorbs -> blurred_bound <= mochizuki_bound - (ell^2 - 1)%:R * delta
   100. Prove ell >= 2 -> (ell^2 - 1) >= ell
   101. Prove ell >= 2 -> (sum_of_squares ell) - (ell^2 - 1) <= sum_linear ell
   102. Prove ell >= 3 -> (sum_of_squares ell) - (ell^2 - 1) < sum_linear ell
   103. Prove blurring_absorbs -> ell >= 2 -> blurred_bound <= scholze_stix_bound + C
   104. Prove blurring_absorbs -> ell >= 3 -> blurred_bound < scholze_stix_bound + delta
   105. Prove blurring_absorbs -> delta <= critical -> blurred_bound <= 0
   106. Define scaling_outcome D ind := consistent D \/ (jsquared D /\ ~consistent D) \/ blurring_absorbs ind
   107. Prove diagram_commutes D -> consistent D -> effective_bound D = scholze_stix_bound
   108. Prove jsquared D -> ~consistent D -> effective_bound D = mochizuki_bound
   109. Prove blurring_absorbs ind -> blurred_bound <= scholze_stix_bound for large ell
   110. Define useful_bound b := b > 0
   111. Define vacuous_bound b := b <= 0
   112. Prove delta <= critical -> vacuous_bound (scholze_stix_bound)
   113. Prove delta <= critical -> ell >= 2 -> useful_bound (mochizuki_bound)
   114. Prove diagram_commutes D -> consistent D -> delta <= critical -> vacuous_bound (effective_bound D)
   115. Prove diagram_commutes D -> jsquared D -> ~consistent D -> delta > moch_critical -> useful_bound (effective_bound D)
   116. Prove blurring_absorbs ind -> delta <= critical -> vacuous_bound (blurred_bound)
   117. State trilemma: diagram_commutes D -> (consistent /\ vacuous) \/ (jsquared /\ ~consistent) \/ (blurring /\ vacuous)
   118. Prove trilemma by case analysis
   119. Define iut_succeeds D ind delta deg_q := commutes /\ jsquared /\ useful /\ ~blurring
   120. Prove iut_succeeds D ind delta deg_q -> ~consistent_identifications D
   121. Prove iut_succeeds D ind delta deg_q -> ~blurring_absorbs_jsquared ind
   122. Prove iut_succeeds D ind delta deg_q -> delta > deg_q / (sum_of_squares ell)%:R
   123. State necessary_conditions: iut_succeeds -> (~consistent /\ ~blurring /\ delta > moch_critical)
   124. Prove necessary_conditions
   125. State ss_position: commutes -> (consistent \/ blurring) -> delta <= critical -> vacuous
   126. Prove ss_position
*)

From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Import Num.Theory.

Open Scope ring_scope.

Section Places.

Inductive PlaceType : Type :=
  | Archimedean : PlaceType
  | NonArchimedean : nat -> PlaceType.

Record Place := mkPlace {
  place_type : PlaceType;
  place_index : nat
}.

Definition is_archimedean (v : Place) : bool :=
  match place_type v with
  | Archimedean => true
  | NonArchimedean _ => false
  end.

Definition is_nonarchimedean (v : Place) : bool :=
  ~~ is_archimedean v.

End Places.

Section RCopies.

Variable R : ringType.

Record RCopy := mkRCopy {
  rcopy_label : nat
}.

Record RMap := mkRMap {
  rmap_source : RCopy;
  rmap_target : RCopy;
  rmap_scalar : R
}.

Definition rmap_compose (f g : RMap) : RMap :=
  mkRMap (rmap_source g) (rmap_target f) (rmap_scalar f * rmap_scalar g).

Definition rmap_id (c : RCopy) : RMap :=
  mkRMap c c 1.

Lemma rmap_compose_scalar (f g : RMap) :
  rmap_scalar (rmap_compose f g) = rmap_scalar f * rmap_scalar g.
Proof. by []. Qed.

Lemma rmap_id_scalar (c : RCopy) :
  rmap_scalar (rmap_id c) = 1.
Proof. by []. Qed.

End RCopies.

Section SSDiagram.

Variable R : ringType.
Variable ell : nat.

Record SSDiagram := mkSSD {
  ssd_R_Theta_Theta : RCopy;
  ssd_R_Theta_q : RCopy;
  ssd_R_c_theta : 'I_ell -> RCopy;
  ssd_R_c_q : RCopy;
  ssd_R_Theta : RCopy;
  ssd_R_q : RCopy;
  ssd_theta_link : RMap R;
  ssd_c_to_abs_theta : 'I_ell -> RMap R;
  ssd_c_to_abs_q : RMap R;
  ssd_c_to_arith_theta : 'I_ell -> RMap R;
  ssd_c_to_arith_q : RMap R;
  ssd_arith_comparison : RMap R
}.

Definition path_via_abstract (D : SSDiagram) (j : 'I_ell) : R :=
  rmap_scalar (ssd_c_to_abs_q D) *
  rmap_scalar (ssd_theta_link D) *
  rmap_scalar (ssd_c_to_abs_theta D j).

Definition path_via_arith (D : SSDiagram) (j : 'I_ell) : R :=
  rmap_scalar (ssd_c_to_arith_q D) *
  rmap_scalar (ssd_arith_comparison D) *
  rmap_scalar (ssd_c_to_arith_theta D j).

Definition paths_consistent (D : SSDiagram) : Prop :=
  forall j : 'I_ell, path_via_abstract D j = path_via_arith D j.

End SSDiagram.

Section PilotObjects.

Variable R : ringType.
Variable ell : nat.
Variable bad_places : seq Place.

Record QPilot := mkQPilot {
  qp_value : Place -> R
}.

Record ThetaPilot := mkThetaPilot {
  tp_value : 'I_ell -> Place -> R
}.

Definition theta_q_exponent (j : 'I_ell) : nat := (nat_of_ord j).+1 * (nat_of_ord j).+1.

End PilotObjects.

Section CoreQuestion.

Variable R : ringType.
Variable ell : nat.
Hypothesis ell_pos : (0 < ell)%N.

Variable identification_scalar : 'I_ell -> R.

Definition j_squared (j : 'I_ell) : R := ((nat_of_ord j).+1 * (nat_of_ord j).+1)%:R.

Definition mochizuki_claim : Prop :=
  forall j : 'I_ell, identification_scalar j = j_squared j.

Definition uniform_claim : Prop :=
  forall j : 'I_ell, identification_scalar j = 1.

End CoreQuestion.

Section LogVolume.

Variable R : numDomainType.
Variable ell : nat.
Hypothesis ell_pos : (0 < ell)%N.

Variable delta : R.
Variable deg_q : R.
Variable scale : 'I_ell -> R.

Definition log_vol_theta : R :=
  \sum_(j < ell) (scale (Ordinal (ltn_ord j)) * delta).

Definition log_vol_q : R := deg_q.

Definition cor312_ineq : Prop :=
  - log_vol_theta <= - log_vol_q.

End LogVolume.

Section InequalityAnalysis.

Variable R : numDomainType.
Variable ell : nat.
Hypothesis ell_pos : (0 < ell)%N.

Variable delta : R.
Variable deg_q : R.

Definition sum_of_squares (n : nat) : nat :=
  \sum_(1 <= j < n.+1) (j * j).

Definition sum_linear (n : nat) : nat :=
  \sum_(1 <= j < n.+1) j.

Definition jsq_scaled_bound (n : nat) (d dq : R) : R :=
  (sum_of_squares n)%:R * d - dq.

Definition uniform_scaled_bound (n : nat) (d dq : R) : R :=
  n%:R * d - dq.

Definition bound_is_useful (bound : R) : Prop :=
  exists c : R, c > 0 /\ bound >= c.

Definition bound_is_vacuous (bound : R) (d : R) : Prop :=
  bound <= 0 /\ d >= 0.

Lemma sum_of_squares_1 : sum_of_squares 1 = 1.
Proof. by rewrite /sum_of_squares big_nat1. Qed.

Lemma sum_of_squares_2 : sum_of_squares 2 = 5.
Proof. by rewrite /sum_of_squares big_ltn // big_nat1. Qed.

Lemma sum_linear_1 : sum_linear 1 = 1.
Proof. by rewrite /sum_linear big_nat1. Qed.

Lemma sum_linear_2 : sum_linear 2 = 3.
Proof. by rewrite /sum_linear big_ltn // big_nat1. Qed.

Lemma squares_gt_linear_at_2 : (sum_of_squares 2 > sum_linear 2)%N.
Proof. by rewrite sum_of_squares_2 sum_linear_2. Qed.

End InequalityAnalysis.

Section Resolution.

Variable R : numDomainType.
Variable ell : nat.
Hypothesis ell_ge_2 : (2 <= ell)%N.

Variable theta_to_abstract_scalar : 'I_ell -> R.

Definition scalars_are_jsquared : Prop :=
  forall j : 'I_ell, theta_to_abstract_scalar j = ((nat_of_ord j).+1 * (nat_of_ord j).+1)%:R.

Definition scalars_are_uniform : Prop :=
  forall j : 'I_ell, theta_to_abstract_scalar j = 1.

Definition scalars_vary : Prop :=
  exists j1 j2 : 'I_ell, theta_to_abstract_scalar j1 <> theta_to_abstract_scalar j2.

Lemma four_gt_one : (4 > 1)%N.
Proof. by []. Qed.

Lemma jsq_at_2_is_4 : (2 * 2 = 4)%N.
Proof. by []. Qed.

End Resolution.

Section Frobenioids.

Variable R : ringType.

Record DivisorMonoid := mkDM {
  dm_carrier : Type;
  dm_zero : dm_carrier;
  dm_add : dm_carrier -> dm_carrier -> dm_carrier;
  dm_assoc : forall a b c, dm_add a (dm_add b c) = dm_add (dm_add a b) c;
  dm_unit_l : forall a, dm_add dm_zero a = a;
  dm_unit_r : forall a, dm_add a dm_zero = a
}.

Record UnitGroup := mkUG {
  ug_carrier : Type;
  ug_one : ug_carrier;
  ug_mul : ug_carrier -> ug_carrier -> ug_carrier;
  ug_inv : ug_carrier -> ug_carrier;
  ug_assoc : forall a b c, ug_mul a (ug_mul b c) = ug_mul (ug_mul a b) c;
  ug_unit_l : forall a, ug_mul ug_one a = a;
  ug_inv_l : forall a, ug_mul (ug_inv a) a = ug_one
}.

Record Frobenioid := mkFrob {
  frob_divisors : DivisorMonoid;
  frob_units : UnitGroup;
  frob_degree : dm_carrier frob_divisors -> R;
  frob_frobenius : nat -> dm_carrier frob_divisors -> dm_carrier frob_divisors;
  frob_frob_degree : forall n d,
    frob_degree (frob_frobenius n d) = n%:R * frob_degree d
}.

Definition frob_trivial_units (F : Frobenioid) : Prop :=
  forall u : ug_carrier (frob_units F), u = ug_one (frob_units F).

Definition frob_realified (F : Frobenioid) : Type :=
  dm_carrier (frob_divisors F).

End Frobenioids.

Section PrimeStripDef.

Variable R : numDomainType.
Variable places : seq Place.

Record FmuStrip := mkFmuStrip {
  fmu_frob : Place -> Frobenioid R;
  fmu_units_mod_torsion : Place -> Type;
  fmu_global_degree : R
}.

Record FtimesStrip := mkFtimesStrip {
  ftimes_frob : Place -> Frobenioid R;
  ftimes_full_units : Place -> UnitGroup;
  ftimes_global_degree : R
}.

Record FrealStrip := mkFrealStrip {
  freal_values : Place -> R;
  freal_sum : R
}.

Inductive PrimeStripVariant :=
  | PS_Fmu : FmuStrip -> PrimeStripVariant
  | PS_Ftimes : FtimesStrip -> PrimeStripVariant
  | PS_Freal : FrealStrip -> PrimeStripVariant.

End PrimeStripDef.

Record PrimeStrip := mkPS {
  ps_ring : numDomainType;
  ps_places : seq Place;
  ps_variant : PrimeStripVariant ps_ring
}.

Section HodgeTheaterDef.

Variable R : numDomainType.
Variable ell : nat.

Record MonoThetaEnv := mkMTE {
  mte_cyclotomic_rigidity : Type;
  mte_theta_values : 'I_ell -> R;
  mte_q_parameter : R
}.

Record EtalePortion := mkEtale {
  etale_fund_group : Type;
  etale_galois_action : Type
}.

Record FrobeniusPortion := mkFrob_portion {
  frobp_prime_strip : PrimeStripVariant R;
  frobp_monoid_action : Type
}.

Record HodgeTheater := mkHT {
  ht_label : nat;
  ht_etale : EtalePortion;
  ht_frobenius : FrobeniusPortion;
  ht_mono_theta : MonoThetaEnv;
  ht_theta_strip : PrimeStripVariant R;
  ht_q_strip : PrimeStripVariant R;
  ht_base_field : fieldType
}.

Definition ht_theta_values (H : HodgeTheater) : 'I_ell -> R :=
  mte_theta_values (ht_mono_theta H).

Definition ht_q_param (H : HodgeTheater) : R :=
  mte_q_parameter (ht_mono_theta H).

Record ThetaLink := mkTL {
  tl_domain : HodgeTheater;
  tl_codomain : HodgeTheater;
  tl_fmu_iso : PrimeStripVariant R -> PrimeStripVariant R;
  tl_theta_to_q : Prop
}.

Definition tl_identifies_theta_with_q (link : ThetaLink) : Prop :=
  tl_fmu_iso link (ht_theta_strip (tl_domain link)) =
  ht_q_strip (tl_codomain link).

Record LogLink := mkLL {
  ll_domain : HodgeTheater;
  ll_codomain : HodgeTheater;
  ll_log_map : R -> R;
  ll_preserves_galois : Prop
}.

Record LogThetaLattice := mkLTL {
  ltl_theaters : int -> int -> HodgeTheater;
  ltl_theta_links : int -> ThetaLink;
  ltl_log_links : int -> int -> LogLink;
  ltl_vertical_log : forall m n, ll_domain (ltl_log_links m n) = ltl_theaters m n;
  ltl_horizontal_theta : forall n,
    tl_domain (ltl_theta_links n) = ltl_theaters 0 n
}.

End HodgeTheaterDef.

Section Indeterminacies.

Variable R : numDomainType.
Variable ell : nat.

Record Ind1_UnitGroup := mkInd1 {
  ind1_automorphisms : Type;
  ind1_action_on_units : ind1_automorphisms -> R -> R;
  ind1_preserves_structure : forall a x y,
    ind1_action_on_units a (x * y) = ind1_action_on_units a x * ind1_action_on_units a y
}.

Record Ind2_Galois := mkInd2 {
  ind2_kummer_isos : nat -> Type;
  ind2_upper_semi_compat : forall m n, (m <= n)%N -> ind2_kummer_isos m -> ind2_kummer_isos n;
  ind2_log_link_compat : Prop
}.

Record Ind3_Label := mkInd3 {
  ind3_label_perms : Type;
  ind3_F_ell_action : ind3_label_perms -> 'I_ell -> 'I_ell;
  ind3_upper_semi_compat_nonarc : Prop;
  ind3_surjective_arc : Prop
}.

Record FullIndeterminacy := mkFullInd {
  full_ind1 : Ind1_UnitGroup;
  full_ind2 : Ind2_Galois;
  full_ind3 : Ind3_Label
}.

Definition indeterminacy_region (ind : FullIndeterminacy) (base : R) : R -> Prop :=
  fun x => exists a : ind1_automorphisms (full_ind1 ind),
    x = @ind1_action_on_units (full_ind1 ind) a base.

Definition blurring_factor (ind : FullIndeterminacy) : R -> R := id.

Definition indeterminacy_absorbs_jsquared
  (ind : FullIndeterminacy) (j : 'I_ell) (scale : R) : Prop :=
  forall base : R,
    indeterminacy_region ind base (scale * base).

Definition scholze_stix_bound (ind : FullIndeterminacy) : Prop :=
  forall j : 'I_ell,
    indeterminacy_absorbs_jsquared ind j ((nat_of_ord j).+1 * (nat_of_ord j).+1)%:R ->
    exists c : R, c >= (ell * ell)%:R.

End Indeterminacies.

Section MultiradialAlgorithm.

Variable R : numDomainType.
Variable ell : nat.
Hypothesis ell_pos : (0 < ell)%N.

Definition theta_pilot_region
  (ind : FullIndeterminacy R ell) (theta_vals : 'I_ell -> R) : ('I_ell -> R) -> Prop :=
  fun f => forall j, @indeterminacy_region R ell ind (theta_vals j) (f j).

Definition q_pilot_value (q : R) : R := q.

Definition multiradial_output
  (ind : FullIndeterminacy R ell)
  (theta_vals : 'I_ell -> R)
  (q : R) : Prop :=
  exists f : 'I_ell -> R,
    theta_pilot_region ind theta_vals f /\
    forall j, f j <= q.

Definition theorem_3_11
  (H1 H2 : HodgeTheater R ell)
  (link : ThetaLink R ell)
  (ind : FullIndeterminacy R ell) : Prop :=
  tl_domain link = H1 ->
  tl_codomain link = H2 ->
  multiradial_output ind (ht_theta_values H1) (ht_q_param H2).

End MultiradialAlgorithm.

Section Corollary312.

Variable R : numDomainType.
Variable ell : nat.
Hypothesis ell_pos : (0 < ell)%N.

Definition log_vol_theta_pilot
  (ind : FullIndeterminacy R ell)
  (theta_vals : 'I_ell -> R) : R :=
  \sum_(j < ell) theta_vals (Ordinal (ltn_ord j)).

Definition log_vol_q_pilot (q_val : R) : R := q_val.

Definition corollary_3_12_statement
  (ind : FullIndeterminacy R ell)
  (theta_vals : 'I_ell -> R)
  (q_val : R) : Prop :=
  - log_vol_theta_pilot ind theta_vals <= - log_vol_q_pilot q_val.

Definition corollary_3_12_from_multiradial
  (H1 H2 : HodgeTheater R ell)
  (link : ThetaLink R ell)
  (ind : FullIndeterminacy R ell) : Prop :=
  theorem_3_11 H1 H2 link ind ->
  corollary_3_12_statement ind (ht_theta_values H1) (ht_q_param H2).

Definition concrete_theta_scaling (j : 'I_ell) : nat :=
  (nat_of_ord j).+1 * (nat_of_ord j).+1.

Definition abstract_theta_identification
  (concrete : 'I_ell -> R) (abstract : 'I_ell -> R) (scale : 'I_ell -> R) : Prop :=
  forall j, abstract j = scale j * concrete j.

Definition mochizuki_scaling (j : 'I_ell) : R :=
  (concrete_theta_scaling j)%:R.

Definition uniform_scaling (j : 'I_ell) : R := 1.

Definition scaling_choice_determines_inequality
  (scale : 'I_ell -> R)
  (concrete_theta : 'I_ell -> R)
  (q_val : R) : R :=
  \sum_(j < ell) scale (Ordinal (ltn_ord j)) * concrete_theta (Ordinal (ltn_ord j)) - q_val.

Definition useful_inequality (bound : R) : Prop :=
  bound > 0.

Definition vacuous_inequality (bound : R) : Prop :=
  bound <= 0.

End Corollary312.

Section DiagramAnalysis.

Variable R : numDomainType.
Variable ell : nat.
Hypothesis ell_pos : (0 < ell)%N.
Hypothesis R_char0 : [char R] =i pred0.

Record RCopyNode := mkRCN {
  rcn_id : nat
}.

Record RIdentification := mkRI {
  ri_source : RCopyNode;
  ri_target : RCopyNode;
  ri_scale : R
}.

Definition ri_compose (f g : RIdentification) (Hmatch : ri_target g = ri_source f) : RIdentification :=
  mkRI (ri_source g) (ri_target f) (ri_scale f * ri_scale g).

Definition ri_identity (n : RCopyNode) : RIdentification :=
  mkRI n n 1.

Record SchStixDiagram := mkSchStix {
  node_R_theta_theta : RCopyNode;
  node_R_theta_q : RCopyNode;
  node_R_c_theta : 'I_ell -> RCopyNode;
  node_R_c_q : RCopyNode;
  node_R_arith_theta : RCopyNode;
  node_R_arith_q : RCopyNode;

  edge_theta_link : RIdentification;
  edge_c_to_abs_theta : 'I_ell -> RIdentification;
  edge_c_to_abs_q : RIdentification;
  edge_c_to_arith_theta : 'I_ell -> RIdentification;
  edge_c_to_arith_q : RIdentification;
  edge_arith_eq : RIdentification
}.

Definition path_abstract (D : SchStixDiagram) (j : 'I_ell) : R :=
  ri_scale (edge_theta_link D) *
  ri_scale (edge_c_to_abs_theta D j).

Definition path_arithmetic (D : SchStixDiagram) (j : 'I_ell) : R :=
  ri_scale (edge_arith_eq D) *
  ri_scale (edge_c_to_arith_theta D j).

Definition diagram_commutes (D : SchStixDiagram) : Prop :=
  forall j : 'I_ell, path_abstract D j = path_arithmetic D j.

Definition scaling_from_diagram (D : SchStixDiagram) : 'I_ell -> R :=
  fun j => ri_scale (edge_c_to_abs_theta D j).

Definition tate_curve_scaling (j : 'I_ell) : R :=
  ((nat_of_ord j).+1 * (nat_of_ord j).+1)%:R.

Definition diagram_has_tate_scaling (D : SchStixDiagram) : Prop :=
  forall j : 'I_ell, scaling_from_diagram D j = tate_curve_scaling j.

Definition diagram_has_uniform_scaling (D : SchStixDiagram) : Prop :=
  forall j : 'I_ell, scaling_from_diagram D j = 1.

Lemma tate_nonuniform_at_1 (H1 : (1 < ell)%N) :
  tate_curve_scaling (Ordinal H1) <> 1.
Proof.
  rewrite /tate_curve_scaling /= -[1]/(1%:R) => /eqP.
  by rewrite eqr_nat.
Qed.

Definition commutes_and_tate_implies (D : SchStixDiagram) : Prop :=
  diagram_commutes D ->
  diagram_has_tate_scaling D ->
  forall j : 'I_ell, path_arithmetic D j = tate_curve_scaling j.

Definition commutes_and_uniform_implies (D : SchStixDiagram) : Prop :=
  diagram_commutes D ->
  diagram_has_uniform_scaling D ->
  forall j : 'I_ell, path_arithmetic D j = 1.

Definition tate_and_uniform_incompatible (D : SchStixDiagram) (H1 : (1 < ell)%N) : Prop :=
  diagram_has_tate_scaling D ->
  diagram_has_uniform_scaling D ->
  False.

Lemma tate_uniform_contradiction (D : SchStixDiagram) (H1 : (1 < ell)%N) :
  tate_and_uniform_incompatible D H1.
Proof.
  rewrite /tate_and_uniform_incompatible => Htate Hunif.
  have Heq : tate_curve_scaling (Ordinal H1) = 1.
    by rewrite -(Htate (Ordinal H1)) Hunif.
  by move: Heq; apply: tate_nonuniform_at_1.
Qed.

Definition core_question (D : SchStixDiagram) : Prop :=
  diagram_commutes D ->
  (diagram_has_tate_scaling D \/ diagram_has_uniform_scaling D).

Definition mochizuki_diagram_claim (D : SchStixDiagram) : Prop :=
  diagram_commutes D /\ diagram_has_tate_scaling D.

Definition scholze_stix_diagram_claim (D : SchStixDiagram) : Prop :=
  diagram_commutes D -> diagram_has_uniform_scaling D.

End DiagramAnalysis.

Section TateCurve.

Variable K : fieldType.
Variable q : K.
Hypothesis q_nonzero : q != 0.
Hypothesis q_not_root_of_unity : forall n : nat, (0 < n)%N -> q ^+ n != 1.

Definition tate_curve := K.

Variable ell : nat.
Hypothesis ell_pos : (0 < ell)%N.

Definition torsion_point (j : 'I_ell) : K := q ^+ (nat_of_ord j).

Definition theta_at_torsion (j : 'I_ell) : K :=
  q ^+ ((nat_of_ord j).+1 * (nat_of_ord j).+1).

Definition q_pilot : K := q.

Definition theta_q_ratio (j : 'I_ell) : K :=
  theta_at_torsion j / q_pilot.

Definition theta_exponent (j : 'I_ell) : nat :=
  (nat_of_ord j).+1 * (nat_of_ord j).+1.

Lemma theta_exp_1 : theta_exponent (Ordinal ell_pos) = 1.
Proof. by rewrite /theta_exponent /= muln1. Qed.

Lemma theta_exp_grows (j : 'I_ell) :
  ((nat_of_ord j).+1 <= theta_exponent j)%N.
Proof.
  rewrite /theta_exponent.
  by rewrite leq_pmulr // ltnW.
Qed.

Definition derived_scalar (j : 'I_ell) : nat := theta_exponent j.

End TateCurve.

Section Connection.

Variable R : numDomainType.
Variable ell : nat.
Hypothesis ell_ge_2 : (2 <= ell)%N.

Definition tate_derived_scalar (j : 'I_ell) : R :=
  ((nat_of_ord j).+1 * (nat_of_ord j).+1)%:R.

Lemma tate_scalar_at_0 (H : (0 < ell)%N) :
  tate_derived_scalar (Ordinal H) = 1.
Proof. by rewrite /tate_derived_scalar /= muln1. Qed.

Lemma tate_scalar_at_1 (H : (1 < ell)%N) :
  tate_derived_scalar (Ordinal H) = 4%:R.
Proof. by rewrite /tate_derived_scalar /=. Qed.

Definition tate_scalars_match_jsquared :
  forall j : 'I_ell, tate_derived_scalar j = ((nat_of_ord j).+1 * (nat_of_ord j).+1)%:R.
Proof. by move=> j; rewrite /tate_derived_scalar. Qed.

End Connection.

Section Inconsistency.

Variable R : numDomainType.
Variable ell : nat.
Hypothesis ell_ge_2 : (2 <= ell)%N.

Definition uniform_scalars (f : 'I_ell -> R) : Prop :=
  forall j : 'I_ell, f j = 1.

Definition jsquared_scalars (f : 'I_ell -> R) : Prop :=
  forall j : 'I_ell, f j = ((nat_of_ord j).+1 * (nat_of_ord j).+1)%:R.

Lemma uniform_implies_all_one (f : 'I_ell -> R) (H0 : (0 < ell)%N) :
  uniform_scalars f -> f (Ordinal H0) = 1.
Proof. by move=> Hu; apply: Hu. Qed.

Lemma jsquared_at_0 (f : 'I_ell -> R) (H0 : (0 < ell)%N) :
  jsquared_scalars f -> f (Ordinal H0) = 1.
Proof. by move=> Hj; rewrite Hj /= muln1. Qed.

Lemma jsquared_at_1 (f : 'I_ell -> R) (H1 : (1 < ell)%N) :
  jsquared_scalars f -> f (Ordinal H1) = 4%:R.
Proof. by move=> Hj; rewrite Hj /=. Qed.

Definition uniform_and_jsquared_agree (f : 'I_ell -> R) : Prop :=
  uniform_scalars f /\ jsquared_scalars f.

Lemma agree_implies_all_jsq_eq_1 (f : 'I_ell -> R) :
  uniform_and_jsquared_agree f ->
  forall j : 'I_ell, ((nat_of_ord j).+1 * (nat_of_ord j).+1)%:R = (1 : R).
Proof.
  move=> [Hu Hj] k.
  by rewrite -Hj Hu.
Qed.

Lemma agree_implies_4_eq_1 (f : 'I_ell -> R) (H1 : (1 < ell)%N) :
  uniform_and_jsquared_agree f -> (4%:R : R) = 1.
Proof.
  move=> Ha.
  exact: (agree_implies_all_jsq_eq_1 Ha (Ordinal H1)).
Qed.

Hypothesis R_char_gt_3 : (3%:R : R) != 0.

Lemma four_neq_one_R : (4%:R : R) != 1.
Proof.
  apply/negP => /eqP H4eq1.
  move: R_char_gt_3.
  have H3: (3%:R : R) = 4%:R - 1%:R.
    by rewrite -natrB //=.
  by rewrite H3 H4eq1 subrr eqxx.
Qed.

Lemma no_agreement (f : 'I_ell -> R) (H1 : (1 < ell)%N) :
  ~ uniform_and_jsquared_agree f.
Proof.
  move=> Ha.
  move: (agree_implies_4_eq_1 H1 Ha).
  by move/eqP; rewrite (negPf four_neq_one_R).
Qed.

End Inconsistency.

Theorem iut_core_tension (R : numDomainType) (ell : nat)
  (ell_ge_2 : (2 <= ell)%N) (R_char_gt_3 : (3%:R : R) != 0) :
  forall f : 'I_ell -> R,
    jsquared_scalars f -> (1 < ell)%N -> ~ uniform_scalars f.
Proof.
  move=> f Hj H1 Hu.
  apply: (no_agreement R_char_gt_3 (f:=f) H1).
  by split.
Qed.
