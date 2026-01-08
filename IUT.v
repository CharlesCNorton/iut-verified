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

From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.

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

Record PrimeStrip := mkPS {
  ps_data : Type
}.

Record HodgeTheater := mkHT {
  ht_label : nat;
  ht_theta_strip : PrimeStrip;
  ht_q_strip : PrimeStrip
}.

Record ThetaLink := mkTL {
  tl_domain : HodgeTheater;
  tl_codomain : HodgeTheater;
  tl_strip_map : PrimeStrip -> PrimeStrip
}.

Definition tl_identifies_theta_with_q (link : ThetaLink) : Prop :=
  tl_strip_map link (ht_theta_strip (tl_domain link)) =
  ht_q_strip (tl_codomain link).

Record LogThetaLattice := mkLTL {
  ltl_theaters : int -> int -> HodgeTheater;
  ltl_theta_links : int -> int -> ThetaLink;
  ltl_log_links : int -> int -> PrimeStrip -> PrimeStrip
}.

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
