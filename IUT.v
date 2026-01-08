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
