From Coq Require Import Arith Fin Lia List Vector VectorSpec Classical_Prop.
From Mell.Core Require Import Vector.
From Mell.BVAS Require Import RunOrder.
From Mell.Semilinear Require Import Presentation LinearEquations.
From Mell.Order Require Import PeriodicOrder.
From Mell.VAS Require Import Runs Transformer Intraproductions.

Import ListNotations.

Theorem unbounded_gamma_coordinate_witness : forall d
    (system : PlainVAS d) (gamma : ProductionTriple d)
    (index : Fin.t d),
    ~ BoundedGammaCoordinate system gamma index ->
    forall bound : nat,
      exists configuration : NVec d,
        QGamma system gamma configuration /\
        (bound < Vector.nth configuration index)%nat.
Proof.
  intros d system gamma index Hunbounded bound.
  apply NNPP. intro Hnone. apply Hunbounded.
  exists bound. intros configuration Hconfiguration.
  destruct (le_lt_dec (Vector.nth configuration index) bound)
    as [Hle|Hgreater]; [exact Hle|].
  exfalso. apply Hnone. exists configuration. split; assumption.
Qed.

Theorem qgamma_unbounded_strict_comparable_pair : forall d
    (system : PlainVAS d) (gamma : ProductionTriple d)
    (index : Fin.t d),
    ~ BoundedGammaCoordinate system gamma index ->
    exists lower upper : NVec d,
      QGamma system gamma lower /\
      QGamma system gamma upper /\
      nvec_le lower upper /\
      (Vector.nth lower index < Vector.nth upper index)%nat.
Proof.
  intros d system gamma index Hunbounded.
  destruct (@restricted_af_finite_cover_classic
      (NVec d) (QGamma system gamma) nvec_le
      (nvec_le_restricted_afs d (QGamma system gamma)))
    as [basis Hbasis].
  set (bound := List.fold_right Nat.max 0%nat
    (List.map (fun base => Vector.nth (proj1_sig base) index) basis)).
  destruct (unbounded_gamma_coordinate_witness d system gamma index
    Hunbounded bound) as [upper [Hupper Hstrict]].
  destruct (Hbasis (exist _ upper Hupper)) as [base [Hbase Hle]].
  exists (proj1_sig base), upper. repeat split.
  - exact (proj2_sig base).
  - exact Hupper.
  - exact Hle.
  - assert (Hbase_bound :
        (Vector.nth (proj1_sig base) index <= bound)%nat).
    { unfold bound. apply in_fold_right_max. apply in_map_iff.
      exists base. split; [reflexivity | exact Hbase]. }
    lia.
Qed.

Theorem unbounded_coordinate_positive_intraproduction : forall d
    (system : PlainVAS d) (gamma : ProductionTriple d)
    (index : Fin.t d),
    ValidProductionTriple system gamma ->
    ~ BoundedGammaCoordinate system gamma index ->
    exists h : NVec d,
      IntraProduction system gamma h /\
      (0 < Vector.nth h index)%nat.
Proof.
  intros d system gamma index Hvalid Hunbounded.
  destruct (qgamma_unbounded_strict_comparable_pair d system gamma index
    Hunbounded) as [lower [upper [Hlower [Hupper [Hle Hstrict]]]]].
  destruct (lemma_5_6_intraproduction_dominates d system gamma
    lower upper Hvalid Hlower Hupper Hle) as [h [Hh Hdominates]].
  exists h. split; [exact Hh|].
  specialize (Hdominates index). unfold nvec_add in Hdominates.
  rewrite (nth_map2 Nat.add _ _ index index index eq_refl eq_refl)
    in Hdominates.
  lia.
Qed.

Fixpoint fin_index_list (d : nat) : list (Fin.t d) :=
  match d return list (Fin.t d) with
  | 0 => []
  | S tail => Fin.F1 :: List.map Fin.FS (fin_index_list tail)
  end.

Lemma fin_index_list_complete : forall d (index : Fin.t d),
    List.In index (fin_index_list d).
Proof.
  intros d. induction d as [|tail IH].
  - intro index. exact (Fin.case0 (fun index =>
      List.In index (fin_index_list 0)) index).
  - intro index. refine (Fin.caseS' index
      (fun index => List.In index (fin_index_list (S tail))) _ _).
    + left. reflexivity.
    + intro inner. right. apply in_map, IH.
Qed.

Lemma intraproduction_positive_on_unbounded_list : forall d
    (system : PlainVAS d) (gamma : ProductionTriple d),
    ValidProductionTriple system gamma ->
    forall indices : list (Fin.t d),
      exists h : NVec d,
        IntraProduction system gamma h /\
        forall index,
          List.In index indices ->
          ~ BoundedGammaCoordinate system gamma index ->
          (0 < Vector.nth h index)%nat.
Proof.
  intros d system gamma Hvalid indices.
  induction indices as [|head tail IH].
  - exists (nvec_zero d). split.
    + apply intraproduction_zero.
    + intros index Hin. contradiction.
  - destruct IH as [tail_h [Htail_h Htail_positive]].
    destruct (classic (BoundedGammaCoordinate system gamma head))
      as [Hbounded|Hunbounded].
    + exists tail_h. split; [exact Htail_h|].
      intros index [Heq|Hin] Hindex_unbounded.
      * subst index. contradiction.
      * now apply Htail_positive.
    + destruct (unbounded_coordinate_positive_intraproduction d system gamma
        head Hvalid Hunbounded) as [head_h [Hhead_h Hhead_positive]].
      exists (nvec_add head_h tail_h). split.
      * now apply intraproduction_add.
      * intros index [Heq|Hin] Hindex_unbounded.
        -- subst index. unfold nvec_add.
           rewrite (nth_map2 Nat.add _ _ head head head eq_refl eq_refl).
           lia.
        -- specialize (Htail_positive index Hin Hindex_unbounded).
           unfold nvec_add.
           rewrite (nth_map2 Nat.add _ _ index index index eq_refl eq_refl).
           lia.
Qed.

Theorem intraproduction_positive_on_all_unbounded : forall d
    (system : PlainVAS d) (gamma : ProductionTriple d),
    ValidProductionTriple system gamma ->
    exists h : NVec d,
      IntraProduction system gamma h /\
      forall index : Fin.t d,
        ~ BoundedGammaCoordinate system gamma index ->
        (0 < Vector.nth h index)%nat.
Proof.
  intros d system gamma Hvalid.
  destruct (intraproduction_positive_on_unbounded_list d system gamma Hvalid
    (fin_index_list d)) as [h [Hh Hpositive]].
  exists h. split; [exact Hh|].
  intros index Hunbounded. apply Hpositive; [apply fin_index_list_complete|].
  exact Hunbounded.
Qed.

Theorem lemma_5_7_bounded_coordinates_intraproduction : forall d
    (system : PlainVAS d) (gamma : ProductionTriple d),
    ValidProductionTriple system gamma ->
    exists h : NVec d,
      IntraProduction system gamma h /\
      forall index : Fin.t d,
        (BoundedGammaCoordinate system gamma index <->
         Vector.nth h index = 0%nat).
Proof.
  intros d system gamma Hvalid.
  destruct (intraproduction_positive_on_all_unbounded d system gamma Hvalid)
    as [h [Hh Hpositive]].
  exists h. split; [exact Hh|]. intro index. split.
  - intro Hbounded. now apply bounded_coordinate_intraproduction_zero
      with (system := system) (gamma := gamma).
  - intro Hzero. destruct (classic
      (BoundedGammaCoordinate system gamma index)) as [Hbounded|Hunbounded].
    + exact Hbounded.
    + specialize (Hpositive index Hunbounded). lia.
Qed.

Corollary bounded_coordinate_add_intraproduction : forall d
    (system : PlainVAS d) (gamma : ProductionTriple d)
    (configuration h : NVec d) (index : Fin.t d),
    QGamma system gamma configuration ->
    IntraProduction system gamma h ->
    BoundedGammaCoordinate system gamma index ->
    Vector.nth (nvec_add configuration h) index =
      Vector.nth configuration index.
Proof.
  intros d system gamma configuration h index _ Hh Hbounded.
  pose proof (bounded_coordinate_intraproduction_zero d system gamma
    index h Hbounded Hh) as Hzero.
  unfold nvec_add.
  rewrite (nth_map2 Nat.add _ _ index index index eq_refl eq_refl), Hzero.
  lia.
Qed.

Theorem lemma_5_7_unbounded_coordinate_growth : forall d
    (system : PlainVAS d) (gamma : ProductionTriple d),
    ValidProductionTriple system gamma ->
    exists h : NVec d,
      IntraProduction system gamma h /\
      (forall index : Fin.t d,
        BoundedGammaCoordinate system gamma index <->
        Vector.nth h index = 0%nat) /\
      forall configuration,
        QGamma system gamma configuration ->
        forall index : Fin.t d,
          ~ BoundedGammaCoordinate system gamma index ->
          forall bound : nat,
            exists multiplier : nat,
              (bound < Vector.nth
                (nvec_add configuration (nvec_scale multiplier h))
                index)%nat /\
              QGamma system gamma
                (nvec_add configuration (nvec_scale multiplier h)).
Proof.
  intros d system gamma Hvalid.
  destruct (lemma_5_7_bounded_coordinates_intraproduction d system gamma
    Hvalid) as [h [Hh Hcharacterization]].
  exists h. split; [exact Hh|]. split; [exact Hcharacterization|].
  intros configuration Hconfiguration index Hunbounded bound.
  exists (S bound). split.
  - assert (Hpositive : (0 < Vector.nth h index)%nat).
    { destruct (Vector.nth h index) eqn:Hcoordinate; [|lia].
      exfalso. apply Hunbounded. apply (proj2 (Hcharacterization index)).
      exact Hcoordinate. }
    unfold nvec_add, nvec_scale.
    rewrite (nth_map2 Nat.add _ _ index index index eq_refl eq_refl),
      (nth_map _ _ index index eq_refl).
    nia.
  - eapply lemma_5_5_qgamma_add_intraproduction_nsmul; eauto.
Qed.
