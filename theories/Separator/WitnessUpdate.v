From Coq Require Import Classical_Prop Lia Lra List Program.Equality QArith Qabs
  Sorting.Permutation Vector Wellfounded.Lexicographic_Product ZArith.
From KruskalAfProp Require Import af.af af.af_tools af.af_ramsey.
From Mell.Core Require Import Vector.
From Mell.BVAS Require Import System Runs Contexts RunOrder.
From Mell.BVAS Require Import OneSourceReduction.
From Mell.Geometry Require Import ClosedLinearization Cone MathCompBridge
  QConeCore Periodic RationalClosure RationalDefinability RationalHToV.
From Mell.Geometry Require Import ClosedLinearizationL2 LatticeGordanV
  LatticeGordanInterface QIntegerHRep.
From Mell.Geometry Require Import RationalConeAssembly.
From Mell.Geometry Require Import FaceStrippingDiagonal FaceStrippingExtract
  FaceStrippingFinitary FaceStrippingLemma610 FaceStrippingLemma611 FaceStrippingRecursion
  FaceStrippingSection6 FaceStrippingTheorem.
From Mell.Geometry Require Import FaceStrippingOrderFoundation FiniteFaces Faces.
From Mell.Geometry Require Import FaceDimension.
From Mell.Order Require Import PeriodicOrder.
From Mell.Order Require Import FiniteBasis.
From Mell.Separator Require Import Attractor DirectedRuns SafetyWitness
  RankDecrease DoubledRelation FiniteGraph SafeLinearization TransformerPeriod.
From Mell.WSVAS Require Import BVASSimulation SafeLinearization.
From Mell.VAS Require Import AlmostSemilinearProjection Intraproductions
  PeriodicIntersection.
From Mell.Semilinear Require Import Closure Presentation.

Import ListNotations.
Module StdVector := Coq.Vectors.Vector.

(** A finitely generated integer period contained in the nonnegative
    orthant has the expected one-component semilinear presentation after
    restriction along [nvec_to_zvec].  Keeping this bridge explicit avoids
    selecting a presentation for an arbitrary semilinear set. *)
Definition nonnegative_zvec_to_nvec {d} (value : ZVec d) : NVec d :=
  StdVector.map Z.to_nat value.

Lemma nonnegative_zvec_roundtrip : forall d (value : ZVec d),
  (forall index, (0 <= StdVector.nth value index)%Z) ->
  nvec_to_zvec (nonnegative_zvec_to_nvec value) = value.
Proof.
  intros d value Hnonnegative.
  apply zvec_ext. intro index.
  unfold nvec_to_zvec, nonnegative_zvec_to_nvec.
  rewrite (StdVector.nth_map Z.of_nat _ index index eq_refl),
    (StdVector.nth_map Z.to_nat _ index index eq_refl).
  now rewrite Z2Nat.id.
Qed.

Lemma nvec_to_zvec_injective_update : forall d (left right : NVec d),
  nvec_to_zvec left = nvec_to_zvec right -> left = right.
Proof.
  intros d left right Heq.
  apply (proj1 (StdVector.eq_nth_iff nat d left right)).
  intros index other Heq_index. subst other.
  apply (f_equal (fun value => StdVector.nth value index)) in Heq.
  unfold nvec_to_zvec in Heq.
  repeat rewrite (StdVector.nth_map Z.of_nat _ index index eq_refl) in Heq.
  now apply Nat2Z.inj.
Qed.

Lemma nonnegative_generated_generators : forall d (set : ZSet d)
    generators,
  (forall generator, List.In generator generators -> set generator) ->
  NonnegativeSet set ->
  List.Forall
    (fun generator => forall index,
      (0 <= StdVector.nth generator index)%Z)
    generators.
Proof.
  intros d set generators Hsound Hnonnegative.
  apply List.Forall_forall. intros generator Hin index.
  now apply Hnonnegative, Hsound.
Qed.

Lemma weighted_sum_nonnegative_generators : forall d
    (generators : list (ZVec d)) coefficients,
  List.Forall
    (fun generator => forall index,
      (0 <= StdVector.nth generator index)%Z)
    generators ->
  length coefficients = length generators ->
  exists contribution,
    weighted_sum coefficients
      (List.map nonnegative_zvec_to_nvec generators) = Some contribution /\
    nvec_to_zvec contribution =
      zvec_linear_combination generators coefficients.
Proof.
  intros d generators. induction generators as [|generator generators IH];
    intros coefficients Hnonnegative Hlength.
  - destruct coefficients; [|discriminate].
    exists (nvec_zero d). split; [reflexivity|].
    apply zvec_ext. intro index. unfold nvec_to_zvec, nvec_zero, zvec_zero.
    cbn.
    rewrite (StdVector.nth_map Z.of_nat _ index index eq_refl),
      (StdVector.const_nth nat 0%nat d index).
    change (0%Z = StdVector.nth (StdVector.const 0%Z d) index).
    symmetry. apply (StdVector.const_nth Z 0%Z d index).
  - inversion Hnonnegative as [|? ? Hgenerator Hgenerators]; subst.
    destruct coefficients as [|coefficient coefficients]; [discriminate|].
    cbn in Hlength. injection Hlength as Hlength.
    destruct (IH coefficients Hgenerators Hlength)
      as [tail [Htail Htail_exact]].
    exists (nvec_add
      (nvec_scale coefficient (nonnegative_zvec_to_nvec generator)) tail).
    split.
    + cbn. now rewrite Htail.
    + rewrite nvec_to_zvec_add, Htail_exact, nvec_scale_to_zvec,
        nonnegative_zvec_roundtrip by exact Hgenerator.
      reflexivity.
Qed.

Lemma weighted_sum_some_lengths : forall d coefficients
    (periods : list (NVec d)) value,
  weighted_sum coefficients periods = Some value ->
  length coefficients = length periods.
Proof.
  intros d coefficients. induction coefficients as [|coefficient coefficients IH];
    intros periods value Hsum; destruct periods as [|period periods];
    cbn in Hsum; try discriminate; auto.
  destruct (weighted_sum coefficients periods) as [tail|] eqn:Htail;
    try discriminate.
  cbn. f_equal. exact (IH periods tail Htail).
Qed.

Lemma generated_nonnegative_semilinear : forall d (set : ZSet d),
  FinitelyGeneratedPeriodic set ->
  NonnegativeSet set ->
  Semilinear (fun value : NVec d => set (nvec_to_zvec value)).
Proof.
  intros d set [generators [Hsound Hgenerated]] Hnonnegative.
  exists [((nvec_zero d),
    List.map nonnegative_zvec_to_nvec generators)]. intro value.
  unfold denote. split.
  - intro Hvalue.
    apply (proj1 (Hgenerated (nvec_to_zvec value))) in Hvalue.
    destruct Hvalue as [coefficients Hcoefficients].
    exists (nvec_zero d,
      List.map nonnegative_zvec_to_nvec generators). split; [now left|].
    unfold linear_denote; cbn.
    destruct (weighted_sum_nonnegative_generators d generators
      (StdVector.to_list coefficients)
      (nonnegative_generated_generators d set generators Hsound Hnonnegative))
      as [contribution [Hsum Hcontribution]].
    + now rewrite length_to_list.
    + exists (StdVector.to_list coefficients), contribution. split;
        [exact Hsum|].
      rewrite nvec_add_zero_left.
      apply nvec_to_zvec_injective_update.
      rewrite Hcontribution, Hcoefficients. reflexivity.
  - intros [component [[Hcomponent|Hfalse] Hlinear]]; [|contradiction].
    subst component. unfold linear_denote in Hlinear; cbn in Hlinear.
    destruct Hlinear as [coefficients [contribution [Hsum Hvalue]]].
    subst value. rewrite nvec_add_zero_left.
    apply (proj2 (Hgenerated (nvec_to_zvec contribution))).
    assert (Hlength : length coefficients = length generators).
    { pose proof (weighted_sum_some_lengths d coefficients
        (List.map nonnegative_zvec_to_nvec generators) contribution Hsum)
        as Hlength. now rewrite length_map in Hlength. }
    pose proof (weighted_sum_nonnegative_generators d generators coefficients
      (nonnegative_generated_generators d set generators Hsound Hnonnegative)
      Hlength) as [expected [Hexpected_sum Hexpected_exact]].
    rewrite Hsum in Hexpected_sum. inversion Hexpected_sum; subst expected.
    rewrite Hexpected_exact. now apply zvec_generated_list_coefficients.
Qed.

Lemma cone_of_nonnegative_set_nonnegative : forall d (set : ZSet d),
  NonnegativeSet set ->
  forall point, Cone set point -> forall index, Qle 0 (point index).
Proof.
  intros d set Hnonnegative point [generated [Hgenerated Hpoint]] index.
  assert (Hgenerated_nonnegative : Qle 0 (generated index)).
  { clear Hpoint point. induction Hgenerated.
    - unfold qvec_zero, Qle. cbn. lia.
    - unfold qvec_add, qvec_scale, zvec_to_qvec.
      setoid_replace (0#1) with ((0#1) + (0#1)) by ring.
      apply Qplus_le_compat; [|exact IHHgenerated].
      apply Qmult_le_0_compat; [exact H|].
      change (inject_Z 0 <= inject_Z (StdVector.nth value index)).
      now rewrite <- Zle_Qle; apply Hnonnegative. }
  setoid_rewrite (Hpoint index). exact Hgenerated_nonnegative.
Qed.

Lemma qclosure_nonnegative : forall d (set : QSet d),
  (forall point, set point -> forall index, Qle 0 (point index)) ->
  forall point, QClosure set point -> forall index, Qle 0 (point index).
Proof.
  intros d set Hnonnegative point Hclosure index.
  destruct (Qlt_le_dec (point index) 0) as [Hnegative|Hnonnegative_point];
    [|exact Hnonnegative_point].
  set (delta := - point index).
  assert (Hdelta : 0 < delta).
  { unfold delta. setoid_replace (0#1) with (- (0#1)) by ring.
    now apply Qopp_lt_compat. }
  destruct (Hclosure delta Hdelta) as [approximant [Happroximant Hclose]].
  specialize (Hclose index).
  pose proof (Hnonnegative approximant Happroximant index) as Happrox_nonnegative.
  assert (Hdifference : point index - approximant index < 0).
  { setoid_replace (point index - approximant index)
      with (point index + - approximant index) by ring.
    setoid_replace (0#1) with ((0#1) + (0#1)) by ring.
    apply Qplus_lt_le_compat; [exact Hnegative|].
    setoid_replace (0#1) with (- (0#1)) by ring.
    now apply Qopp_le_compat. }
  rewrite (Qabs_neg _ (Qlt_le_weak _ _ Hdifference)) in Hclose.
  unfold delta in Hclose.
  exfalso. apply (Qlt_not_le _ _ Hclose).
  setoid_replace (- point index) with ((0#1) + - point index) by ring.
  setoid_replace (- (point index - approximant index))
    with (approximant index + - point index) by ring.
  apply Qplus_le_compat; [exact Happrox_nonnegative|apply Qle_refl].
Qed.

Lemma closed_linearization_nonnegative : forall d (set : ZSet d),
  NonnegativeSet set -> NonnegativeSet (ClosedLinearization set).
Proof.
  intros d set Hnonnegative value [_ Hclosure] index.
  pose proof (qclosure_nonnegative d (Cone set)
    (cone_of_nonnegative_set_nonnegative d set Hnonnegative)
    (zvec_to_qvec value) Hclosure index) as Hq.
  unfold zvec_to_qvec in Hq.
  change (inject_Z 0 <= inject_Z (StdVector.nth value index)) in Hq.
  now rewrite <- Zle_Qle in Hq.
Qed.

Lemma singleton_nset_semilinear : forall d (base : NVec d),
  Semilinear (fun value => value = base).
Proof.
  intros d base. exists [(base, [])]. intro value. split.
  - intro Hvalue. subst value. exists (base, []). split; [now left|].
    unfold linear_denote; cbn. exists [], (nvec_zero d). split;
      [reflexivity|]. now rewrite nvec_add_zero_right.
  - intros [component [[Hcomponent|Hfalse] Hlinear]]; [|contradiction].
    subst component. unfold linear_denote in Hlinear; cbn in Hlinear.
    destruct Hlinear as [coefficients [contribution [Hsum Hvalue]]].
    destruct coefficients; [|discriminate]. inversion Hsum; subst contribution.
    now rewrite nvec_add_zero_right in Hvalue.
Qed.

Lemma nset_translate_semilinear : forall d (base : NVec d)
    (set : NVec d -> Prop),
  Semilinear set -> Semilinear (NSetTranslate base set).
Proof.
  intros d base set Hset.
  pose proof (semilinear_minkowski_sum d
    (fun value => value = base) set
    (singleton_nset_semilinear d base) Hset) as Hsum.
  destruct Hsum as [code Hcode]. exists code. intro value.
  transitivity (exists left right,
    left = base /\ set right /\ value = nvec_add left right).
  - unfold NSetTranslate. split.
    + intros [offset [Hoffset Hvalue]]. subst value.
      exists base, offset. repeat split; auto.
    + intros [left [right [Hleft [Hright Hvalue]]]]. subst left value.
      now exists right.
  - apply Hcode.
Qed.

Lemma finite_translate_union_semilinear : forall d
    (bases : list (NVec d)) (set : NVec d -> Prop),
  Semilinear set ->
  Semilinear (fun value => exists base,
    List.In base bases /\ NSetTranslate base set value).
Proof.
  intros d bases set Hset.
  assert (Hall : List.Forall Semilinear
      (List.map (fun base => NSetTranslate base set) bases)).
  { apply List.Forall_map, List.Forall_forall.
    intros base _. now apply nset_translate_semilinear. }
  destruct (semilinear_finite_union d
    (List.map (fun base => NSetTranslate base set) bases) Hall)
    as [code Hcode].
  exists code. intro value. rewrite <- Hcode. split.
  - intros [base [Hbase Hvalue]]. exists (NSetTranslate base set). split.
    + apply in_map_iff. exists base. now split.
    + exact Hvalue.
  - intros [translated [Hin Hvalue]]. apply in_map_iff in Hin.
    destruct Hin as [base [Htranslated Hbase]]. subst translated.
    now exists base.
Qed.

Lemma afs_intersection : forall X (P : X -> Prop) R S,
  afs P R -> afs P S ->
  afs P (fun left right => R left right /\ S left right).
Proof.
  intros X P R S HR HS. apply af_sub_rel_afs.
  exact (af_inter (afs_af_sub_rel HR) (afs_af_sub_rel HS)).
Qed.

Corollary restricted_intersection_finite_cover : forall X
    (P : X -> Prop) R S,
  afs P R -> afs P S ->
  exists basis : list {x : X | P x},
    forall x : {x : X | P x},
      exists b, List.In b basis /\
        R (proj1_sig b) (proj1_sig x) /\
        S (proj1_sig b) (proj1_sig x).
Proof.
  intros X P R S HR HS.
  destruct (restricted_wqo_finite_cover X P
    (fun left right => R left right /\ S left right)
    (afs_intersection X P R S HR HS)) as [basis Hbasis].
  exists basis. exact Hbasis.
Qed.

Lemma finite_predicate_unique_image : forall A B (items : list A)
    (predicate : A -> Prop) (relation : A -> B -> Prop),
  (forall item, List.In item items -> exists value, relation item value) ->
  (forall item left right,
    relation item left -> relation item right -> left = right) ->
  exists values : list B,
    forall value, List.In value values <->
      exists item, List.In item items /\ predicate item /\ relation item value.
Proof.
  intros A B items. induction items as [|item items IH];
    intros predicate relation Htotal Hunique.
  - exists []. intro value. split; [contradiction|].
    intros [found [Hin _]]. contradiction.
  - assert (Htail : forall found, List.In found items ->
        exists value, relation found value).
    { intros found Hin. apply Htotal. now right. }
    destruct (IH predicate relation Htail Hunique) as [values Hvalues].
    destruct (classic (predicate item)) as [Hitem|Hitem].
    + destruct (Htotal item ltac:(now left)) as [head Hhead].
      exists (head :: values). intro value. split.
      * intro Hmember. destruct Hmember as [Heq|Htail_member].
        -- subst value. exists item. split; [now left|].
           split; assumption.
        -- apply Hvalues in Htail_member.
           destruct Htail_member as [found [Hfound_in [HP HR]]].
           exists found. split; [now right|]. split; assumption.
      * intro Hexists.
        destruct Hexists as
          [candidate [Hcandidate_in [Hcandidate_predicate Hcandidate_relation]]].
        destruct Hcandidate_in as [Heq|Hin].
        -- subst candidate. left.
           now apply Hunique with (item := item).
        -- right. apply Hvalues. exists candidate. auto.
    + exists values. intro value. rewrite Hvalues. split.
      * intros [found [Hin [HP HR]]]. exists found. split; [now right|].
        now split.
      * intros [found [Hfound_in [HP HR]]].
        destruct Hfound_in as [Heq|Hin].
        -- subst found. contradiction.
        -- exists found. auto.
Qed.

Definition BottomSCCBase {d} {system : IBVAS d}
    (nodes : list (DirectedIRun system))
    (root : WitnessVertex nodes) (base : NVec d) : Prop :=
  exists vertex node,
    BottomSCC (WitnessEdge nodes) root vertex /\
    witness_vertex_node nodes vertex node /\
    base = irun_target (directed_root node).

Lemma bottom_scc_bases_finite : forall d (system : IBVAS d)
    (nodes : list (DirectedIRun system)) root,
  exists bases : list (NVec d),
    forall base, List.In base bases <-> BottomSCCBase nodes root base.
Proof.
  intros d system nodes root.
  destruct (finite_predicate_unique_image
    (WitnessVertex nodes) (NVec d) (finite_vertices (length nodes))
    (BottomSCC (WitnessEdge nodes) root)
    (fun vertex base => exists node,
      witness_vertex_node nodes vertex node /\
      base = irun_target (directed_root node))) as [bases Hbases].
  - intros vertex _. destruct (witness_vertex_node_exists d system nodes vertex)
      as [node Hnode]. exists (irun_target (directed_root node)), node.
    now split.
  - intros vertex left right [left_node [Hleft_node Hleft]]
      [right_node [Hright_node Hright]].
    unfold witness_vertex_node in Hleft_node, Hright_node.
    assert (left_node = right_node) by congruence. subst right_node.
    congruence.
  - exists bases. intro base. rewrite Hbases. unfold BottomSCCBase. split.
    + intros [vertex [_ [Hbottom [node [Hnode Hbase]]]]].
      exists vertex, node. auto.
    + intros [vertex [node [Hbottom [Hnode Hbase]]]].
      exists vertex. split; [apply finite_vertices_complete|].
      split; [exact Hbottom|]. exists node. now split.
Qed.

Definition BottomSCCPeriod {d} {system : IBVAS d}
    (representative : DirectedIRun system) : NVec d -> Prop :=
  fun offset => DirectedClosedPeriod representative (nvec_to_zvec offset).

Lemma bottom_scc_period_periodic : forall d (system : IBVAS d)
    (representative : DirectedIRun system),
  PeriodicNSet (BottomSCCPeriod representative).
Proof.
  intros d system representative. unfold BottomSCCPeriod.
  pose proof (closed_linearization_periodic d
    (DirectedPeriod representative)
    (directed_period_periodic d system representative)) as Hperiodic.
  split.
  - rewrite nvec_zero_to_zvec. exact (proj1 Hperiodic).
  - intros left right Hleft Hright.
    rewrite nvec_to_zvec_add. now apply (proj2 Hperiodic).
Qed.

Definition BottomSCCRegion {d} {system : IBVAS d}
    (nodes : list (DirectedIRun system)) (root : WitnessVertex nodes)
    (representative : DirectedIRun system) : NVec d -> Prop :=
  fun value => exists base,
    BottomSCCBase nodes root base /\
    NSetTranslate base (BottomSCCPeriod representative) value.

Lemma bottom_scc_region_finitary : forall d (system : IBVAS d)
    (nodes : list (DirectedIRun system)) root representative,
  exists bases : list (NVec d),
    forall value,
      BottomSCCRegion nodes root representative value <->
      exists base, List.In base bases /\
        NSetTranslate base (BottomSCCPeriod representative) value.
Proof.
  intros d system nodes root representative.
  destruct (bottom_scc_bases_finite d system nodes root) as [bases Hbases].
  exists bases. intro value. unfold BottomSCCRegion. setoid_rewrite <- Hbases.
  reflexivity.
Qed.

Lemma has_source_forall_source_shuffle : forall d
    (X I : NVec d -> Prop) word,
  HasSource X word -> List.Forall I word -> SourceShuffle X I word.
Proof.
  intros d X I word [value [Hin HX]] Hall.
  apply in_split in Hin as [prefix [suffix ->]].
  apply List.Forall_app in Hall as [Hprefix Hrest].
  inversion Hrest as [|? ? Hvalue Hsuffix]; subst.
  exists prefix, value, suffix. repeat split; assumption.
Qed.

Lemma source_multi_shuffle_all_right : forall d
    (X I : NVec d -> Prop) word,
  SourceMultiShuffle X I word ->
  (forall value, X value -> I value) ->
  List.Forall I word.
Proof.
  intros d X I word Hmulti Hsub.
  destruct (source_multi_shuffle_characterization d X I word Hmulti)
    as [Hall _].
  eapply List.Forall_impl; [|exact Hall]. firstorder.
Qed.

Lemma source_multi_shuffle_monotone_update : forall d
    (left left' right right' : NSet d) word,
  (forall value, left value -> left' value) ->
  (forall value, right value -> right' value) ->
  SourceMultiShuffle left right word ->
  SourceMultiShuffle left' right' word.
Proof.
  intros d left left' right right' word Hleft Hright
    [specials [others [Hnonempty [Hspecials [Hothers Hperm]]]]].
  exists specials, others. repeat split; try assumption.
  - eapply List.Forall_impl; [|exact Hspecials]. exact Hleft.
  - eapply List.Forall_impl; [|exact Hothers]. exact Hright.
Qed.

Section MarkedSubstitution.
Context {d : nat} (system : IBVAS d).
Variables X I R : NVec d -> Prop.

Lemma marked_free_substitute : forall outer,
  MarkedFreeIRun system R I outer ->
  (forall value, R value ->
    exists inner,
      ValidFreeIRun system inner /\
      irun_target inner = value /\
      SourceMultiShuffle X I (free_irun_sources inner)) ->
  exists result,
    ValidFreeIRun system result /\
    irun_target result = irun_target outer /\
    SourceMultiShuffle X I (free_irun_sources result).
Proof.
  intros outer Hmarked Hreplace.
  induction Hmarked as
    [value HR|action before main after target Haction Hbefore Hafter
      HbeforeI HafterI Hmain IH Happly].
  - now apply Hreplace.
  - destruct IH as [middle [Hmiddle [Hmiddle_target Hsources]]].
    exists (irun_node action
      (iruns_append before (iruns_cons middle after)) target).
    split.
    + constructor; [exact Haction| |].
      * apply valid_free_iruns_append; [exact Hbefore|].
        constructor; assumption.
      * repeat rewrite iruns_targets_append_free in Happly |- *. cbn in *.
        now rewrite Hmiddle_target.
    + split; [reflexivity|]. cbn. rewrite free_iruns_sources_append. cbn.
      apply source_multi_shuffle_partition.
      * apply List.Forall_app. split.
        -- eapply List.Forall_impl; [|exact HbeforeI]. firstorder.
        -- apply List.Forall_app. split.
           ++ eapply source_multi_shuffle_forall in Hsources as [Hall _].
              eapply List.Forall_impl; [|exact Hall]. firstorder.
           ++ eapply List.Forall_impl; [|exact HafterI]. firstorder.
      * destruct (source_multi_shuffle_forall d X I
          (free_irun_sources middle) Hsources) as [_ [value [Hin HX]]].
        exists value. split; [|exact HX].
        apply in_or_app. right. apply in_or_app. left. exact Hin.
Qed.

End MarkedSubstitution.

Section MultiSubstitution.
Context {d : nat} (system : IBVAS d).
Variables X I R : NVec d -> Prop.
Hypothesis replace_R : forall value, R value ->
  exists inner,
    ValidFreeIRun system inner /\
    irun_target inner = value /\
    SourceMultiShuffle X I (free_irun_sources inner).

Definition ExpandedRun (run : IRun d) : Prop :=
  exists result,
    ValidFreeIRun system result /\
    irun_target result = irun_target run /\
    (HasSource R (free_irun_sources run) ->
      SourceMultiShuffle X I (free_irun_sources result)) /\
    (~ HasSource R (free_irun_sources run) ->
      List.Forall I (free_irun_sources result)).

Definition ExpandedRuns (runs : IRuns d) : Prop :=
  exists results,
    ValidFreeIRuns system results /\
    iruns_targets results = iruns_targets runs /\
    (HasSource R (free_iruns_sources runs) ->
      SourceMultiShuffle X I (free_iruns_sources results)) /\
    (~ HasSource R (free_iruns_sources runs) ->
      List.Forall I (free_iruns_sources results)).

Lemma multi_substitute_runs :
  (forall run, ValidFreeIRun system run ->
    List.Forall (fun value => R value \/ I value)
      (free_irun_sources run) -> ExpandedRun run) /\
  (forall runs, ValidFreeIRuns system runs ->
    List.Forall (fun value => R value \/ I value)
      (free_iruns_sources runs) -> ExpandedRuns runs).
Proof.
  apply ValidFreeIRun_IRuns_ind.
  - intros value Hall. cbn in Hall.
    inversion Hall as [|? ? Hvalue Hnil]; subst.
    destruct (classic (R value)) as [HR|HnotR].
    + destruct (replace_R value HR) as [inner [Hinner [Htarget Hmulti]]].
      exists inner. split; [exact Hinner|]. split; [exact Htarget|]. split.
      * intro Hignored. exact Hmulti.
      * intro Hnone. exfalso. apply Hnone. exists value. cbn. auto.
    + exists (irun_leaf value). split; [constructor|]. split; [reflexivity|].
      split.
      * intro Hsource. destruct Hsource as [found [Hin Hfound]].
        destruct Hin as [Heq|Hfalse].
        -- subst found. contradiction.
        -- contradiction.
      * intro Hignored. constructor; [tauto|constructor].
  - intros action children target Haction Hchildren IH Happly Hall.
    unfold ExpandedRun.
    destruct (IH Hall) as [results [Hresults [Htargets [Hhas Hnone]]]].
    exists (irun_node action results target). split.
    + constructor; [exact Haction|exact Hresults|]. now rewrite Htargets.
    + split; [reflexivity|]. split.
      * cbn. exact Hhas.
      * cbn. exact Hnone.
  - intros Hall. exists iruns_nil. split; [constructor|]. split;
      [reflexivity|]. split.
    + intros [value [[] Hvalue]].
    + intro Hignored. constructor.
  - intros run runs Hrun IHrun Hruns IHruns Hall.
    cbn in Hall. apply List.Forall_app in Hall as [Hrun_sources Hruns_sources].
    destruct (IHrun Hrun_sources) as
      [new_run [Hnew_run [Hnew_target [Hrun_has Hrun_none]]]].
    destruct (IHruns Hruns_sources) as
      [new_runs [Hnew_runs [Hnew_targets [Hruns_has Hruns_none]]]].
    exists (iruns_cons new_run new_runs). split; [constructor; assumption|].
    split; [cbn; now rewrite Hnew_target, Hnew_targets|]. split.
    + cbn. intro Hsome.
      apply has_source_app in Hsome as [Hsome|Hsome].
      * destruct (source_multi_shuffle_characterization d X I _
          (Hrun_has Hsome)) as [Hrun_all Hrun_X].
        assert (Htail_all : List.Forall (fun value => X value \/ I value)
            (free_iruns_sources new_runs)).
        { destruct (classic (HasSource R (free_iruns_sources runs)))
            as [Htail_R|Htail_R].
          - exact (proj1 (source_multi_shuffle_characterization d X I _
              (Hruns_has Htail_R))).
          - eapply (@List.Forall_impl _ I
              (fun value => X value \/ I value)).
            + intros value Hvalue. now right.
            + exact (Hruns_none Htail_R). }
        apply source_multi_shuffle_partition.
        -- apply List.Forall_app. split; assumption.
        -- apply (proj2 (has_source_app d X _ _)). left. exact Hrun_X.
      * destruct (source_multi_shuffle_characterization d X I _
          (Hruns_has Hsome)) as [Htail_all Htail_X].
        assert (Hrun_all : List.Forall (fun value => X value \/ I value)
            (free_irun_sources new_run)).
        { destruct (classic (HasSource R (free_irun_sources run)))
            as [Hrun_R|Hrun_R].
          - exact (proj1 (source_multi_shuffle_characterization d X I _
              (Hrun_has Hrun_R))).
          - eapply (@List.Forall_impl _ I
              (fun value => X value \/ I value)).
            + intros value Hvalue. now right.
            + exact (Hrun_none Hrun_R). }
        apply source_multi_shuffle_partition.
        -- apply List.Forall_app. split; assumption.
        -- apply (proj2 (has_source_app d X _ _)). right. exact Htail_X.
    + cbn. intro Hnone_all. apply List.Forall_app. split.
      * apply Hrun_none. intro Hrun_R. apply Hnone_all.
        apply (proj2 (has_source_app d R _ _)). now left.
      * apply Hruns_none. intro Hruns_R. apply Hnone_all.
        apply (proj2 (has_source_app d R _ _)). now right.
Qed.

End MultiSubstitution.

Theorem lemma_3_7_attractor_extension : forall d
    (system : IBVAS d) (attractor invariant X : NVec d -> Prop),
  Attractor system attractor ->
  IBVASInductiveInvariant system invariant ->
  (forall value, attractor value -> invariant value) ->
  Attractor system
    (fun value => attractor value \/
      ReachFromNonemptyShuffle system X invariant value).
Proof.
  intros d system attractor invariant X Hattr Hinvariant HA.
  set (R := fun value => ReachFromNonemptyShuffle system X invariant value).
  assert (HreachI : forall value, Reach system value -> invariant value).
  { exact (proj1 (reach_in_inductive_invariant d system invariant Hinvariant)). }
  intros target [outer [Houter [Htarget Hmulti]]].
  destruct (source_multi_shuffle_characterization d
    (fun value => attractor value \/ R value) (Reach system)
    (free_irun_sources outer) Hmulti) as [Hall Hhas].
  destruct (classic (HasSource R (free_irun_sources outer))) as [HR|HnoR].
  - right. unfold R.
    assert (HallRI : List.Forall (fun value => R value \/ invariant value)
        (free_irun_sources outer)).
    { eapply List.Forall_impl; [|exact Hall].
      intros value [[HAv|HRv]|Hreach]; [right; now apply HA|now left|].
      right. now apply HreachI. }
    destruct (proj1 (multi_substitute_runs system X invariant R
      ltac:(intros value [inner [Hvalid [Hinner_target Hsources]]];
        exists inner; auto)) outer Houter HallRI)
      as [result [Hresult [Hresult_target [Hresult_multi _]]]].
    exists result. split; [exact Hresult|]. split.
    + now rewrite Hresult_target, Htarget.
    + exact (Hresult_multi HR).
  - left. apply Hattr. exists outer. split; [exact Houter|].
    split; [exact Htarget|]. apply source_multi_shuffle_partition.
    + apply (forall_union_no_source d R
        (fun value => attractor value \/ Reach system value)
        (free_irun_sources outer)).
      * eapply List.Forall_impl; [|exact Hall].
        intros value [[HAv|HRv]|Hreach].
        -- right. now left.
        -- now left.
        -- right. now right.
      * exact HnoR.
    + destruct Hhas as [value [Hin [HAv|HRv]]].
      * exists value. split; assumption.
      * exfalso. apply HnoR. exists value. split; assumption.
Qed.

Theorem attractor_extension_absorbed_sources : forall d
    (system : IBVAS d) (attractor invariant X : NVec d -> Prop),
  Attractor system attractor ->
  IBVASInductiveInvariant system invariant ->
  (forall value, attractor value -> invariant value) ->
  (forall value, X value -> invariant value) ->
  Attractor system
    (fun value => attractor value \/
      ReachFromNonemptyShuffle system X invariant value).
Proof.
  intros d system attractor invariant X Hattr Hinvariant HA HX.
  set (R := fun value => ReachFromNonemptyShuffle system X invariant value).
  assert (HreachI : forall value, Reach system value -> invariant value).
  { exact (proj1 (reach_in_inductive_invariant d system invariant Hinvariant)). }
  assert (Hclosed : ClosedUnderFreeRuns system invariant).
  { now apply inductive_invariant_closed_free_runs. }
  assert (HRsub : forall value, R value -> invariant value).
  { intros value [run [Hvalid [Htarget Hmulti]]]. rewrite <- Htarget.
    apply Hclosed with (run := run); [exact Hvalid|].
    eapply source_multi_shuffle_all_right; [exact Hmulti|exact HX]. }
  intros target [outer [Houter [Htarget Hmulti]]].
  destruct (source_multi_shuffle_characterization d
    (fun value => attractor value \/ R value) (Reach system)
    (free_irun_sources outer) Hmulti) as [Hall Hhas].
  destruct (classic (HasSource R (free_irun_sources outer))) as [Hsome|Hnone].
  - right. unfold R.
    assert (HallI : List.Forall invariant (free_irun_sources outer)).
    { eapply List.Forall_impl; [|exact Hall].
      intros value [[HAvalue|HRvalue]|Hreach];
        [now apply HA|now apply HRsub|now apply HreachI]. }
    assert (Hshuffle : SourceShuffle R invariant (free_irun_sources outer)).
    { now apply has_source_forall_source_shuffle. }
    pose proof (valid_free_source_shuffle_marked system R invariant outer
      Houter Hshuffle) as Hmarked.
    destruct (marked_free_substitute system X invariant R outer Hmarked)
      as [result [Hresult [Hresult_target Hresult_sources]]].
    + intros value [inner [Hinner [Hinner_target Hinner_sources]]].
      exists inner. auto.
    + exists result. split; [exact Hresult|]. split.
      * now rewrite Hresult_target, Htarget.
      * exact Hresult_sources.
  - left. apply Hattr. exists outer. split; [exact Houter|].
    split; [exact Htarget|]. apply source_multi_shuffle_partition.
    + apply List.Forall_forall. intros value Hin.
      apply List.Forall_forall with (x := value) in Hall; [|exact Hin].
      destruct Hall as [[HAvalue|HRvalue]|Hreach].
      * now left.
      * exfalso. apply Hnone. now exists value.
      * now right.
    + destruct Hhas as [value [Hin [HAvalue|HRvalue]]].
      * now exists value.
      * exfalso. apply Hnone. now exists value.
Qed.

Lemma reach_inductive_invariant : forall d (system : IBVAS d),
  IBVASInductiveInvariant system (Reach system).
Proof.
  intros d system. split.
  - intros value Hinitial. now apply initial_is_reachable.
  - intros action children target Haction Hchildren Happly.
    now apply reach_action_in with (action := action) (children := children).
Qed.

Lemma marked_reachable_to_special_leaf : forall d (system : IBVAS d)
    (X : NVec d -> Prop) run,
  MarkedFreeIRun system X (Reach system) run ->
  exists input, X input /\
    SpecialLeafReach system input (irun_target run).
Proof.
  intros d system X run Hmarked. induction Hmarked.
  - exists value. split; [assumption|constructor].
  - destruct IHHmarked as [input [Hinput Hspecial]].
    exists input. split; [exact Hinput|].
    eapply special_action with
      (action := action)
      (prefix := iruns_targets before)
      (middle := irun_target main)
      (suffix := iruns_targets after).
    + exact H.
    + exact (proj2 (inductive_invariant_free_runs system (Reach system)
        (reach_inductive_invariant d system)) before H0 H2).
    + exact Hspecial.
    + exact (proj2 (inductive_invariant_free_runs system (Reach system)
        (reach_inductive_invariant d system)) after H1 H3).
    + cbn.
      replace (iruns_targets before ++ irun_target main :: iruns_targets after)
        with (iruns_targets (iruns_append before (iruns_cons main after))).
      * exact H4.
      * rewrite iruns_targets_append. reflexivity.
Qed.

Lemma reach_from_shuffle_attractor_or_special : forall d
    (system : IBVAS d) (attractor X : NVec d -> Prop) output,
  Attractor system attractor ->
  (forall value, X value -> Reach system value) ->
  ReachFromShuffle system X
    (fun value => attractor value \/ Reach system value) output ->
  attractor output \/
  exists input, X input /\ SpecialLeafReach system input output.
Proof.
  intros d system attractor X output Hattr HXreach
    [run [Hvalid [Htarget Hshuffle]]].
  destruct (classic (HasSource attractor (free_irun_sources run)))
    as [Hhas|Hnone].
  - left. apply Hattr. exists run. split; [exact Hvalid|]. split;
      [exact Htarget|].
    destruct Hshuffle as
      [prefix [special [suffix [Hword [HX [Hprefix Hsuffix]]]]]].
    apply source_multi_shuffle_partition; [|exact Hhas].
    rewrite Hword. apply List.Forall_app. split; [exact Hprefix|]. constructor.
    + right. now apply HXreach.
    + exact Hsuffix.
  - right.
    assert (Hshuffle_reach : SourceShuffle X (Reach system)
        (free_irun_sources run)).
    { destruct Hshuffle as
        [prefix [special [suffix [Hword [HX [Hprefix Hsuffix]]]]]].
      exists prefix, special, suffix. repeat split; auto.
      - apply List.Forall_forall. intros value Hin.
        apply List.Forall_forall with (x := value) in Hprefix; [|exact Hin].
        destruct Hprefix as [HA|HR]; [exfalso|exact HR].
        apply Hnone. exists value. split; [|exact HA].
        rewrite Hword. apply in_or_app. now left.
      - apply List.Forall_forall. intros value Hin.
        apply List.Forall_forall with (x := value) in Hsuffix; [|exact Hin].
        destruct Hsuffix as [HA|HR]; [exfalso|exact HR].
        apply Hnone. exists value. split; [|exact HA].
        rewrite Hword. apply in_or_app. right. now right. }
    pose proof (valid_free_source_shuffle_marked system X (Reach system)
      run Hvalid Hshuffle_reach) as Hmarked.
    destruct (marked_reachable_to_special_leaf d system X run Hmarked)
      as [input [Hinput Hspecial]].
    exists input. split; [exact Hinput|]. now rewrite <- Htarget.
Qed.


(** A [SpecialLeafReach] context can be closed by an attractor.  This is the
    occurrence-sensitive form used in Lemma 7.3. *)
Lemma attractor_special_leaf_closed : forall d (system : IBVAS d)
    (set : NVec d -> Prop) input output,
  Attractor system set -> set input ->
  SpecialLeafReach system input output -> set output.
Proof.
  intros d system set input output Hattr Hinput Hreach.
  induction Hreach as
    [input|input action prefix middle suffix output Haction Hprefix
      Hmiddle IH Hsuffix Happly].
  - exact Hinput.
  - apply Hattr. exists
      (irun_node action (free_leaf_runs (prefix ++ middle :: suffix)) output).
    split.
    + econstructor; [exact Haction|apply free_leaf_runs_valid|].
      now rewrite free_leaf_runs_targets.
    + split; [reflexivity|]. cbn. rewrite free_leaf_runs_sources.
      apply source_multi_shuffle_partition.
      * apply List.Forall_app. split.
        -- eapply List.Forall_impl; [|exact Hprefix]. firstorder.
        -- constructor.
           ++ left. now apply IH.
           ++ eapply List.Forall_impl; [|exact Hsuffix]. firstorder.
      * exists middle. split.
        -- apply in_or_app. right. now left.
        -- now apply IH.
Qed.

(** Rebase a directed initialized run at one of its represented runs while
    retaining the original rational cone. *)
Definition rebase_directed_irun {d} {system : IBVAS d}
    (node : DirectedIRun system) (run : IRun d)
    (member : DirectedRunMember node run) : DirectedIRun system :=
  {| directed_root := run;
     directed_root_valid := proj1 member;
     directed_generators := directed_generators node;
     directed_cone_nonnegative := directed_cone_nonnegative system node |}.

Lemma rebase_directed_cone : forall d (system : IBVAS d)
    (node : DirectedIRun system) run member point,
  DirectedCone (rebase_directed_irun node run member) point <->
  DirectedCone node point.
Proof. reflexivity. Qed.

Lemma nvec_add_cancel_left_exact : forall d
    (base left right : NVec d),
  nvec_add base left = nvec_add base right -> left = right.
Proof.
  intros d base left right Heq.
  apply (proj1 (Vector.eq_nth_iff nat d left right)).
  intros index other Heq_index. subst other.
  apply (f_equal (fun value => Vector.nth value index)) in Heq.
  unfold nvec_add in Heq.
  repeat rewrite (StdVector.nth_map2 _ _ _ index index index eq_refl eq_refl)
    in Heq. lia.
Qed.

Lemma lemma_7_4_directed_irun_rebase_member : forall d
    (system : IBVAS d) (node : DirectedIRun system) run
    (member : DirectedRunMember node run) extension,
  DirectedRunMember (rebase_directed_irun node run member) extension ->
  DirectedRunMember node extension.
Proof.
  intros d system node run member extension Hextension.
  pose proof member as Hmember.
  destruct Hmember as
    [Hrun [base_offset [Hbase_le [Hbase_target Hbase_cone]]]].
  destruct Hextension as
    [Hvalid [offset [Hle [Htarget Hcone]]]].
  cbn in Htarget, Hcone.
  split; [exact Hvalid|].
  exists (nvec_add base_offset offset). split.
  - eapply irun_le_trans; eauto.
  - split.
    + rewrite Htarget, Hbase_target, nvec_add_assoc. reflexivity.
    + unfold DirectedCone in *. apply (proj2
        (qcone_generated_qvec_ext d (directed_generators node)
          (nvec_to_qvec (nvec_add base_offset offset))
          (qvec_add (nvec_to_qvec base_offset) (nvec_to_qvec offset))
          (nvec_to_qvec_add_directed d base_offset offset))).
      apply qcone_generated_add; assumption.
Qed.

Lemma rebase_directed_zero_member : forall d (system : IBVAS d)
    (node : DirectedIRun system) run
    (member : DirectedRunMember node run),
  DirectedRunMember (rebase_directed_irun node run member) run.
Proof.
  intros d system node run member. split; [exact (proj1 member)|].
  exists (nvec_zero d). split; [apply irun_le_refl|]. split.
  - symmetry. apply nvec_add_zero_right.
  - unfold DirectedCone. apply (proj2
      (qcone_generated_qvec_ext d (directed_generators node)
        (nvec_to_qvec (nvec_zero d)) (qvec_zero d)
        (nvec_to_qvec_zero_directed d))).
    apply qcone_generated_zero.
Qed.

Lemma lemma_7_4_directed_irun_rebase_edge : forall d
    (system : IBVAS d) (node : DirectedIRun system) run
    (member : DirectedRunMember node run),
  DirectedIRunEdge (rebase_directed_irun node run member) node.
Proof.
  intros d system node run member.
  exists run, run. split.
  - now apply rebase_directed_zero_member.
  - split; [exact member|]. exists context_hole. reflexivity.
Qed.

Theorem lemma_7_4_directed_irun_rebase : forall d
    (system : IBVAS d) (node : DirectedIRun system) run
    (member : DirectedRunMember node run),
  (forall extension,
      DirectedRunMember (rebase_directed_irun node run member) extension ->
      DirectedRunMember node extension) /\
  (forall value,
      DirectedPeriod (rebase_directed_irun node run member) value ->
      DirectedClosedPeriod node value).
Proof.
  intros d system node run member. split.
  - now apply lemma_7_4_directed_irun_rebase_member.
  - intros value Hvalue.
    eapply lemma_3_13_directed_closed_period_inclusion.
    + now apply lemma_7_4_directed_irun_rebase_edge.
    + intros point Hpoint. exact Hpoint.
    + destruct Hvalue as [natural [-> Hoffset]].
      apply periodic_nset_in_closed_linearization.
      * apply directed_offset_periodic.
      * exact Hoffset.
Qed.

Definition NClosedDirectedPeriod {d} {system : IBVAS d}
    (node : DirectedIRun system) : NVec d -> Prop :=
  fun offset => DirectedClosedPeriod node (nvec_to_zvec offset).

Definition DirectedRootTranslate {d} {system : IBVAS d}
    (node : DirectedIRun system) (period : NVec d -> Prop) : NVec d -> Prop :=
  fun value => exists offset, period offset /\
    value = nvec_add (irun_target (directed_root node)) offset.

Lemma directed_offset_in_closed_period_n : forall d
    (system : IBVAS d) (node : DirectedIRun system) offset,
  DirectedOffset node offset -> NClosedDirectedPeriod node offset.
Proof.
  intros d system node offset Hoffset. unfold NClosedDirectedPeriod.
  apply periodic_nset_in_closed_linearization.
  - apply directed_offset_periodic.
  - exact Hoffset.
Qed.

Theorem lemma_7_3_attractor_contact_propagation : forall d
    (system : IBVAS d) (attractor period : NVec d -> Prop)
    (source target : DirectedIRun system),
  Attractor system attractor ->
  PeriodicNSet period ->
  NSetStable attractor period ->
  DirectedIRunEdge source target ->
  (forall offset,
      NClosedDirectedPeriod source offset <-> period offset) ->
  (forall offset,
      NClosedDirectedPeriod target offset <-> period offset) ->
  (exists value, attractor value /\
      DirectedRootTranslate source period value) ->
  exists value, attractor value /\
    DirectedRootTranslate target period value.
Proof.
  intros d system attractor period source target Hattr Hperiodic Hstable
    [source_run [target_run [Hsource [Htarget Hocc]]]]
    Hsource_period Htarget_period
    [contact [Hcontact [contact_offset [Hcontact_offset Hcontact_eq]]]].
  destruct Hsource as
    [Hsource_valid [source_offset
      [Hsource_le [Hsource_target Hsource_cone]]]].
  destruct Htarget as
    [Htarget_valid [target_offset
      [Htarget_le [Htarget_target Htarget_cone]]]].
  assert (Hsource_offset : period source_offset).
  { apply (proj1 (Hsource_period source_offset)).
    apply directed_offset_in_closed_period_n. split.
    - exists source_run. split; [exact Hsource_valid|].
      split; [exact Hsource_le|exact Hsource_target].
    - exact Hsource_cone. }
  assert (Htarget_offset : period target_offset).
  { apply (proj1 (Htarget_period target_offset)).
    apply directed_offset_in_closed_period_n. split.
    - exists target_run. split; [exact Htarget_valid|].
      split; [exact Htarget_le|exact Htarget_target].
    - exact Htarget_cone. }
  assert (Hsource_contact : attractor
      (nvec_add (irun_target source_run) contact_offset)).
  { pose proof (Hstable contact source_offset Hcontact Hsource_offset)
      as Hshifted.
    rewrite Hcontact_eq in Hshifted.
    rewrite Hsource_target.
    rewrite !nvec_add_assoc in Hshifted |- *.
    replace (nvec_add source_offset contact_offset)
      with (nvec_add contact_offset source_offset) by
      apply nvec_add_comm_period.
    exact Hshifted. }
  assert (Hspecial : SpecialLeafReach system
      (nvec_add (irun_target source_run) contact_offset)
      (nvec_add (irun_target target_run) contact_offset)).
  { apply special_leaf_reach_shift.
    destruct Hocc as [context Hcontext]. subst target_run.
    now apply valid_context_special_leaf. }
  assert (Htarget_contact : attractor
      (nvec_add (irun_target target_run) contact_offset)).
  { eapply attractor_special_leaf_closed; eauto. }
  exists (nvec_add (irun_target target_run) contact_offset). split.
  - exact Htarget_contact.
  - exists (nvec_add target_offset contact_offset). split.
    + apply (proj2 Hperiodic); assumption.
    + rewrite Htarget_target, nvec_add_assoc. reflexivity.
Qed.

Lemma special_leaf_wrap_occurrence : forall d (system : IBVAS d)
    input output (matched : IRun d),
  ValidIRun system matched ->
  irun_target matched = input ->
  SpecialLeafReach system input output ->
  exists whole,
    ValidIRun system whole /\
    irun_target whole = output /\
    IRunOccurrence matched whole.
Proof.
  intros d system input output matched Hmatched Htarget Hreach.
  revert matched Hmatched Htarget.
  induction Hreach as
    [input|input action prefix middle suffix output Haction Hprefix
      Hmiddle IH Hsuffix Happly]; intros matched Hmatched Htarget.
  - exists matched. repeat split; auto. exists context_hole. reflexivity.
  - destruct (IH matched Hmatched Htarget)
      as [middle_run [Hmiddle_valid [Hmiddle_target [inner Hinner]]]].
    destruct (reach_forall_to_valid_iruns d system prefix Hprefix)
      as [before [Hbefore Ebefore]].
    destruct (reach_forall_to_valid_iruns d system suffix Hsuffix)
      as [after [Hafter Eafter]].
    exists (irun_node action
      (iruns_append before (iruns_cons middle_run after)) output).
    split.
    + constructor; [exact Haction| |].
      * apply valid_iruns_append_intro; [exact Hbefore|].
        constructor; assumption.
      * rewrite iruns_targets_append, Ebefore. cbn.
        now rewrite Hmiddle_target, Eafter.
    + split; [reflexivity|].
      exists (context_node action before inner after output).
      cbn. now rewrite Hinner.
Qed.

Definition WitnessSuccessor {d} {system : IBVAS d}
    (nodes : list (DirectedIRun system))
    (source target : DirectedIRun system) : Prop :=
  List.In target nodes /\ DirectedIRunEdge source target.

Theorem lemma_7_2_safety_witness_successors : forall d
    (system : IBVAS d) safe (witness : SafetyWitness system safe)
    source source_run output,
  List.In source (witness_nodes witness) ->
  DirectedRunMember source source_run ->
  SpecialLeafReach system (irun_target source_run) output ->
  witness_attractor witness output \/
  exists target,
    WitnessSuccessor (witness_nodes witness) source target /\
    exists target_run,
      DirectedRunMember target target_run /\
      irun_target target_run = output /\
      IRunOccurrence source_run target_run.
Proof.
  intros d system safe witness source source_run output Hsource_in
    Hsource_member Hreach.
  destruct (special_leaf_wrap_occurrence d system
    (irun_target source_run) output source_run
    (proj1 Hsource_member) eq_refl Hreach)
    as [whole [Hwhole [Hwhole_target Hocc]]].
  destruct (witness_run_coverage system safe witness whole Hwhole)
    as [HA|Hcovered].
  - left. now rewrite <- Hwhole_target.
  - right. destruct Hcovered as [target [Htarget_in Htarget_member]].
    exists target. split.
    + split; [exact Htarget_in|].
      exists source_run, whole. split; [exact Hsource_member|].
      split; assumption.
    + exists whole. split; [exact Htarget_member|].
      split; assumption.
Qed.

Lemma bottom_scc_graph_reach_closed : forall count
    (edge : Fin.t count -> Fin.t count -> Prop) root source target,
  BottomSCC edge root source ->
  GraphReach edge source target ->
  BottomSCC edge root target.
Proof.
  intros count edge root source target Hsource Hpath.
  induction Hpath as [|middle target Hpath IH Hedge].
  - exact Hsource.
  - eapply bottom_scc_closed; [exact IH|exact Hedge].
Qed.

Lemma witness_vertex_node_unique : forall d (system : IBVAS d)
    (nodes : list (DirectedIRun system)) vertex left right,
  witness_vertex_node nodes vertex left ->
  witness_vertex_node nodes vertex right -> left = right.
Proof.
  intros d system nodes vertex left right Hleft Hright.
  unfold witness_vertex_node in *. congruence.
Qed.

Lemma witness_graph_reach_closed_period_inclusion : forall d
    (system : IBVAS d) (nodes : list (DirectedIRun system)) root
    source target source_node target_node,
  HomogeneousWitnessNodes nodes ->
  BottomSCC (WitnessEdge nodes) root source ->
  GraphReach (WitnessEdge nodes) source target ->
  witness_vertex_node nodes source source_node ->
  witness_vertex_node nodes target target_node ->
  forall value,
    DirectedClosedPeriod source_node value ->
    DirectedClosedPeriod target_node value.
Proof.
  intros d system nodes root source target source_node target_node
    Hhom Hbottom Hpath.
  revert source_node target_node Hbottom.
  induction Hpath as [|middle target Hprefix IH Hedge];
    intros source_node target_node Hbottom Hsource_node Htarget_node value Hvalue.
  - pose proof (witness_vertex_node_unique d system nodes source
      source_node target_node Hsource_node Htarget_node). subst target_node.
    exact Hvalue.
  - destruct Hedge as [middle_node [edge_target
      [Hmiddle_node [Hedge_target Hedge_nodes]]]].
    pose proof (witness_vertex_node_unique d system nodes target
      edge_target target_node Hedge_target Htarget_node) as ->.
    assert (Hmiddle_bottom : BottomSCC (WitnessEdge nodes) root middle).
    { eapply bottom_scc_graph_reach_closed; eauto. }
    assert (Hprefix_value : DirectedClosedPeriod middle_node value).
    { eapply IH; eauto. }
    eapply lemma_3_13_directed_closed_period_inclusion; [exact Hedge_nodes| |].
    intros point Hpoint.
    assert (Hscc : SameSCC (WitnessEdge nodes) middle target).
    { assert (Htarget_bottom : BottomSCC (WitnessEdge nodes) root target).
      { eapply bottom_scc_closed; [exact Hmiddle_bottom|].
        exists middle_node, target_node. repeat split; assumption. }
      destruct Hmiddle_bottom as [[Hrm Hmr] Hroot].
      destruct Htarget_bottom as [[Hrt Htr] _]. split.
      * eapply graph_reach_trans; [exact Hmr|exact Hrt].
      * eapply graph_reach_trans; [exact Htr|exact Hrm]. }
    pose proof (Hhom middle target middle_node target_node Hscc
      Hmiddle_node Htarget_node) as Hcones.
    now apply (proj1 (Hcones point)).
    + exact Hprefix_value.
Qed.

Theorem bottom_scc_common_closed_period : forall d
    (system : IBVAS d) (nodes : list (DirectedIRun system)) root
    representative representative_node member member_node,
  HomogeneousWitnessNodes nodes ->
  BottomSCCRoot (WitnessEdge nodes) root ->
  BottomSCC (WitnessEdge nodes) root representative ->
  BottomSCC (WitnessEdge nodes) root member ->
  witness_vertex_node nodes representative representative_node ->
  witness_vertex_node nodes member member_node ->
  forall value,
    DirectedClosedPeriod representative_node value <->
    DirectedClosedPeriod member_node value.
Proof.
  intros d system nodes root representative representative_node member
    member_node Hhom Hroot Hrepresentative Hmember Hrep_node Hmember_node value.
  destruct Hrepresentative as [[Hrr Hrepr] _].
  destruct Hmember as [[Hrm Hmr] _]. split.
  - eapply (witness_graph_reach_closed_period_inclusion d system nodes root
      representative member representative_node member_node).
    + exact Hhom.
    + split; [split; [exact Hrr|exact Hrepr]|exact Hroot].
    + eapply graph_reach_trans; [exact Hrepr|exact Hrm].
    + exact Hrep_node.
    + exact Hmember_node.
  - eapply (witness_graph_reach_closed_period_inclusion d system nodes root
      member representative member_node representative_node).
    + exact Hhom.
    + split; [split; [exact Hrm|exact Hmr]|exact Hroot].
    + eapply graph_reach_trans; [exact Hmr|exact Hrr].
    + exact Hmember_node.
    + exact Hrep_node.
Qed.

Theorem bottom_scc_common_cone : forall d
    (system : IBVAS d) (nodes : list (DirectedIRun system)) root
    representative representative_node member member_node,
  HomogeneousWitnessNodes nodes ->
  BottomSCC (WitnessEdge nodes) root representative ->
  BottomSCC (WitnessEdge nodes) root member ->
  witness_vertex_node nodes representative representative_node ->
  witness_vertex_node nodes member member_node ->
  forall point,
    DirectedCone representative_node point <->
    DirectedCone member_node point.
Proof.
  intros d system nodes root representative representative_node member
    member_node Hhom [[Hrr Hrepr] Hbottom]
    [[Hrm Hmr] _] Hrep_node Hmember_node point.
  apply Hhom with (left := representative) (right := member);
    try assumption.
  split.
  - eapply graph_reach_trans; [exact Hrepr|exact Hrm].
  - eapply graph_reach_trans; [exact Hmr|exact Hrr].
Qed.

Lemma nclosed_directed_period_periodic : forall d
    (system : IBVAS d) (node : DirectedIRun system),
  PeriodicNSet (NClosedDirectedPeriod node).
Proof.
  intros d system node. unfold NClosedDirectedPeriod.
  apply closed_linearization_n_periodic, directed_offset_periodic.
Qed.

Lemma directed_offset_in_common_closed_period : forall d
    (system : IBVAS d) (nodes : list (DirectedIRun system)) root
    representative representative_node member member_node offset,
  HomogeneousWitnessNodes nodes ->
  BottomSCCRoot (WitnessEdge nodes) root ->
  BottomSCC (WitnessEdge nodes) root representative ->
  BottomSCC (WitnessEdge nodes) root member ->
  witness_vertex_node nodes representative representative_node ->
  witness_vertex_node nodes member member_node ->
  DirectedOffset member_node offset ->
  NClosedDirectedPeriod representative_node offset.
Proof.
  intros d system nodes root representative representative_node member
    member_node offset Hhom Hroot Hrep Hmember Hrep_node Hmember_node Hoffset.
  apply (proj2 (bottom_scc_common_closed_period d system nodes root
    representative representative_node member member_node Hhom Hroot
    Hrep Hmember Hrep_node Hmember_node (nvec_to_zvec offset))).
  now apply directed_offset_in_closed_period_n.
Qed.

Lemma bottom_scc_period_semilinear : forall d (system : IBVAS d)
    (representative : DirectedIRun system),
  Semilinear (BottomSCCPeriod representative).
Proof.
  intros d system representative. unfold BottomSCCPeriod.
  apply generated_nonnegative_semilinear.
  - apply lemma_3_12_directed_closed_period_finitely_generated.
  - apply closed_linearization_nonnegative.
    apply directed_period_nonnegative.
Qed.

Lemma bottom_scc_region_semilinear : forall d (system : IBVAS d)
    (nodes : list (DirectedIRun system)) root representative,
  Semilinear (BottomSCCRegion nodes root representative).
Proof.
  intros d system nodes root representative.
  destruct (bottom_scc_region_finitary d system nodes root representative)
    as [bases Hbases].
  pose proof (finite_translate_union_semilinear d bases
    (BottomSCCPeriod representative)
    (bottom_scc_period_semilinear d system representative)) as Hfinite.
  destruct Hfinite as [code Hcode]. exists code. intro value.
  rewrite Hbases. apply Hcode.
Qed.

Lemma bottom_scc_region_stable : forall d (system : IBVAS d)
    (nodes : list (DirectedIRun system)) root representative,
  NSetStable (BottomSCCRegion nodes root representative)
    (BottomSCCPeriod representative).
Proof.
  intros d system nodes root representative value increment
    [base [Hbase [offset [Hoffset Hvalue]]]] Hincrement.
  exists base. split; [exact Hbase|].
  exists (nvec_add offset increment). split.
  - unfold BottomSCCPeriod in *.
    pose proof (closed_linearization_periodic d
      (DirectedPeriod representative)
      (directed_period_periodic d system representative)) as Hperiodic.
    rewrite nvec_to_zvec_add. now apply (proj2 Hperiodic).
  - subst value. rewrite nvec_add_assoc. reflexivity.
Qed.

Lemma bottom_scc_member_targets_region : forall d
    (system : IBVAS d) (nodes : list (DirectedIRun system)) root
    representative representative_node member member_node run,
  HomogeneousWitnessNodes nodes ->
  BottomSCCRoot (WitnessEdge nodes) root ->
  BottomSCC (WitnessEdge nodes) root representative ->
  BottomSCC (WitnessEdge nodes) root member ->
  witness_vertex_node nodes representative representative_node ->
  witness_vertex_node nodes member member_node ->
  DirectedRunMember member_node run ->
  BottomSCCRegion nodes root representative_node (irun_target run).
Proof.
  intros d system nodes root representative representative_node member
    member_node run Hhom Hroot Hrep Hmember Hrep_node Hmember_node Hrun.
  destruct Hrun as [Hvalid [offset [Hle [Htarget Hcone]]]].
  exists (irun_target (directed_root member_node)). split.
  - exists member, member_node. split; [exact Hmember|].
    split; [exact Hmember_node|reflexivity].
  - exists offset. split.
    + unfold BottomSCCPeriod.
      apply (directed_offset_in_common_closed_period d system nodes root
        representative representative_node member member_node offset
        Hhom Hroot Hrep Hmember Hrep_node Hmember_node).
      split.
      * exists run. split; [exact Hvalid|]. split; assumption.
      * exact Hcone.
    + exact Htarget.
Qed.

Definition DirectedTargetSet {d} {system : IBVAS d}
    (node : DirectedIRun system) : NVec d -> Prop :=
  fun value => exists run,
    DirectedRunMember node run /\ irun_target run = value.

Definition BottomSCCInvariant {d} (system : IBVAS d)
    (attractor : NVec d -> Prop) : NVec d -> Prop :=
  fun value => attractor value \/ Reach system value.

Definition BottomSCCTarget {d} {system : IBVAS d}
    (safe attractor : NVec d -> Prop)
    (nodes : list (DirectedIRun system)) (root : WitnessVertex nodes)
    (representative : DirectedIRun system) : NVec d -> Prop :=
  fun value => attractor value \/
    (BottomSCCRegion nodes root representative value /\ safe value).

Lemma semilinear_binary_union : forall d (left right : NSet d),
  Semilinear left -> Semilinear right ->
  Semilinear (fun value => left value \/ right value).
Proof.
  intros d left right Hleft Hright.
  pose proof (semilinear_finite_union d [left; right]
    ltac:(repeat constructor; assumption)) as Hunion.
  destruct Hunion as [code Hcode]. exists code. intro value.
  rewrite <- Hcode. split.
  - intros [Hleft_value|Hright_value].
    + exists left. split; [now left|exact Hleft_value].
    + exists right. split; [right; now left|exact Hright_value].
  - intros [set [[Heq|[Heq|Hfalse]] Hvalue]].
    + subst set. now left.
    + subst set. now right.
    + contradiction.
Qed.

Lemma bottom_scc_invariant_inductive : forall d (system : IBVAS d)
    attractor,
  Attractor system attractor ->
  IBVASInductiveInvariant system (BottomSCCInvariant system attractor).
Proof. intros; now apply attractor_union_reach_inductive. Qed.

Lemma bottom_scc_target_semilinear : forall d (system : IBVAS d) safe
    (witness : SafetyWitness system safe) root representative,
  Semilinear (BottomSCCTarget safe (witness_attractor witness)
    (witness_nodes witness) root representative).
Proof.
  intros d system safe witness root representative.
  unfold BottomSCCTarget.
  apply semilinear_binary_union.
  - apply witness_attractor_semilinear.
  - apply semilinear_intersection.
    + apply bottom_scc_region_semilinear.
    + exact (witness_safe_semilinear system safe witness).
Qed.

Lemma directed_target_set_reachable : forall d (system : IBVAS d)
    (node : DirectedIRun system) value,
  DirectedTargetSet node value -> Reach system value.
Proof.
  intros d system node value [run [Hrun <-]].
  now apply valid_irun_reach, Hrun.
Qed.

Theorem bottom_scc_representative_shuffle_safe : forall d
    (system : IBVAS d) safe (witness : SafetyWitness system safe)
    root representative representative_node,
  BottomSCCRoot (WitnessEdge (witness_nodes witness)) root ->
  BottomSCC (WitnessEdge (witness_nodes witness)) root representative ->
  witness_vertex_node (witness_nodes witness) representative
    representative_node ->
  forall output,
    ReachFromShuffle system (DirectedTargetSet representative_node)
      (BottomSCCInvariant system (witness_attractor witness)) output ->
    BottomSCCTarget safe (witness_attractor witness)
      (witness_nodes witness) root representative_node output.
Proof.
  intros d system safe witness root representative representative_node
    Hroot Hrepresentative Hrepresentative_node output Hreach.
  destruct (reach_from_shuffle_attractor_or_special d system
    (witness_attractor witness) (DirectedTargetSet representative_node)
    output (witness_attractor_closed system safe witness)
    (directed_target_set_reachable d system representative_node) Hreach)
    as [Hattractor|[input [[source_run [Hsource_member Hsource_target]]
      Hspecial]]].
  - now left.
  - subst input.
    destruct (lemma_7_2_safety_witness_successors d system safe witness
      representative_node source_run output) as [Hattractor|Hsuccessor].
    + now apply nth_error_In with
        (n := proj1_sig (Fin.to_nat representative)).
    + exact Hsource_member.
    + exact Hspecial.
    + now left.
    + destruct Hsuccessor as [target [[Htarget_in Hedge]
        [target_run [Htarget_member [Htarget_value Hocc]]]]].
      right. split.
      * apply In_nth_error in Htarget_in.
        destruct Htarget_in as [target_index Htarget_index].
        assert (Htarget_bound : (target_index < length (witness_nodes witness))%nat).
        { apply nth_error_Some. rewrite Htarget_index. discriminate. }
        set (target_vertex := Fin.of_nat_lt Htarget_bound).
        assert (Htarget_node : witness_vertex_node (witness_nodes witness)
            target_vertex target).
        { unfold witness_vertex_node, target_vertex. now rewrite Fin.to_nat_of_nat. }
        assert (Hedge_vertex : WitnessEdge (witness_nodes witness)
            representative target_vertex).
        { exists representative_node, target. repeat split; assumption. }
        assert (Htarget_bottom : BottomSCC
            (WitnessEdge (witness_nodes witness)) root target_vertex).
        { eapply bottom_scc_closed; eauto. }
        rewrite <- Htarget_value.
        exact (bottom_scc_member_targets_region d system
          (witness_nodes witness) root representative representative_node
          target_vertex target target_run
          (witness_nodes_homogeneous system safe witness) Hroot
          Hrepresentative Htarget_bottom Hrepresentative_node Htarget_node
          Htarget_member).
      * rewrite <- Htarget_value.
        apply (witness_reach_safe system safe witness), valid_irun_reach,
          Htarget_member.
Qed.

Lemma reach_from_shuffle_source_extensional : forall d
    (system : IBVAS d) (left right invariant : NVec d -> Prop) output,
  (forall value, left value <-> right value) ->
  ReachFromShuffle system left invariant output ->
  ReachFromShuffle system right invariant output.
Proof.
  intros d system left right invariant output Heq
    [run [Hvalid [Htarget
      [prefix [special [suffix [Hword [Hleft [Hprefix Hsuffix]]]]]]]]].
  exists run. split; [exact Hvalid|]. split; [exact Htarget|].
  exists prefix, special, suffix. repeat split; auto.
  now apply (proj1 (Heq special)).
Qed.

Lemma directed_target_set_translate : forall d (system : IBVAS d)
    (node : DirectedIRun system) value,
  DirectedTargetSet node value <->
  NSetTranslate (irun_target (directed_root node))
    (DirectedOffset node) value.
Proof.
  intros d system node value. unfold DirectedTargetSet, NSetTranslate.
  rewrite directed_run_targets. split.
  - intros [offset [Hoffset Hvalue]]. exists offset. auto.
  - intros [offset [Hoffset Hvalue]]. exists offset. auto.
Qed.

Lemma bottom_scc_target_bound : forall d (system : IBVAS d) safe
    (witness : SafetyWitness system safe) root representative,
  forall value,
    BottomSCCTarget safe (witness_attractor witness)
      (witness_nodes witness) root representative value ->
    NSetMinkowskiN
      (BottomSCCInvariant system (witness_attractor witness))
      (BottomSCCPeriod representative) value.
Proof.
  intros d system safe witness root representative value [HA|[HY Hsafe]].
  - exists value, (nvec_zero d). split; [now left|]. split.
    + unfold BottomSCCPeriod.
      pose proof (closed_linearization_periodic d
        (DirectedPeriod representative)
        (directed_period_periodic d system representative)) as Hperiodic.
      rewrite nvec_zero_to_zvec. exact (proj1 Hperiodic).
    + symmetry. apply nvec_add_zero_right.
  - destruct HY as [base [Hbase [offset [Hoffset Hvalue]]]].
    exists base, offset. split.
    + right. destruct Hbase as [vertex [node [Hbottom [Hnode Hbase]]]].
      subst base. apply valid_irun_reach, directed_root_valid.
    + split; [exact Hoffset|exact Hvalue].
Qed.

Lemma directed_offset_asymptotically_definable : forall d
    (system : IBVAS d) (node : DirectedIRun system),
  AsymptoticallyDefinableNSet (DirectedOffset node).
Proof.
  intros d system node. split.
  - apply directed_offset_periodic.
  - change (QDefinable (Cone (DirectedPeriod node))).
    exact (directed_period_asymptotically_definable d system node).
Qed.

Theorem bottom_scc_safe_linearization : forall d
    (system : IBVAS d) safe (witness : SafetyWitness system safe)
    root representative representative_node,
  BottomSCCRoot (WitnessEdge (witness_nodes witness)) root ->
  BottomSCC (WitnessEdge (witness_nodes witness)) root representative ->
  witness_vertex_node (witness_nodes witness) representative
    representative_node ->
  exists offset,
    DirectedOffset representative_node offset /\
    forall output,
      ReachFromNonemptyShuffle system
        (NSetTranslate
          (nvec_add (irun_target (directed_root representative_node)) offset)
          (BottomSCCPeriod representative_node))
        (BottomSCCInvariant system (witness_attractor witness)) output ->
      BottomSCCTarget safe (witness_attractor witness)
        (witness_nodes witness) root representative_node output.
Proof.
  intros d system safe witness root representative representative_node
    Hroot Hrepresentative Hrepresentative_node.
  apply (lemma_5_1_bvas_safe_linearization d system
    (witness_attractor witness)
    (BottomSCCTarget safe (witness_attractor witness)
      (witness_nodes witness) root representative_node)
    (DirectedOffset representative_node)
    (irun_target (directed_root representative_node))).
  - apply bottom_scc_invariant_inductive.
    exact (witness_attractor_closed system safe witness).
  - exact (witness_attractor_semilinear system safe witness).
  - apply bottom_scc_target_semilinear.
  - apply directed_offset_periodic.
  - apply directed_offset_asymptotically_definable.
  - intros output Hreach.
    apply bottom_scc_representative_shuffle_safe with
      (root := root) (representative := representative);
      try assumption.
    apply reach_from_shuffle_source_extensional with
      (left := NSetTranslate (irun_target (directed_root representative_node))
        (DirectedOffset representative_node)).
    + intro value. symmetry. apply directed_target_set_translate.
    + exact Hreach.
  - apply bottom_scc_target_bound.
Qed.

(** A nonempty-shuffle reachability set inherits every period that can be
    pushed into one distinguished source occurrence.  The other occurrences
    remain tagged as either source or invariant leaves; no membership in the
    invariant is inferred for them. *)
Lemma reach_from_nonempty_shuffle_stable : forall d (system : IBVAS d)
    (source invariant period : NSet d),
  NSetStable source period ->
  NSetStable
    (ReachFromNonemptyShuffle system source invariant) period.
Proof.
  intros d system source invariant period Hstable output offset
    [run [Hvalid [Htarget Hmulti]]] Hoffset.
  destruct (source_multi_shuffle_characterization d source invariant
    (free_irun_sources run) Hmulti) as [Hall Hhas].
  assert (Hshuffle : SourceShuffle source
      (fun value => source value \/ invariant value)
      (free_irun_sources run)).
  { now apply has_source_forall_source_shuffle. }
  pose proof (valid_free_source_shuffle_marked system source
    (fun value => source value \/ invariant value) run Hvalid Hshuffle)
    as Hmarked.
  destruct (marked_free_shift system source
    (fun value => source value \/ invariant value) period Hstable
    run offset Hmarked Hoffset) as [shifted [Hshifted Hshifted_target]].
  exists shifted. split.
  - now apply marked_free_valid with
      (X := source) (I := fun value => source value \/ invariant value).
  - split.
    + now rewrite Hshifted_target, Htarget.
    + destruct (marked_free_source_shuffle system source
        (fun value => source value \/ invariant value) shifted Hshifted)
        as [prefix [special [suffix
          [Hword [Hspecial [Hprefix Hsuffix]]]]]].
      apply source_multi_shuffle_partition.
      * rewrite Hword. apply List.Forall_app. split; [exact Hprefix|].
        constructor; [now left|exact Hsuffix].
      * exists special. split; [|exact Hspecial]. rewrite Hword.
        apply in_or_app. right. now left.
Qed.

Lemma translated_period_stable : forall d (base : NVec d)
    (period : NSet d),
  PeriodicNSet period -> NSetStable (NSetTranslate base period) period.
Proof.
  intros d base period Hperiodic value offset
    [first [Hfirst Hvalue]] Hoffset.
  exists (nvec_add first offset). split.
  - now apply (proj2 Hperiodic).
  - rewrite Hvalue, nvec_add_assoc. reflexivity.
Qed.

Definition BottomSCCLinearReach {d} {system : IBVAS d}
    (attractor : NSet d) (representative : DirectedIRun system)
    (offset : NVec d) : NSet d :=
  ReachFromNonemptyShuffle system
    (NSetTranslate
      (nvec_add (irun_target (directed_root representative)) offset)
      (BottomSCCPeriod representative))
    (BottomSCCInvariant system attractor).

Lemma bottom_scc_linear_reach_stable : forall d (system : IBVAS d)
    attractor representative offset,
  NSetStable (BottomSCCLinearReach attractor representative offset)
    (BottomSCCPeriod (d := d) (system := system) representative).
Proof.
  intros. apply reach_from_nonempty_shuffle_stable.
  apply translated_period_stable.
  apply bottom_scc_period_periodic.
Qed.

Lemma empty_attractor : forall d (system : IBVAS d),
  Attractor system (fun _ : NVec d => False).
Proof.
  intros d system output [run [_ [_ Hmulti]]].
  destruct (source_multi_shuffle_characterization d
    (fun _ : NVec d => False) (Reach system)
    (free_irun_sources run) Hmulti) as [_ [value [_ Hfalse]]].
  contradiction.
Qed.

Lemma bottom_scc_linear_reach_attractor : forall d (system : IBVAS d)
    attractor (representative : DirectedIRun system) offset,
  IBVASInductiveInvariant system (BottomSCCInvariant system attractor) ->
  Attractor system (BottomSCCLinearReach attractor representative offset).
Proof.
  intros d system attractor representative offset Hinvariant.
  pose proof (lemma_3_7_attractor_extension d system
    (fun _ : NVec d => False)
    (BottomSCCInvariant system attractor)
    (NSetTranslate
      (nvec_add (irun_target (directed_root representative)) offset)
      (BottomSCCPeriod representative))
    (empty_attractor d system) Hinvariant
    (fun value Hfalse => False_rect _ Hfalse)) as Hextension.
  intros output [run [Hrun [Htarget
    [specials [initials [Hnonempty [Hspecials [Hinitials Hperm]]]]]]]].
  assert (Hunion : False \/ BottomSCCLinearReach attractor representative
      offset output).
  { apply Hextension. exists run. split; [exact Hrun|].
    split; [exact Htarget|]. exists specials, initials.
    repeat split; try assumption.
    eapply List.Forall_impl; [|exact Hspecials].
    intros value Hvalue. now right. }
  destruct Hunion as [Hfalse|Hreach]; [contradiction|exact Hreach].
Qed.

Lemma bottom_scc_contact_along_path : forall d (system : IBVAS d)
    (nodes : list (DirectedIRun system)) root representative
    representative_node member member_node (set : NSet d),
  HomogeneousWitnessNodes nodes ->
  BottomSCCRoot (WitnessEdge nodes) root ->
  BottomSCC (WitnessEdge nodes) root representative ->
  GraphReach (WitnessEdge nodes) representative member ->
  witness_vertex_node nodes representative representative_node ->
  witness_vertex_node nodes member member_node ->
  Attractor system set ->
  NSetStable set (BottomSCCPeriod representative_node) ->
  (exists value, set value /\
    DirectedRootTranslate representative_node
      (BottomSCCPeriod representative_node) value) ->
  exists value, set value /\
    DirectedRootTranslate member_node
      (BottomSCCPeriod representative_node) value.
Proof.
  intros d system nodes root representative representative_node member
    member_node set Hhom Hroot Hrepresentative Hpath.
  revert representative_node member_node Hrepresentative.
  induction Hpath as [|middle target Hpath IH Hedge];
    intros representative_node member_node Hrepresentative
      Hrepresentative_node Hmember_node Hattr Hstable Hcontact.
  - pose proof (witness_vertex_node_unique d system nodes representative
      representative_node member_node Hrepresentative_node Hmember_node).
    subst member_node. exact Hcontact.
  - destruct Hedge as [middle_node [target_node
      [Hmiddle_node [Htarget_node Hedge_nodes]]]].
    pose proof (witness_vertex_node_unique d system nodes target
      target_node member_node Htarget_node Hmember_node) as ->.
    assert (Hmiddle_bottom : BottomSCC (WitnessEdge nodes) root middle).
    { eapply bottom_scc_graph_reach_closed; eauto. }
    assert (Htarget_bottom : BottomSCC (WitnessEdge nodes) root target).
    { eapply bottom_scc_closed; [exact Hmiddle_bottom|].
      exists middle_node, member_node. repeat split; assumption. }
    assert (Hmiddle_contact : exists value, set value /\
        DirectedRootTranslate middle_node
          (BottomSCCPeriod representative_node) value).
    { eapply IH; eauto. }
    eapply lemma_7_3_attractor_contact_propagation.
    + exact Hattr.
    + apply bottom_scc_period_periodic.
    + exact Hstable.
    + exact Hedge_nodes.
    + intro offset. unfold BottomSCCPeriod, NClosedDirectedPeriod.
      exact (iff_sym (bottom_scc_common_closed_period d system nodes root
        representative representative_node middle middle_node Hhom Hroot
        Hrepresentative Hmiddle_bottom Hrepresentative_node Hmiddle_node
        (nvec_to_zvec offset))).
    + intro offset. unfold BottomSCCPeriod, NClosedDirectedPeriod.
      exact (iff_sym (bottom_scc_common_closed_period d system nodes root
        representative representative_node target member_node Hhom Hroot
        Hrepresentative Htarget_bottom Hrepresentative_node Hmember_node
        (nvec_to_zvec offset))).
    + exact Hmiddle_contact.
Qed.

Theorem bottom_scc_contact_all : forall d (system : IBVAS d)
    (nodes : list (DirectedIRun system)) root representative
    representative_node (set : NSet d),
  HomogeneousWitnessNodes nodes ->
  BottomSCCRoot (WitnessEdge nodes) root ->
  BottomSCC (WitnessEdge nodes) root representative ->
  witness_vertex_node nodes representative representative_node ->
  Attractor system set ->
  NSetStable set (BottomSCCPeriod representative_node) ->
  (exists value, set value /\
    DirectedRootTranslate representative_node
      (BottomSCCPeriod representative_node) value) ->
  forall member member_node,
    BottomSCC (WitnessEdge nodes) root member ->
    witness_vertex_node nodes member member_node ->
    exists value, set value /\
      DirectedRootTranslate member_node
        (BottomSCCPeriod representative_node) value.
Proof.
  intros d system nodes root representative representative_node set Hhom
    Hroot Hrepresentative Hrepresentative_node Hattr Hstable Hcontact
    member member_node Hmember Hmember_node.
  destruct Hrepresentative as [[Hrr Hrep_to_root] Hroot_copy].
  destruct Hmember as [[Hroot_to_member Hmember_to_root] _].
  eapply bottom_scc_contact_along_path.
  - exact Hhom.
  - exact Hroot.
  - split.
    + split; [exact Hrr|exact Hrep_to_root].
    + exact Hroot_copy.
  - eapply graph_reach_trans; [exact Hrep_to_root|exact Hroot_to_member].
  - exact Hrepresentative_node.
  - exact Hmember_node.
  - exact Hattr.
  - exact Hstable.
  - exact Hcontact.
Qed.

Theorem bottom_scc_region_backward_cover : forall d (system : IBVAS d)
    (nodes : list (DirectedIRun system)) root representative
    representative_node (set : NSet d),
  HomogeneousWitnessNodes nodes ->
  BottomSCCRoot (WitnessEdge nodes) root ->
  BottomSCC (WitnessEdge nodes) root representative ->
  witness_vertex_node nodes representative representative_node ->
  Attractor system set ->
  NSetStable set (BottomSCCPeriod representative_node) ->
  (exists value, set value /\
    DirectedRootTranslate representative_node
      (BottomSCCPeriod representative_node) value) ->
  forall value,
    BottomSCCRegion nodes root representative_node value ->
    exists increment,
      BottomSCCPeriod representative_node increment /\
      set (nvec_add value increment) /\
      BottomSCCRegion nodes root representative_node
        (nvec_add value increment).
Proof.
  intros d system nodes root representative representative_node set Hhom
    Hroot Hrepresentative Hrepresentative_node Hattr Hstable Hcontact value
    [base [[member [member_node [Hmember [Hmember_node Hbase]]]]
      [value_offset [Hvalue_offset Hvalue]]]].
  subst base value.
  destruct (bottom_scc_contact_all d system nodes root representative
    representative_node set Hhom Hroot Hrepresentative
    Hrepresentative_node Hattr Hstable Hcontact member member_node Hmember
    Hmember_node) as [contact [Hcontact_set
      [contact_offset [Hcontact_offset Hcontact_value]]]].
  exists contact_offset. split; [exact Hcontact_offset|]. split.
  - replace
      (nvec_add
        (nvec_add (irun_target (directed_root member_node)) value_offset)
        contact_offset)
      with (nvec_add contact value_offset).
    + apply Hstable; assumption.
    + rewrite Hcontact_value.
      apply (proj1 (StdVector.eq_nth_iff nat d _ _)).
      intros index other Heq. subst other. unfold nvec_add.
      repeat rewrite (StdVector.nth_map2 Nat.add _ _ index index index
        eq_refl eq_refl). lia.
  - exists (irun_target (directed_root member_node)). split.
    + exists member, member_node. split; [exact Hmember|].
      split; [exact Hmember_node|reflexivity].
    + exists (nvec_add value_offset contact_offset). split.
      * apply (proj2 (bottom_scc_period_periodic d system representative_node));
          assumption.
      * rewrite nvec_add_assoc. reflexivity.
Qed.

Lemma nset_as_z_reflect : forall d (set : NSet d) value,
  NSetAsZ set (nvec_to_zvec value) <-> set value.
Proof.
  intros d set value. split.
  - intros [natural [Heq Hset]].
    apply nvec_to_zvec_injective_update in Heq. now subst natural.
  - intro Hset. exists value. auto.
Qed.

Lemma nset_stable_as_z_cylindric : forall d
    (set periodN : NSet d) (periodZ : ZSet d),
  (forall value, periodN value <-> periodZ (nvec_to_zvec value)) ->
  NonnegativeSet periodZ ->
  NSetStable set periodN ->
  QCylindric periodZ (NSetAsZ set).
Proof.
  intros d set periodN periodZ Hperiod Hnonnegative Hstable
    base increment [nbase [-> Hbase]] Hincrement.
  set (nincrement := nonnegative_zvec_to_nvec increment).
  assert (Hroundtrip : nvec_to_zvec nincrement = increment).
  { apply nonnegative_zvec_roundtrip. now apply Hnonnegative. }
  exists (nvec_add nbase nincrement). split.
  - rewrite nvec_to_zvec_add, Hroundtrip. reflexivity.
  - apply Hstable; [exact Hbase|].
    apply Hperiod. now rewrite Hroundtrip.
Qed.

Lemma bottom_scc_region_z_finitary : forall d (system : IBVAS d)
    (nodes : list (DirectedIRun system)) root representative,
  FinitaryQCylindric (DirectedClosedPeriod representative)
    (NSetAsZ (BottomSCCRegion nodes root representative)).
Proof.
  intros d system nodes root representative.
  destruct (bottom_scc_region_finitary d system nodes root representative)
    as [bases Hbases].
  exists (List.map nvec_to_zvec bases). intro integer. split.
  - intros [natural [Hinteger Hregion]]. subst integer.
    apply Hbases in Hregion.
    destruct Hregion as [base [Hbase [offset [Hoffset Hvalue]]]].
    exists (nvec_to_zvec base), (nvec_to_zvec offset). split.
    + now apply in_map.
    + split; [exact Hoffset|]. subst natural. now rewrite nvec_to_zvec_add.
  - intros [base [increment [Hbase [Hincrement Hinteger]]]].
    apply in_map_iff in Hbase.
    destruct Hbase as [nbase [Hbase Hnbase]]. subst base.
    set (nincrement := nonnegative_zvec_to_nvec increment).
    assert (Hroundtrip : nvec_to_zvec nincrement = increment).
    { apply nonnegative_zvec_roundtrip.
      exact (closed_linearization_nonnegative d (DirectedPeriod representative)
        (directed_period_nonnegative d system representative)
        increment Hincrement). }
    exists (nvec_add nbase nincrement). split.
    + rewrite nvec_to_zvec_add, Hroundtrip. exact Hinteger.
    + apply Hbases. exists nbase. split; [exact Hnbase|].
      exists nincrement. split.
      * unfold BottomSCCPeriod. now rewrite Hroundtrip.
      * reflexivity.
Qed.

Lemma finitary_nonnegative_semilinear : forall d
    (period set : ZSet d),
  FinitelyGeneratedPeriodic period ->
  NonnegativeSet period ->
  NonnegativeSet set ->
  FinitaryQCylindric period set ->
  Semilinear (fun value : NVec d => set (nvec_to_zvec value)).
Proof.
  intros d period set Hfinite Hperiod_nonnegative Hset_nonnegative
    [bases Hbases].
  assert (Hbases_nonnegative : List.Forall
      (fun base => forall index, (0 <= StdVector.nth base index)%Z) bases).
  { apply List.Forall_forall. intros base Hbase index.
    apply Hset_nonnegative. apply (proj2 (Hbases base)).
    exists base, (zvec_zero d). split; [exact Hbase|]. split.
    - exact (proj1 (finitely_generated_periodic_is_periodic d period Hfinite)).
    - now rewrite zvec_add_zero_right. }
  set (nbases := List.map nonnegative_zvec_to_nvec bases).
  set (nperiod := fun value : NVec d => period (nvec_to_zvec value)).
  assert (Hperiod_semilinear : Semilinear nperiod).
  { apply generated_nonnegative_semilinear; assumption. }
  pose proof (finite_translate_union_semilinear d nbases nperiod
    Hperiod_semilinear) as Hunion.
  destruct Hunion as [code Hcode]. exists code. intro value.
  rewrite <- Hcode. unfold nbases, nperiod. split.
  - intro Hset.
    apply (proj1 (Hbases (nvec_to_zvec value))) in Hset.
    destruct Hset as [base [increment [Hbase [Hincrement Heq]]]].
    assert (Hbase_nonnegative : forall index,
        (0 <= StdVector.nth base index)%Z).
    { apply List.Forall_forall with (x := base) in Hbases_nonnegative;
        assumption. }
    assert (Hincrement_nonnegative : forall index,
        (0 <= StdVector.nth increment index)%Z)
      by now apply Hperiod_nonnegative.
    exists (nonnegative_zvec_to_nvec base). split.
    + now apply in_map.
    + exists (nonnegative_zvec_to_nvec increment). split.
      * rewrite nonnegative_zvec_roundtrip by exact Hincrement_nonnegative.
        exact Hincrement.
      * apply nvec_to_zvec_injective_update.
        rewrite nvec_to_zvec_add.
        rewrite !nonnegative_zvec_roundtrip by assumption.
        exact Heq.
  - intros [base [Hbase [increment [Hincrement Heq]]]].
    apply in_map_iff in Hbase.
    destruct Hbase as [zbase [Hbase Hzbase]]. subst base value.
    apply (proj2 (Hbases
      (nvec_to_zvec (nvec_add (nonnegative_zvec_to_nvec zbase) increment)))).
    exists zbase, (nvec_to_zvec increment). split; [exact Hzbase|]. split.
    + exact Hincrement.
    + apply List.Forall_forall with (x := zbase) in Hbases_nonnegative;
        [|exact Hzbase].
      rewrite nvec_to_zvec_add,
        nonnegative_zvec_roundtrip by exact Hbases_nonnegative.
      reflexivity.
Qed.

Definition BottomSCCLinearSlice {d} {system : IBVAS d}
    (nodes : list (DirectedIRun system)) root representative
    (attractor : NSet d) (offset : NVec d) : NSet d :=
  fun value => BottomSCCLinearReach attractor representative offset value /\
    BottomSCCRegion nodes root representative value.

Lemma bottom_scc_linear_slice_stable : forall d (system : IBVAS d)
    (nodes : list (DirectedIRun system)) root
    (representative : DirectedIRun system) attractor offset,
  NSetStable
    (BottomSCCLinearSlice nodes root representative attractor offset)
    (BottomSCCPeriod representative).
Proof.
  intros d system nodes root representative attractor offset value increment
    [HR HY] HQ. split.
  - now apply bottom_scc_linear_reach_stable.
  - now apply bottom_scc_region_stable.
Qed.

Lemma bottom_scc_linear_slice_finitary_z : forall d
    (system : IBVAS d) (nodes : list (DirectedIRun system)) root
    (representative : DirectedIRun system) attractor offset,
  FinitaryQCylindric (DirectedClosedPeriod representative)
    (NSetAsZ
      (BottomSCCLinearSlice nodes root representative attractor offset)).
Proof.
  intros d system nodes root representative attractor offset.
  apply finitary_qcylindric_sub with
    (B := NSetAsZ (BottomSCCRegion nodes root representative)).
  - apply closed_linearization_periodic, directed_period_periodic.
  - apply lemma_3_12_directed_closed_period_finitely_generated.
  - apply nset_stable_as_z_cylindric with
      (periodN := BottomSCCPeriod representative).
    + intros value. reflexivity.
    + apply closed_linearization_nonnegative, directed_period_nonnegative.
    + apply bottom_scc_linear_slice_stable.
  - apply bottom_scc_region_z_finitary.
  - intros integer [natural [Hinteger [_ HY]]].
    exists natural. auto.
Qed.

Lemma bottom_scc_linear_slice_semilinear : forall d
    (system : IBVAS d) (nodes : list (DirectedIRun system)) root
    (representative : DirectedIRun system) attractor offset,
  Semilinear
    (BottomSCCLinearSlice nodes root representative attractor offset).
Proof.
  intros d system nodes root representative attractor offset.
  assert (Hsemilinear : Semilinear (fun value : NVec d =>
      NSetAsZ (BottomSCCLinearSlice nodes root representative attractor offset)
        (nvec_to_zvec value))).
  { apply (finitary_nonnegative_semilinear d
      (DirectedClosedPeriod representative)
      (NSetAsZ
        (BottomSCCLinearSlice nodes root representative attractor offset))).
    - apply lemma_3_12_directed_closed_period_finitely_generated.
    - apply closed_linearization_nonnegative, directed_period_nonnegative.
    - intros integer [natural [-> _]] index.
      unfold nvec_to_zvec.
      rewrite (StdVector.nth_map Z.of_nat _ index index eq_refl).
      lia.
    - apply bottom_scc_linear_slice_finitary_z. }
  destruct Hsemilinear as [code Hcode]. exists code. intro value.
  rewrite <- Hcode. symmetry. apply nset_as_z_reflect.
Qed.

Lemma attractor_extensional : forall d (system : IBVAS d)
    (left right : NSet d),
  (forall value, left value <-> right value) ->
  Attractor system left -> Attractor system right.
Proof.
  intros d system left right Heq Hleft output Hreach.
  apply (proj1 (Heq output)). apply Hleft.
  destruct Hreach as [run [Hvalid [Htarget Hmulti]]].
  exists run. split; [exact Hvalid|]. split; [exact Htarget|].
  apply source_multi_shuffle_monotone_update with
    (left := right) (right := Reach system).
  - intros value Hvalue. now apply (proj2 (Heq value)).
  - intros; assumption.
  - exact Hmulti.
Qed.

Lemma bottom_scc_linear_reach_contact : forall d (system : IBVAS d)
    attractor (representative : DirectedIRun system) offset,
  BottomSCCPeriod representative offset ->
  exists value,
    BottomSCCLinearReach attractor representative offset value /\
    DirectedRootTranslate representative
      (BottomSCCPeriod representative) value.
Proof.
  intros d system attractor representative offset Hoffset.
  set (base := nvec_add (irun_target (directed_root representative)) offset).
  exists base. split.
  - exists (irun_leaf base). split; [constructor|]. split; [reflexivity|].
    apply source_multi_shuffle_partition.
    + constructor; [left|constructor]. exists (nvec_zero d). split.
      * unfold BottomSCCPeriod.
        pose proof (closed_linearization_periodic d
          (DirectedPeriod representative)
          (directed_period_periodic d system representative)) as HP.
        rewrite nvec_zero_to_zvec. exact (proj1 HP).
      * symmetry. apply nvec_add_zero_right.
    + exists base. cbn. split; [now left|]. exists (nvec_zero d). split.
      * unfold BottomSCCPeriod.
        pose proof (closed_linearization_periodic d
          (DirectedPeriod representative)
          (directed_period_periodic d system representative)) as HP.
        rewrite nvec_zero_to_zvec. exact (proj1 HP).
      * symmetry. apply nvec_add_zero_right.
  - exists offset. split; [exact Hoffset|reflexivity].
Qed.

Definition BottomSCCExtendedAttractor {d} {system : IBVAS d}
    (nodes : list (DirectedIRun system)) root representative
    (attractor : NSet d) offset : NSet d :=
  fun value => attractor value \/
    BottomSCCLinearSlice nodes root representative attractor offset value.

Theorem bottom_scc_safe_extension : forall d (system : IBVAS d) safe
    (witness : SafetyWitness system safe) root representative
    representative_node,
  BottomSCCRoot (WitnessEdge (witness_nodes witness)) root ->
  BottomSCC (WitnessEdge (witness_nodes witness)) root representative ->
  witness_vertex_node (witness_nodes witness) representative
    representative_node ->
  exists offset,
    DirectedOffset representative_node offset /\
    (forall value,
      BottomSCCLinearReach (witness_attractor witness)
        representative_node offset value ->
      BottomSCCTarget safe (witness_attractor witness)
        (witness_nodes witness) root representative_node value) /\
    Semilinear (BottomSCCExtendedAttractor (witness_nodes witness) root
      representative_node (witness_attractor witness) offset) /\
    Attractor system (BottomSCCExtendedAttractor (witness_nodes witness) root
      representative_node (witness_attractor witness) offset) /\
    (forall value,
      BottomSCCExtendedAttractor (witness_nodes witness) root
        representative_node (witness_attractor witness) offset value ->
      safe value) /\
    FinitaryQCylindric (DirectedClosedPeriod representative_node)
      (NSetAsZ (BottomSCCLinearSlice (witness_nodes witness) root
        representative_node (witness_attractor witness) offset)) /\
    (forall value,
      BottomSCCRegion (witness_nodes witness) root representative_node value ->
      exists increment,
        BottomSCCPeriod representative_node increment /\
        BottomSCCLinearSlice (witness_nodes witness) root representative_node
          (witness_attractor witness) offset (nvec_add value increment)).
Proof.
  intros d system safe witness root representative representative_node
    Hroot Hrepresentative Hrepresentative_node.
  destruct (bottom_scc_safe_linearization d system safe witness root
    representative representative_node Hroot Hrepresentative
    Hrepresentative_node) as [offset [Hoffset Hsafe]].
  exists offset. split; [exact Hoffset|]. split; [exact Hsafe|].
  split.
  - apply semilinear_binary_union.
    + apply witness_attractor_semilinear.
    + apply bottom_scc_linear_slice_semilinear.
  - split.
    + apply attractor_extensional with
        (left := fun value => witness_attractor witness value \/
          BottomSCCLinearReach (witness_attractor witness)
            representative_node offset value).
      * intro value. split.
        -- intros [HA|HR]; [now left|].
           specialize (Hsafe value HR). destruct Hsafe as [HA|[HY _]].
           ++ now left.
           ++ right. now split.
        -- intros [HA|[HR _]]; [now left|now right].
      * apply lemma_3_7_attractor_extension.
        -- apply witness_attractor_closed.
        -- apply bottom_scc_invariant_inductive,
            witness_attractor_closed.
        -- intros value HA. now left.
    + split.
      * intros value [HA|[HR HY]].
        -- exact (@witness_attractor_safe d system safe witness value HA).
        -- specialize (Hsafe value HR). destruct Hsafe as [HA|[_ Hsafe_value]].
           ++ exact (@witness_attractor_safe d system safe witness value HA).
           ++ exact Hsafe_value.
      * split.
        -- apply bottom_scc_linear_slice_finitary_z.
        -- intros value HY.
           assert (Hoffset_period : BottomSCCPeriod representative_node offset).
           { unfold BottomSCCPeriod.
             apply periodic_nset_in_closed_linearization.
             - apply directed_offset_periodic.
             - exact Hoffset. }
           eapply bottom_scc_region_backward_cover; eauto.
           ++ apply witness_nodes_homogeneous.
           ++ apply bottom_scc_linear_reach_attractor.
              apply bottom_scc_invariant_inductive,
                witness_attractor_closed.
           ++ apply bottom_scc_linear_reach_stable.
           ++ apply bottom_scc_linear_reach_contact; exact Hoffset_period.
Qed.

Definition SpecialLeafRelationZ {d} (system : IBVAS d)
    (left right : ZVec d) : Prop :=
  exists nleft nright,
    left = nvec_to_zvec nleft /\ right = nvec_to_zvec nright /\
    SpecialLeafReach system nleft nright.

Lemma special_leaf_relation_z_diagonal : forall d (system : IBVAS d)
    (node : DirectedIRun system),
  QDiagonal (DirectedClosedPeriod node) (SpecialLeafRelationZ system).
Proof.
  intros d system node left right increment
    [nleft [nright [-> [-> Hspecial]]]] Hincrement.
  set (nincrement := nonnegative_zvec_to_nvec increment).
  assert (Hroundtrip : nvec_to_zvec nincrement = increment).
  { apply nonnegative_zvec_roundtrip.
    exact (closed_linearization_nonnegative d (DirectedPeriod node)
      (directed_period_nonnegative d system node) increment Hincrement). }
  exists (nvec_add nleft nincrement), (nvec_add nright nincrement).
  split; [now rewrite nvec_to_zvec_add, Hroundtrip|]. split.
  - now rewrite nvec_to_zvec_add, Hroundtrip.
  - now apply special_leaf_reach_shift.
Qed.

Lemma bottom_scc_linear_slice_no_boundary : forall d
    (system : IBVAS d) (nodes : list (DirectedIRun system)) root
    (representative : DirectedIRun system) attractor offset,
  Attractor system (BottomSCCLinearReach attractor representative offset) ->
  NoBoundaryEdge
    (NSetAsZ (BottomSCCLinearSlice nodes root representative attractor offset))
    (NSetAsZ (BottomSCCRegion nodes root representative))
    (SpecialLeafRelationZ system).
Proof.
  intros d system nodes root representative attractor offset Hattr
    left right [source [target [Hsource [Htarget Hspecial]]]]
    [nleft [Hleft [HRleft HYleft]]]
    [nright [Hright HYright]] Hnot_slice.
  assert (Hsource_natural : source = nleft).
  { apply nvec_to_zvec_injective_update. rewrite <- Hsource, <- Hleft.
    reflexivity. }
  assert (Htarget_natural : target = nright).
  { apply nvec_to_zvec_injective_update. rewrite <- Htarget, <- Hright.
    reflexivity. }
  subst source target.
  apply Hnot_slice. exists nright. split; [exact Hright|]. split.
  - eapply attractor_special_leaf_closed; eauto.
  - exact HYright.
Qed.

Definition BottomSCCStrippingPackage {d} {system : IBVAS d}
    (nodes : list (DirectedIRun system)) (root : WitnessVertex nodes)
    (representative : DirectedIRun system) (attractor : NSet d)
    (offset : NVec d)
    (faces : list (QSet d)) : Prop :=
  OrderedStrippingFaces (DirectedClosedPeriod representative) faces /\
  nth_error faces 0 = Some (Cone (DirectedClosedPeriod representative)) /\
  (forall (stage : nat) face,
    (stage < length faces)%nat -> nth_error faces stage = Some face ->
    FinitaryQCylindric
      (FacePeriod (DirectedClosedPeriod representative) face)
      (StrippingSlice (DirectedClosedPeriod representative)
        (NSetAsZ (BottomSCCLinearSlice nodes root representative attractor offset))
        (NSetAsZ (BottomSCCRegion nodes root representative)) faces stage)) /\
  (forall value,
    (NSetAsZ (BottomSCCRegion nodes root representative) value /\
      ~ NSetAsZ (BottomSCCLinearSlice nodes root representative attractor offset)
        value) <->
    exists stage, (stage < length faces)%nat /\
      StrippingSlice (DirectedClosedPeriod representative)
        (NSetAsZ (BottomSCCLinearSlice nodes root representative attractor offset))
        (NSetAsZ (BottomSCCRegion nodes root representative)) faces stage value) /\
  (forall value,
    ~ StrippingSlice (DirectedClosedPeriod representative)
      (NSetAsZ (BottomSCCLinearSlice nodes root representative attractor offset))
      (NSetAsZ (BottomSCCRegion nodes root representative)) faces 0 value) /\
  (forall (earlier later : nat) left right,
    (earlier < later)%nat -> (later < length faces)%nat ->
    StrippingSlice (DirectedClosedPeriod representative)
      (NSetAsZ (BottomSCCLinearSlice nodes root representative attractor offset))
      (NSetAsZ (BottomSCCRegion nodes root representative)) faces later left ->
    StrippingSlice (DirectedClosedPeriod representative)
      (NSetAsZ (BottomSCCLinearSlice nodes root representative attractor offset))
      (NSetAsZ (BottomSCCRegion nodes root representative)) faces earlier right ->
    ~ SpecialLeafRelationZ system left right).

Theorem bottom_scc_face_stripping : forall d (system : IBVAS d) safe
    (witness : SafetyWitness system safe) root representative
    representative_node,
  BottomSCCRoot (WitnessEdge (witness_nodes witness)) root ->
  BottomSCC (WitnessEdge (witness_nodes witness)) root representative ->
  witness_vertex_node (witness_nodes witness) representative
    representative_node ->
  exists offset faces,
    DirectedOffset representative_node offset /\
    BottomSCCStrippingPackage (witness_nodes witness) root
      representative_node (witness_attractor witness) offset faces.
Proof.
  intros d system safe witness root representative representative_node
    Hroot Hrepresentative Hrepresentative_node.
  destruct (bottom_scc_safe_extension d system safe witness root
    representative representative_node Hroot Hrepresentative
    Hrepresentative_node) as
    [offset [Hoffset [Hsafe [Hsemilinear [Hattractor [Hsafe_ext
      [Hfinite_slice Hback]]]]]]].
  assert (Hperiodic : Periodic (DirectedClosedPeriod representative_node)).
  { apply closed_linearization_periodic.
    apply periodic_nset_as_z, directed_offset_periodic. }
  assert (Hfinite : FinitelyGeneratedPeriodic
      (DirectedClosedPeriod representative_node)).
  { apply lemma_3_12_directed_closed_period_finitely_generated. }
  assert (Hfull : FullPeriodic (DirectedClosedPeriod representative_node)).
  { apply closed_linearization_full.
    apply periodic_nset_as_z, directed_offset_periodic. }
  assert (Hsubset : forall integer,
      NSetAsZ (BottomSCCLinearSlice (witness_nodes witness) root
        representative_node (witness_attractor witness) offset) integer ->
      NSetAsZ (BottomSCCRegion (witness_nodes witness) root
        representative_node) integer).
  { intros integer [natural [-> [_ HY]]]. exists natural. auto. }
  assert (HbackZ : BackwardPeriodCover
      (DirectedClosedPeriod representative_node)
      (NSetAsZ (BottomSCCLinearSlice (witness_nodes witness) root
        representative_node (witness_attractor witness) offset))
      (NSetAsZ (BottomSCCRegion (witness_nodes witness) root
        representative_node))).
  { intros integer [natural [-> HY]].
    destruct (Hback natural HY) as [increment [Hincrement HX]].
    exists (nvec_to_zvec increment). split; [exact Hincrement|].
    exists (nvec_add natural increment). split.
    - now rewrite nvec_to_zvec_add.
    - exact HX. }
  destruct (face_stripping_theorem_diagonal d
    (DirectedClosedPeriod representative_node)
    (NSetAsZ (BottomSCCLinearSlice (witness_nodes witness) root
      representative_node (witness_attractor witness) offset))
    (NSetAsZ (BottomSCCRegion (witness_nodes witness) root
      representative_node))
    (SpecialLeafRelationZ system)
    Hperiodic Hfinite Hfull Hfinite_slice
    (bottom_scc_region_z_finitary d system (witness_nodes witness) root
      representative_node) Hsubset
    (special_leaf_relation_z_diagonal d system representative_node)
    (bottom_scc_linear_slice_no_boundary d system (witness_nodes witness)
      root representative_node (witness_attractor witness) offset
      (bottom_scc_linear_reach_attractor d system
        (witness_attractor witness) representative_node offset
        (bottom_scc_invariant_inductive d system (witness_attractor witness)
          (witness_attractor_closed system safe witness)))))
    as [faces [Hstrip Hdiagonal]].
  exists offset, faces. split; [exact Hoffset|].
  unfold BottomSCCStrippingPackage.
  destruct Hstrip as [Hordered [Hhead [Hinitial [Hfinal
    [Hremainders [Hslices [Hdisjoint [Hcomplete Hfirst]]]]]]]].
  split; [exact Hordered|]. split; [exact Hhead|]. split.
  - intros stage face Hstage Hface.
    exact (proj1 (Hslices stage face Hstage Hface)).
  - split; [exact Hcomplete|]. split.
    + exact (Hfirst HbackZ).
    + exact Hdiagonal.
Qed.

Definition BottomSCCRun {d} {system : IBVAS d}
    (nodes : list (DirectedIRun system)) (root : WitnessVertex nodes)
    (run : IRun d) : Prop :=
  exists vertex node,
    BottomSCC (WitnessEdge nodes) root vertex /\
    witness_vertex_node nodes vertex node /\ DirectedRunMember node run.

Definition ResidualRun {d} {system : IBVAS d}
    (nodes : list (DirectedIRun system)) (root : WitnessVertex nodes)
    (period excluded remaining : ZSet d) faces (stage : nat) (run : IRun d) : Prop :=
  BottomSCCRun nodes root run /\
  StrippingSlice period excluded remaining faces stage
    (nvec_to_zvec (irun_target run)).

Definition ResidualRunLe {d} (period : ZSet d)
    (left right : IRun d) : Prop :=
  IRunLe left right /\
  PeriodicLe period (nvec_to_zvec (irun_target left))
    (nvec_to_zvec (irun_target right)).

Lemma residual_run_wqo : forall d (system : IBVAS d)
    (nodes : list (DirectedIRun system)) (root : WitnessVertex nodes)
    strip_period order_period excluded remaining faces (stage : nat),
  Periodic order_period -> FinitelyGeneratedPeriodic order_period ->
  FinitaryQCylindric order_period
    (StrippingSlice strip_period excluded remaining faces stage) ->
  @afs (IRun d)
    (ResidualRun nodes root strip_period excluded remaining faces stage)
    (ResidualRunLe order_period).
Proof.
  intros d system nodes root strip_period order_period excluded remaining faces stage
    Hperiodic Hfinite Hslice.
  apply af_sub_rel_afs.
  eapply af_rel_morph with
    (X := ({run : IRun d | ValidIRun system run} *
      {value : ZVec d |
        StrippingSlice strip_period excluded remaining faces stage value})%type)
    (f := fun pair run =>
      proj1_sig (fst pair) = proj1_sig run /\
      proj1_sig (snd pair) = nvec_to_zvec (irun_target (proj1_sig run)))
    (R := fun left right =>
      IRunLe (proj1_sig (fst left)) (proj1_sig (fst right)) /\
      PeriodicLe order_period (proj1_sig (snd left)) (proj1_sig (snd right)))
    (T := fun left right =>
      ResidualRunLe order_period (proj1_sig left) (proj1_sig right)).
  - intros [run [[vertex [node [Hbottom [Hnode Hmember]]]] Hrun_slice]].
    exists (exist _ run (proj1 Hmember),
      exist _ (nvec_to_zvec (irun_target run)) Hrun_slice). cbn. auto.
  - intros [[left Hleft_valid] [left_value Hleft_slice]]
      [[right Hright_valid] [right_value Hright_slice]]
      [left_run Hleft_run] [right_run Hright_run]
      [Hleft_eq Hleft_value] [Hright_eq Hright_value]
      [Hrun_le Hperiod_le].
    cbn in *. subst left_run right_run left_value right_value.
    now split.
  - eapply (@af_mono
      ({run : IRun d | ValidIRun system run} *
       {value : ZVec d |
         StrippingSlice strip_period excluded remaining faces stage value})%type
      (fun '(left_run, left_value) '(right_run, right_value) =>
        IRunLe (proj1_sig left_run) (proj1_sig right_run) /\
        PeriodicLe order_period (proj1_sig left_value)
          (proj1_sig right_value))
      (fun left right =>
        IRunLe (proj1_sig (fst left)) (proj1_sig (fst right)) /\
        PeriodicLe order_period (proj1_sig (snd left))
          (proj1_sig (snd right)))).
    + intros [left_run left_value] [right_run right_value] [Hrun Hvalue].
      cbn in *. split; assumption.
    + exact (@af_product
        {run : IRun d | ValidIRun system run}
        {value : ZVec d |
          StrippingSlice strip_period excluded remaining faces stage value}
        (fun left right => IRunLe (proj1_sig left) (proj1_sig right))
        (fun left right => PeriodicLe order_period
          (proj1_sig left) (proj1_sig right))
        (afs_af_sub_rel (irun_le_wqo d system))
        (afs_af_sub_rel (finitary_qcylindric_afs d order_period
          (StrippingSlice strip_period excluded remaining faces stage)
          Hperiodic Hfinite Hslice))).
Qed.

Theorem residual_run_finite_basis : forall d (system : IBVAS d)
    (nodes : list (DirectedIRun system)) (root : WitnessVertex nodes)
    strip_period order_period excluded remaining faces (stage : nat),
  Periodic order_period -> FinitelyGeneratedPeriodic order_period ->
  FinitaryQCylindric order_period
    (StrippingSlice strip_period excluded remaining faces stage) ->
  exists basis : list {run : IRun d |
      ResidualRun nodes root strip_period excluded remaining faces stage run},
    forall run,
      ResidualRun nodes root strip_period excluded remaining faces stage run ->
      exists base, List.In base basis /\
        ResidualRunLe order_period (proj1_sig base) run.
Proof.
  intros d system nodes root strip_period order_period excluded remaining faces stage
    Hperiodic Hfinite Hslice.
  destruct (restricted_af_finite_cover_classic (IRun d)
    (ResidualRun nodes root strip_period excluded remaining faces stage)
    (ResidualRunLe order_period)
    (residual_run_wqo d system nodes root strip_period order_period excluded
      remaining faces stage Hperiodic Hfinite Hslice)) as [basis Hbasis].
  exists basis. intros run Hrun.
  destruct (Hbasis (exist _ run Hrun)) as [base [Hbase Hle]].
  now exists base.
Qed.

Definition face_directed_irun {d} {system : IBVAS d}
    (run : IRun d) (Hvalid : ValidIRun system run)
    (generators : list (QVec d))
    (Hnonnegative : forall point,
      qcone_generated generators point -> forall index, 0 <= point index) :
    DirectedIRun system :=
  {| directed_root := run;
     directed_root_valid := Hvalid;
     directed_generators := generators;
     directed_cone_nonnegative := Hnonnegative |}.

Lemma residual_run_valid : forall d (system : IBVAS d)
    (nodes : list (DirectedIRun system)) (root : WitnessVertex nodes)
    period excluded remaining faces (stage : nat) run,
  ResidualRun nodes root period excluded remaining faces stage run ->
  ValidIRun system run.
Proof.
  intros d system nodes root period excluded remaining faces stage run
    [[vertex [node [_ [_ Hmember]]]] _]. exact (proj1 Hmember).
Qed.

Lemma face_generators_nonnegative : forall d (system : IBVAS d)
    (node : DirectedIRun system) face generators,
  FaceOf (Cone (DirectedClosedPeriod node)) face ->
  SameSet face (qcone_generated generators) ->
  forall point,
    qcone_generated generators point -> forall index, 0 <= point index.
Proof.
  intros d system node face generators Hface Hgenerators point Hpoint index.
  apply (cone_of_nonnegative_set_nonnegative d
    (DirectedClosedPeriod node)).
  - apply closed_linearization_nonnegative, directed_period_nonnegative.
  - apply (face_subset d (Cone (DirectedClosedPeriod node)) face Hface).
    now apply (proj2 (Hgenerators point)).
Qed.

Definition FaceBasisNodes {d} {system : IBVAS d} nodes root
    period excluded remaining faces stage
    (basis : list {run : IRun d |
      ResidualRun nodes root period excluded remaining faces stage run})
    (generators : list (QVec d))
    (Hnonnegative : forall point,
      qcone_generated generators point -> forall index, 0 <= point index) :
    list (DirectedIRun system) :=
  List.map (fun base => face_directed_irun (proj1_sig base)
    (residual_run_valid d system nodes root period excluded remaining faces
      stage (proj1_sig base) (proj2_sig base)) generators Hnonnegative) basis.

Lemma face_basis_nodes_member : forall d (system : IBVAS d) nodes root
    period excluded remaining faces stage basis generators Hnonnegative
    base,
  List.In base basis ->
  List.In (face_directed_irun (proj1_sig base)
      (residual_run_valid d system nodes root period excluded remaining faces
        stage (proj1_sig base) (proj2_sig base)) generators Hnonnegative)
    (FaceBasisNodes nodes root period excluded remaining faces stage basis
      generators Hnonnegative).
Proof.
  intros. unfold FaceBasisNodes. apply in_map_iff.
  exists base. split; [reflexivity|exact H].
Qed.

Lemma periodic_le_natural_offset : forall d (period : ZSet d)
    (left right : NVec d),
  nvec_le left right ->
  PeriodicLe period (nvec_to_zvec left) (nvec_to_zvec right) ->
  exists offset,
    right = nvec_add left offset /\ period (nvec_to_zvec offset).
Proof.
  intros d period left right Hle Hperiod.
  exists (nvec_sub_local right left). split.
  - now apply nvec_sub_exact_local.
  - unfold PeriodicLe in Hperiod.
    replace (nvec_to_zvec (nvec_sub_local right left)) with
      (zvec_sub (nvec_to_zvec right) (nvec_to_zvec left)); [exact Hperiod|].
    apply zvec_ext. intro index.
    unfold nvec_to_zvec, nvec_sub_local, zvec_sub.
    repeat rewrite (StdVector.nth_map _ _ index index eq_refl).
    rewrite (StdVector.nth_map2 Nat.sub _ _ index index index eq_refl eq_refl),
      (StdVector.nth_map2 Z.sub _ _ index index index eq_refl eq_refl).
    repeat rewrite (StdVector.nth_map Z.of_nat _ index index eq_refl).
    rewrite Nat2Z.inj_sub; [reflexivity|apply Hle].
Qed.

Theorem face_basis_nodes_cover : forall d (system : IBVAS d)
    (nodes : list (DirectedIRun system)) (root : WitnessVertex nodes)
    (representative : DirectedIRun system) excluded remaining faces
    (stage : nat) face
    basis generators Hnonnegative,
  SameSet face (qcone_generated generators) ->
  (forall run,
    ResidualRun nodes root (DirectedClosedPeriod representative)
      excluded remaining faces stage run ->
    exists base, List.In base basis /\
      ResidualRunLe (FacePeriod (DirectedClosedPeriod representative) face)
        (proj1_sig base) run) ->
  forall run,
    ResidualRun nodes root (DirectedClosedPeriod representative)
      excluded remaining faces stage run ->
  exists node,
    List.In node (FaceBasisNodes nodes root
      (DirectedClosedPeriod representative)
      excluded remaining faces stage basis generators Hnonnegative) /\
    DirectedRunMember node run.
Proof.
  intros d system nodes root representative excluded remaining faces stage face
    basis generators Hnonnegative Hgenerators Hcover run Hrun.
  destruct (Hcover run Hrun) as [base [Hbase [Hle Hperiod_le]]].
  set (node := face_directed_irun (proj1_sig base)
    (residual_run_valid d system nodes root
      (DirectedClosedPeriod representative)
      excluded remaining faces stage (proj1_sig base) (proj2_sig base))
    generators Hnonnegative).
  exists node. split.
  - unfold node. now apply face_basis_nodes_member.
  - split; [exact (residual_run_valid d system nodes root
      (DirectedClosedPeriod representative)
      excluded remaining faces stage run Hrun)|].
    destruct (periodic_le_natural_offset d
      (FacePeriod (DirectedClosedPeriod representative) face)
      (irun_target (proj1_sig base)) (irun_target run)
      (proj1 Hle) Hperiod_le) as [offset [Htarget Hoffset]].
    exists offset. split; [exact Hle|]. split; [exact Htarget|].
    assert (Heq : QVecEq (zvec_to_qvec (nvec_to_zvec offset))
        (nvec_to_qvec offset)).
    { apply nvec_zvec_qvec_commute. }
    apply (proj1 (qcone_generated_qvec_ext d generators
      (zvec_to_qvec (nvec_to_zvec offset)) (nvec_to_qvec offset) Heq)).
    apply (proj1 (Hgenerators (zvec_to_qvec (nvec_to_zvec offset)))).
    exact (proj2 Hoffset).
Qed.

(** Lemma 7.5's index argument only uses the member-closure half of the
    construction.  It forbids a new-node edge from a later stripping slice
    back to an earlier slice, while allowing equal indices. *)
Theorem lemma_7_5_new_node_edge_direction : forall d
    (system : IBVAS d) (period excluded remaining : ZSet d)
    (faces : list (QSet d)) (earlier later : nat)
    (source target : DirectedIRun system),
  (forall run, DirectedRunMember source run ->
    StrippingSlice period excluded remaining faces earlier
      (nvec_to_zvec (irun_target run))) ->
  (forall run, DirectedRunMember target run ->
    StrippingSlice period excluded remaining faces later
      (nvec_to_zvec (irun_target run))) ->
  (forall (i j : nat) left right,
    (i < j)%nat -> (j < length faces)%nat ->
    StrippingSlice period excluded remaining faces j left ->
    StrippingSlice period excluded remaining faces i right ->
    ~ SpecialLeafRelationZ system left right) ->
  (earlier < length faces)%nat ->
  (later < length faces)%nat ->
  DirectedIRunEdge source target ->
  (earlier <= later)%nat.
Proof.
  intros d system period excluded remaining faces earlier later source target
    Hsource Htarget Hdiagonal Hearlier Hlater Hedge.
  destruct (Nat.lt_ge_cases later earlier) as [Hback|Horder]; [|lia].
  exfalso. destruct Hedge as [source_run [target_run
    [Hsource_member [Htarget_member [context Hcontext]]]]].
  apply (Hdiagonal later earlier
    (nvec_to_zvec (irun_target source_run))
    (nvec_to_zvec (irun_target target_run)) Hback Hearlier
    (Hsource source_run Hsource_member)
    (Htarget target_run Htarget_member)).
  exists (irun_target source_run), (irun_target target_run).
  split; [reflexivity|]. split; [reflexivity|].
  subst target_run. apply valid_context_special_leaf.
  exact (proj1 Htarget_member).
Qed.

Definition RetainedOldNode {d} {system : IBVAS d}
    (nodes : list (DirectedIRun system)) root (node : DirectedIRun system) : Prop :=
  exists vertex,
    ~ BottomSCC (WitnessEdge nodes) root vertex /\
    witness_vertex_node nodes vertex node.

Lemma retained_old_nodes_finite : forall d (system : IBVAS d)
    (nodes : list (DirectedIRun system)) root,
  exists retained : list (DirectedIRun system),
    forall node, List.In node retained <-> RetainedOldNode nodes root node.
Proof.
  intros d system nodes root.
  destruct (finite_predicate_unique_image
    (WitnessVertex nodes) (DirectedIRun system)
    (finite_vertices (length nodes))
    (fun vertex => ~ BottomSCC (WitnessEdge nodes) root vertex)
    (fun vertex node => witness_vertex_node nodes vertex node))
    as [retained Hretained].
  - intros vertex _. apply witness_vertex_node_exists.
  - intros vertex left right Hleft Hright.
    now apply witness_vertex_node_unique with (nodes := nodes) (vertex := vertex).
  - exists retained. intro node. rewrite Hretained. unfold RetainedOldNode.
    split.
    + intros [vertex [_ [Houtside Hnode]]]. now exists vertex.
    + intros [vertex [Houtside Hnode]]. exists vertex. repeat split; try assumption.
      apply finite_vertices_complete.
Qed.

Lemma old_node_occurrence : forall d (system : IBVAS d)
    (nodes : list (DirectedIRun system)) node,
  List.In node nodes ->
  exists vertex, witness_vertex_node nodes vertex node.
Proof.
  intros d system nodes node Hin.
  apply In_nth_error in Hin as [index Hindex].
  assert (Hlt : (index < length nodes)%nat).
  { apply nth_error_Some. rewrite Hindex. discriminate. }
  exists (Fin.of_nat_lt Hlt). unfold witness_vertex_node.
  now rewrite Fin.to_nat_of_nat.
Qed.

Lemma old_node_bottom_or_retained : forall d (system : IBVAS d)
    (nodes : list (DirectedIRun system)) root node,
  List.In node nodes ->
  (exists vertex,
      BottomSCC (WitnessEdge nodes) root vertex /\
      witness_vertex_node nodes vertex node) \/
  RetainedOldNode nodes root node.
Proof.
  intros d system nodes root node Hin.
  destruct (old_node_occurrence d system nodes node Hin) as [vertex Hvertex].
  destruct (classic (BottomSCC (WitnessEdge nodes) root vertex)) as [Hbottom|Hout].
  - left. now exists vertex.
  - right. exists vertex. auto.
Qed.

(** A finite homogeneous half-space presentation is closed for the rational
    sup metric used by [QClosure].  This is the small topological bridge
    needed below; no passage through real numbers is involved. *)
Fixpoint witness_qvec_abs_sum (d : nat) : QVec d -> Q :=
  match d return QVec d -> Q with
  | O => fun _ => 0
  | S d' => fun value => Qabs (value Fin.F1) +
      witness_qvec_abs_sum d' (fun index => value (Fin.FS index))
  end.

Lemma witness_qvec_abs_sum_nonnegative : forall d (value : QVec d),
  0 <= witness_qvec_abs_sum d value.
Proof.
  intros d. induction d as [|d IH]; intro value; cbn.
  - apply Qle_refl.
  - setoid_replace 0 with (0 + 0) by ring.
    apply Qplus_le_compat; [apply Qabs_nonneg|apply IH].
Qed.

Lemma qinner_uniform_near : forall d (normal left right : QVec d) epsilon,
  0 < epsilon ->
  (forall index, Qabs (left index - right index) < epsilon) ->
  Qabs (qinner normal left - qinner normal right) <
    (1 + witness_qvec_abs_sum d normal) * epsilon.
Proof.
  intros d. induction d as [|d IH]; intros normal left right epsilon
    Hepsilon Hnear.
  - cbn [qinner qrow_apply qvec_to_vector qdot witness_qvec_abs_sum Qabs].
    setoid_replace ((1 + 0) * epsilon) with epsilon by ring.
    exact Hepsilon.
  - cbn [qinner qrow_apply qvec_to_vector qdot witness_qvec_abs_sum].
    setoid_replace
      (normal Fin.F1 * left Fin.F1 +
         qdot (qvec_to_vector d (fun index => normal (Fin.FS index)))
           (qvec_to_vector d (fun index => left (Fin.FS index))) -
       (normal Fin.F1 * right Fin.F1 +
         qdot (qvec_to_vector d (fun index => normal (Fin.FS index)))
           (qvec_to_vector d (fun index => right (Fin.FS index)))))
      with
      (normal Fin.F1 * (left Fin.F1 - right Fin.F1) +
       (qinner (fun index => normal (Fin.FS index))
          (fun index => left (Fin.FS index)) -
        qinner (fun index => normal (Fin.FS index))
          (fun index => right (Fin.FS index)))) by
        (unfold qinner, qrow_apply; ring).
    eapply Qle_lt_trans; [apply Qabs_triangle|].
    assert (Hhead :
        Qabs (normal Fin.F1 * (left Fin.F1 - right Fin.F1)) <=
          Qabs (normal Fin.F1) * epsilon).
    { setoid_rewrite Qabs_Qmult.
      pose proof (Qmult_le_compat_r
        (Qabs (left Fin.F1 - right Fin.F1)) epsilon
        (Qabs (normal Fin.F1))
        (Qlt_le_weak _ _ (Hnear Fin.F1))
        (Qabs_nonneg (normal Fin.F1))) as Hscaled.
      setoid_replace
        (Qabs (left Fin.F1 - right Fin.F1) * Qabs (normal Fin.F1))
        with
        (Qabs (normal Fin.F1) * Qabs (left Fin.F1 - right Fin.F1))
        in Hscaled by ring.
      setoid_replace (epsilon * Qabs (normal Fin.F1))
        with (Qabs (normal Fin.F1) * epsilon) in Hscaled by ring.
      exact Hscaled. }
    assert (Htail :
        Qabs
          (qinner (fun index => normal (Fin.FS index))
             (fun index => left (Fin.FS index)) -
           qinner (fun index => normal (Fin.FS index))
             (fun index => right (Fin.FS index))) <
        (1 + witness_qvec_abs_sum d (fun index => normal (Fin.FS index))) *
          epsilon).
    { apply IH; [exact Hepsilon|]. intro index. apply Hnear. }
    setoid_replace
      (Qabs (normal Fin.F1 * (left Fin.F1 - right Fin.F1)) +
       Qabs
         (qinner (fun index => normal (Fin.FS index))
            (fun index => left (Fin.FS index)) -
          qinner (fun index => normal (Fin.FS index))
            (fun index => right (Fin.FS index))))
      with
      (Qabs
         (qinner (fun index => normal (Fin.FS index))
            (fun index => left (Fin.FS index)) -
          qinner (fun index => normal (Fin.FS index))
            (fun index => right (Fin.FS index))) +
       Qabs (normal Fin.F1 * (left Fin.F1 - right Fin.F1)))
      by ring.
    setoid_replace
      ((1 + (Qabs (normal Fin.F1) +
         witness_qvec_abs_sum d (fun index => normal (Fin.FS index)))) * epsilon)
      with
      ((1 + witness_qvec_abs_sum d
          (fun index => normal (Fin.FS index))) * epsilon +
       Qabs (normal Fin.F1) * epsilon)
      by ring.
    apply Qplus_lt_le_compat; [exact Htail|exact Hhead].
Qed.

Lemma rational_polyhedral_cone_topologically_closed_update : forall d
    (cone : QSet d),
  RationalPolyhedralCone cone -> TopologicallyClosed cone.
Proof.
  intros d cone Hpolyhedral point Hclosure.
  destruct (polyhedral_cone_integer_hrep d cone Hpolyhedral) as
    [normals Hnormals].
  apply (proj2 (Hnormals point)). intros normal Hnormal.
  destruct (Qlt_le_dec (qinner (zvec_to_qvec normal) point) 0)
    as [Hnegative|Hnonnegative]; [|exact Hnonnegative].
  set (weight := 1 + witness_qvec_abs_sum d (zvec_to_qvec normal)).
  assert (Hweight : 0 < weight).
  { unfold weight.
    pose proof (witness_qvec_abs_sum_nonnegative d
      (zvec_to_qvec normal)) as Hsum.
    setoid_replace 0 with (0 + 0) by ring.
    apply Qplus_lt_le_compat.
    - unfold Qlt; cbn; lia.
    - exact Hsum. }
  set (epsilon := (- qinner (zvec_to_qvec normal) point) / weight).
  assert (Hepsilon : 0 < epsilon).
  { unfold epsilon. apply Qmult_lt_0_compat.
    - setoid_replace 0 with (- 0) by ring.
      now apply Qopp_lt_compat.
    - now apply Qinv_lt_0_compat. }
  destruct (Hclosure epsilon Hepsilon) as
    [approximant [Happroximant Hnear]].
  assert (Happroximant_nonnegative :
      0 <= qinner (zvec_to_qvec normal) approximant).
  { apply (proj1 (Hnormals approximant) Happroximant normal Hnormal). }
  pose proof (qinner_uniform_near d (zvec_to_qvec normal) point approximant
    epsilon Hepsilon Hnear) as Hinner_near.
  unfold epsilon, weight in Hinner_near.
  assert (Hweight_nonzero : ~ 1 + witness_qvec_abs_sum d
      (zvec_to_qvec normal) == 0).
  { intro Heq. apply (Qlt_not_eq _ _ Hweight). symmetry. exact Heq. }
  setoid_replace
    ((1 + witness_qvec_abs_sum d (zvec_to_qvec normal)) *
      (- qinner (zvec_to_qvec normal) point /
       (1 + witness_qvec_abs_sum d (zvec_to_qvec normal))))
    with (- qinner (zvec_to_qvec normal) point) in Hinner_near by
      (field; exact Hweight_nonzero).
  assert (Hdifference_nonpositive :
      qinner (zvec_to_qvec normal) point -
        qinner (zvec_to_qvec normal) approximant <= 0).
  { assert (Hpoint_approximant :
        qinner (zvec_to_qvec normal) point <=
          qinner (zvec_to_qvec normal) approximant).
    { eapply Qle_trans; [apply Qlt_le_weak; exact Hnegative|].
      exact Happroximant_nonnegative. }
    setoid_replace 0 with
      (qinner (zvec_to_qvec normal) approximant +
       - qinner (zvec_to_qvec normal) approximant) by ring.
    apply Qplus_le_compat; [exact Hpoint_approximant|apply Qle_refl]. }
  setoid_rewrite
    (Qabs_neg
      (qinner (zvec_to_qvec normal) point -
       qinner (zvec_to_qvec normal) approximant)
      Hdifference_nonpositive) in Hinner_near.
  assert (Happroximant_negative :
      qinner (zvec_to_qvec normal) approximant < 0).
  { setoid_replace (qinner (zvec_to_qvec normal) approximant) with
      (- (qinner (zvec_to_qvec normal) point -
          qinner (zvec_to_qvec normal) approximant) +
       qinner (zvec_to_qvec normal) point) by ring.
    setoid_replace 0 with
      (- qinner (zvec_to_qvec normal) point +
       qinner (zvec_to_qvec normal) point) by ring.
    apply Qplus_lt_le_compat; [exact Hinner_near|apply Qle_refl]. }
  exfalso.
  exact ((Qlt_not_le _ _ Happroximant_negative)
    Happroximant_nonnegative).
Qed.

Lemma directed_closed_period_cone_included : forall d (system : IBVAS d)
    (node : DirectedIRun system) point,
  Cone (DirectedClosedPeriod node) point -> DirectedCone node point.
Proof.
  intros d system node point Hpoint.
  assert (Hcone : IsCone (DirectedCone node)).
  { unfold DirectedCone. apply qcone_generated_is_cone. }
  assert (Hclosed : TopologicallyClosed (DirectedCone node)).
  { apply rational_polyhedral_cone_topologically_closed_update.
    apply directed_cone_polyhedral. }
  assert (Hgenerator : forall integer,
      DirectedClosedPeriod node integer ->
      DirectedCone node (zvec_to_qvec integer)).
  { intros integer [Hdifference Hclosure].
    apply Hclosed.
    eapply qclosure_monotone; [|exact Hclosure].
    intros value Hvalue.
    exact (proj2
      (proj1 (directed_period_cone_iff d system node value) Hvalue)). }
  destruct Hpoint as [generated [Hgenerated Hpoint]].
  assert (Hgenerated_in : DirectedCone node generated).
  { clear point Hpoint.
    induction Hgenerated.
    - exact (cone_contains_zero _ Hcone).
    - apply (cone_closed_add _ Hcone).
      + apply (cone_closed_scale _ Hcone); [exact H|].
        now apply Hgenerator.
      + exact IHHgenerated. }
  apply (proj2 (qcone_generated_qvec_ext d (directed_generators node)
    point generated Hpoint)).
  exact Hgenerated_in.
Qed.

(** Every run represented by a face-basis node stays in the stripping
    component from which its basis run was selected.  The essential point is
    that an offset of the new node is simultaneously an [IRunPeriod] offset
    of its basis run and a point of the selected face.  Rebase (Lemma 7.4)
    puts the former in the old SCC closed period; cylindricity of the slice
    then absorbs the offset. *)
Lemma face_basis_node_members_slice : forall d (system : IBVAS d)
    (nodes : list (DirectedIRun system)) (root : WitnessVertex nodes)
    representative_vertex (representative : DirectedIRun system)
    excluded remaining faces stage face generators Hnonnegative
    (base : {run : IRun d |
      ResidualRun nodes root (DirectedClosedPeriod representative)
        excluded remaining faces stage run}),
  HomogeneousWitnessNodes nodes ->
  BottomSCCRoot (WitnessEdge nodes) root ->
  BottomSCC (WitnessEdge nodes) root representative_vertex ->
  witness_vertex_node nodes representative_vertex representative ->
  OrderedStrippingFaces (DirectedClosedPeriod representative) faces ->
  nth_error faces stage = Some face ->
  SameSet face (qcone_generated generators) ->
  FinitaryQCylindric
    (FacePeriod (DirectedClosedPeriod representative) face)
    (StrippingSlice (DirectedClosedPeriod representative)
      excluded remaining faces stage) ->
  forall run,
    DirectedRunMember
      (face_directed_irun (proj1_sig base)
        (residual_run_valid d system nodes root
          (DirectedClosedPeriod representative) excluded remaining faces
          stage (proj1_sig base) (proj2_sig base))
        generators Hnonnegative) run ->
    StrippingSlice (DirectedClosedPeriod representative)
      excluded remaining faces stage (nvec_to_zvec (irun_target run)).
Proof.
  intros d system nodes root representative_vertex representative excluded
    remaining faces stage face generators Hnonnegative base Hhom Hroot
    Hrepresentative Hrepresentative_node Hordered Hface Hgenerators Hfinite
    run Hrun.
  destruct (proj2_sig base) as
    [[member_vertex [member_node [Hmember_bottom
      [Hmember_node Hbase_member]]]] Hbase_slice].
  destruct Hrun as [Hrun_valid [offset [Hbase_le [Hrun_target Hoffset_face]]]].
  cbn in Hbase_le, Hrun_target, Hoffset_face.
  assert (Hface_of : FaceOf (Cone (DirectedClosedPeriod representative)) face).
  { apply (proj1 (proj2 (proj2 Hordered))).
    now apply nth_error_In with (n := stage). }
  assert (Hoffset_representative_cone :
      DirectedCone representative (nvec_to_qvec offset)).
  { apply directed_closed_period_cone_included.
    apply (face_subset d (Cone (DirectedClosedPeriod representative)) face
      Hface_of).
    apply (proj2 (Hgenerators (nvec_to_qvec offset))).
    exact Hoffset_face. }
  assert (Hoffset_member_cone :
      DirectedCone member_node (nvec_to_qvec offset)).
  { apply (proj1 (bottom_scc_common_cone d system nodes root
      representative_vertex representative member_vertex member_node
      Hhom Hrepresentative Hmember_bottom Hrepresentative_node
      Hmember_node (nvec_to_qvec offset))).
    exact Hoffset_representative_cone. }
  assert (Hrebase_member : DirectedRunMember
      (rebase_directed_irun member_node (proj1_sig base) Hbase_member) run).
  { split; [exact Hrun_valid|]. exists offset. split; [exact Hbase_le|].
    split; [exact Hrun_target|]. cbn. exact Hoffset_member_cone. }
  assert (Hoffset_member_closed :
      DirectedClosedPeriod member_node (nvec_to_zvec offset)).
  { apply (proj2 (lemma_7_4_directed_irun_rebase d system member_node
      (proj1_sig base) Hbase_member)).
    exists offset. split; [reflexivity|]. split.
    - exists run. split; [exact Hrun_valid|]. split; [exact Hbase_le|].
      exact Hrun_target.
    - exact Hoffset_member_cone. }
  assert (Hoffset_representative_closed :
      DirectedClosedPeriod representative (nvec_to_zvec offset)).
  { apply (proj2 (bottom_scc_common_closed_period d system nodes root
      representative_vertex representative member_vertex member_node
      Hhom Hroot Hrepresentative Hmember_bottom Hrepresentative_node
      Hmember_node (nvec_to_zvec offset))).
    exact Hoffset_member_closed. }
  assert (Hoffset_period :
      FacePeriod (DirectedClosedPeriod representative) face
        (nvec_to_zvec offset)).
  { split; [exact Hoffset_representative_closed|].
    apply (proj2 (Hgenerators (zvec_to_qvec (nvec_to_zvec offset)))).
    apply (proj2 (qcone_generated_qvec_ext d generators
      (zvec_to_qvec (nvec_to_zvec offset)) (nvec_to_qvec offset)
      (nvec_zvec_qvec_commute d offset))).
    exact Hoffset_face. }
  pose proof (finitary_qcylindric_implies_cylindric d
    (FacePeriod (DirectedClosedPeriod representative) face)
    (StrippingSlice (DirectedClosedPeriod representative)
      excluded remaining faces stage)
    (face_periodic d (DirectedClosedPeriod representative) face
      (closed_linearization_periodic d (DirectedPeriod representative)
        (directed_period_periodic d system representative)) Hface_of)
    Hfinite) as Hstable.
  specialize (Hstable (nvec_to_zvec (irun_target (proj1_sig base)))
    (nvec_to_zvec offset) Hbase_slice Hoffset_period).
  rewrite <- nvec_to_zvec_add, <- Hrun_target in Hstable.
  exact Hstable.
Qed.

Lemma face_directed_irun_rank_lt : forall d (system : IBVAS d)
    (representative : DirectedIRun system) faces stage face generators
    (run : IRun d) (Hvalid : ValidIRun system run)
    (Hnonnegative : forall point,
      qcone_generated generators point -> forall index, 0 <= point index),
  OrderedStrippingFaces (DirectedClosedPeriod representative) faces ->
  (0 < stage)%nat ->
  nth_error faces stage = Some face ->
  SameSet face (qcone_generated generators) ->
  (directed_irun_rank
      (face_directed_irun run Hvalid generators Hnonnegative) <
    directed_irun_rank representative)%nat.
Proof.
  intros d system representative faces stage face generators run Hvalid
    Hnonnegative Hordered Hpositive Hface Hgenerators.
  destruct (polyhedral_span_dimension_exists d
    (Cone (DirectedClosedPeriod representative))) as
    [cone_dimension Hcone_dimension].
  { apply finitely_generated_period_cone_polyhedral.
    - apply closed_linearization_periodic, directed_period_periodic.
    - apply lemma_3_12_directed_closed_period_finitely_generated. }
  assert (Hface_dimension : SpanDimension face
      (directed_irun_rank
        (face_directed_irun run Hvalid generators Hnonnegative))).
  { assert (Hface_of : FaceOf
        (Cone (DirectedClosedPeriod representative)) face).
    { apply (proj1 (proj2 (proj2 Hordered))).
      now apply nth_error_In with (n := stage). }
    destruct (polyhedral_span_dimension_exists d face) as
      [face_dimension Hface_dimension].
    { apply polyhedral_face_finitely_generated with
        (cone := Cone (DirectedClosedPeriod representative)).
      - apply finitely_generated_period_cone_polyhedral.
        + apply closed_linearization_periodic, directed_period_periodic.
        + apply lemma_3_12_directed_closed_period_finitely_generated.
      - exact Hface_of. }
    assert (Heq : face_dimension =
        directed_irun_rank
          (face_directed_irun run Hvalid generators Hnonnegative)).
    { eapply span_dimension_same_set.
      - exact Hgenerators.
      - exact Hface_dimension.
      - exists generators. split; [apply qcone_span_presentation|reflexivity]. }
    now subst face_dimension. }
  assert (Hface_lt :
      (directed_irun_rank
        (face_directed_irun run Hvalid generators Hnonnegative) <
       cone_dimension)%nat).
  { eapply ordered_stripping_noninitial_face_dimension_lt; eauto.
    - apply closed_linearization_periodic, directed_period_periodic.
    - apply lemma_3_12_directed_closed_period_finitely_generated. }
  assert (Hcone_le :
      (cone_dimension <= directed_irun_rank representative)%nat).
  { eapply (span_dimension_monotone d
      (Cone (DirectedClosedPeriod representative))
      (DirectedCone representative) cone_dimension
      (directed_irun_rank representative)).
    - intros point Hpoint.
      exact (directed_closed_period_cone_included d system representative
        point Hpoint).
    - exact Hcone_dimension.
    - apply directed_irun_rank_span. }
  lia.
Qed.

Record FaceReplacementBlock {d} {system : IBVAS d}
    (nodes : list (DirectedIRun system)) (root : WitnessVertex nodes)
    (representative : DirectedIRun system) (excluded remaining : ZSet d)
    (faces : list (QSet d)) : Type := {
  replacement_stage : nat;
  replacement_stage_positive : (0 < replacement_stage)%nat;
  replacement_stage_bounded : (replacement_stage < length faces)%nat;
  replacement_face : QSet d;
  replacement_face_at :
    nth_error faces replacement_stage = Some replacement_face;
  replacement_generators : list (QVec d);
  replacement_generates :
    SameSet replacement_face (qcone_generated replacement_generators);
  replacement_nonnegative : forall point,
    qcone_generated replacement_generators point ->
    forall index, 0 <= point index;
  replacement_basis : list {run : IRun d |
    ResidualRun nodes root (DirectedClosedPeriod representative)
      excluded remaining faces replacement_stage run};
  replacement_basis_cover : forall run,
    ResidualRun nodes root (DirectedClosedPeriod representative)
      excluded remaining faces replacement_stage run ->
    exists base, List.In base replacement_basis /\
      ResidualRunLe
        (FacePeriod (DirectedClosedPeriod representative) replacement_face)
        (proj1_sig base) run
}.

Arguments replacement_stage {d system nodes root representative excluded
  remaining faces} _.
Arguments replacement_stage_positive {d system nodes root representative
  excluded remaining faces} _.
Arguments replacement_stage_bounded {d system nodes root representative
  excluded remaining faces} _.
Arguments replacement_face {d system nodes root representative excluded
  remaining faces} _.
Arguments replacement_face_at {d system nodes root representative excluded
  remaining faces} _.
Arguments replacement_generators {d system nodes root representative excluded
  remaining faces} _.
Arguments replacement_generates {d system nodes root representative excluded
  remaining faces} _ _.
Arguments replacement_nonnegative {d system nodes root representative excluded
  remaining faces} _ _ _ _.
Arguments replacement_basis {d system nodes root representative excluded
  remaining faces} _.
Arguments replacement_basis_cover {d system nodes root representative excluded
  remaining faces} _ _ _.

Definition replacement_block_nodes {d} {system : IBVAS d}
    {nodes : list (DirectedIRun system)} {root : WitnessVertex nodes}
    {representative : DirectedIRun system} {excluded remaining : ZSet d}
    {faces : list (QSet d)}
    (block : FaceReplacementBlock nodes root representative excluded remaining
      faces) : list (DirectedIRun system) :=
  FaceBasisNodes nodes root (DirectedClosedPeriod representative)
    excluded remaining faces (replacement_stage block)
    (replacement_basis block) (replacement_generators block)
    (replacement_nonnegative block).

Definition tagged_replacement_block_nodes {d} {system : IBVAS d}
    {nodes : list (DirectedIRun system)} {root : WitnessVertex nodes}
    {representative : DirectedIRun system} {excluded remaining : ZSet d}
    {faces : list (QSet d)}
    (block : FaceReplacementBlock nodes root representative excluded remaining
      faces) : list (nat * DirectedIRun system) :=
  List.map (fun node => (replacement_stage block, node))
    (replacement_block_nodes block).

Definition replacement_nodes {d} {system : IBVAS d}
    {nodes : list (DirectedIRun system)} {root : WitnessVertex nodes}
    {representative : DirectedIRun system} {excluded remaining : ZSet d}
    {faces : list (QSet d)}
    (blocks : list (FaceReplacementBlock nodes root representative excluded
      remaining faces)) : list (DirectedIRun system) :=
  List.concat (List.map replacement_block_nodes blocks).

Definition tagged_replacement_nodes {d} {system : IBVAS d}
    {nodes : list (DirectedIRun system)} {root : WitnessVertex nodes}
    {representative : DirectedIRun system} {excluded remaining : ZSet d}
    {faces : list (QSet d)}
    (blocks : list (FaceReplacementBlock nodes root representative excluded
      remaining faces)) : list (nat * DirectedIRun system) :=
  List.concat (List.map tagged_replacement_block_nodes blocks).

Lemma face_replacement_block_exists : forall d (system : IBVAS d)
    (nodes : list (DirectedIRun system)) (root : WitnessVertex nodes)
    (representative : DirectedIRun system) excluded remaining faces stage,
  OrderedStrippingFaces (DirectedClosedPeriod representative) faces ->
  (forall index face,
    (index < length faces)%nat -> nth_error faces index = Some face ->
    FinitaryQCylindric
      (FacePeriod (DirectedClosedPeriod representative) face)
      (StrippingSlice (DirectedClosedPeriod representative)
        excluded remaining faces index)) ->
  (0 < stage)%nat -> (stage < length faces)%nat ->
  exists block : FaceReplacementBlock nodes root representative excluded
      remaining faces,
    replacement_stage block = stage.
Proof.
  intros d system nodes root representative excluded remaining faces stage
    Hordered Hslices Hpositive Hbounded.
  destruct (nth_error faces stage) as [face|] eqn:Hface.
  2:{ apply nth_error_None in Hface. lia. }
  assert (Hface_of : FaceOf (Cone (DirectedClosedPeriod representative)) face).
  { apply (proj1 (proj2 (proj2 Hordered))).
    now apply nth_error_In with (n := stage). }
  destruct (polyhedral_face_finitely_generated d
    (Cone (DirectedClosedPeriod representative)) face) as
    [generators Hgenerators].
  { apply finitely_generated_period_cone_polyhedral.
    - apply closed_linearization_periodic, directed_period_periodic.
    - apply lemma_3_12_directed_closed_period_finitely_generated. }
  { exact Hface_of. }
  assert (Hnonnegative : forall point,
      qcone_generated generators point -> forall index, 0 <= point index).
  { eapply face_generators_nonnegative; eauto. }
  assert (Hperiodic : Periodic
      (FacePeriod (DirectedClosedPeriod representative) face)).
  { apply face_periodic; [apply closed_linearization_periodic,
      directed_period_periodic|exact Hface_of]. }
  assert (Hfinite_period : FinitelyGeneratedPeriodic
      (FacePeriod (DirectedClosedPeriod representative) face)).
  { apply face_periodic_finitely_generated;
      [apply lemma_3_12_directed_closed_period_finitely_generated|exact Hface_of]. }
  pose proof (Hslices stage face Hbounded Hface) as Hslice.
  destruct (residual_run_finite_basis d system nodes root
    (DirectedClosedPeriod representative)
    (FacePeriod (DirectedClosedPeriod representative) face)
    excluded remaining faces stage Hperiodic Hfinite_period Hslice) as
    [basis Hbasis].
  unshelve eexists ({| replacement_stage := stage;
    replacement_stage_positive := Hpositive;
    replacement_stage_bounded := Hbounded;
    replacement_face := face;
    replacement_face_at := Hface;
    replacement_generators := generators;
    replacement_generates := Hgenerators;
    replacement_nonnegative := Hnonnegative;
    replacement_basis := basis;
    replacement_basis_cover := Hbasis |}).
  reflexivity.
Qed.

Lemma face_replacement_blocks_exists : forall d (system : IBVAS d)
    (nodes : list (DirectedIRun system)) (root : WitnessVertex nodes)
    (representative : DirectedIRun system) excluded remaining faces,
  OrderedStrippingFaces (DirectedClosedPeriod representative) faces ->
  (forall index face,
    (index < length faces)%nat -> nth_error faces index = Some face ->
    FinitaryQCylindric
      (FacePeriod (DirectedClosedPeriod representative) face)
      (StrippingSlice (DirectedClosedPeriod representative)
        excluded remaining faces index)) ->
  exists blocks : list (FaceReplacementBlock nodes root representative
      excluded remaining faces),
    forall stage, (0 < stage)%nat -> (stage < length faces)%nat ->
      exists block, List.In block blocks /\ replacement_stage block = stage.
Proof.
  intros d system nodes root representative excluded remaining faces
    Hordered Hslices.
  assert (Hbuild : forall stages : list nat,
      (forall stage, List.In stage stages ->
        (0 < stage)%nat /\ (stage < length faces)%nat) ->
      exists blocks : list (FaceReplacementBlock nodes root representative
          excluded remaining faces),
        forall stage, List.In stage stages ->
          exists block, List.In block blocks /\ replacement_stage block = stage).
  { intro stages. induction stages as [|stage stages IH]; intro Hbounds.
    - exists []. intros found Hin. contradiction.
    - destruct (face_replacement_block_exists d system nodes root
        representative excluded remaining faces stage Hordered Hslices
        (proj1 (Hbounds stage (or_introl eq_refl)))
        (proj2 (Hbounds stage (or_introl eq_refl)))) as [block Hblock].
      destruct (IH ltac:(intros found Hin; apply Hbounds; now right)) as
        [blocks Hblocks].
      exists (block :: blocks). intros candidate Hcandidate.
      destruct Hcandidate as [Heq|Htail].
      { subst candidate. exists block. split; [now left|exact Hblock]. }
      { destruct (Hblocks _ Htail) as [other [Hother Heq]].
        exists other. split; [now right|exact Heq]. } }
  set (stages := List.seq 1 (Nat.pred (length faces))).
  destruct (Hbuild stages) as [blocks Hblocks].
  { intros stage Hstage. unfold stages in Hstage. apply in_seq in Hstage. lia. }
  exists blocks. intros stage Hpositive Hbounded.
  apply Hblocks. unfold stages. apply in_seq. lia.
Qed.

Lemma in_tagged_replacement_nodes_iff : forall d (system : IBVAS d)
    (nodes : list (DirectedIRun system)) (root : WitnessVertex nodes)
    (representative : DirectedIRun system) excluded remaining faces blocks
    stage node,
  List.In (stage, node)
    (@tagged_replacement_nodes d system nodes root representative excluded
      remaining faces blocks) <->
  exists block, List.In block blocks /\
    replacement_stage block = stage /\
    List.In node (replacement_block_nodes block).
Proof.
  intros. unfold tagged_replacement_nodes.
  rewrite in_concat. split.
  - intros [tagged [Htagged Hpair]].
    apply in_map_iff in Htagged as [block [Heq_tagged Hblock]].
    subst tagged.
    apply in_map_iff in Hpair as [found [Heq Hfound]].
    inversion Heq. subst. exists block. auto.
  - intros [block [Hblock [<- Hnode]]].
    exists (tagged_replacement_block_nodes block). split.
    + apply in_map_iff. exists block. auto.
    + apply in_map_iff. exists node. auto.
Qed.

Lemma replacement_block_nodes_cover : forall d (system : IBVAS d)
    (nodes : list (DirectedIRun system)) (root : WitnessVertex nodes)
    (representative : DirectedIRun system) excluded remaining faces
    (block : FaceReplacementBlock nodes root representative excluded remaining
      faces) run,
  ResidualRun nodes root (DirectedClosedPeriod representative)
    excluded remaining faces (replacement_stage block) run ->
  exists node, List.In node (replacement_block_nodes block) /\
    DirectedRunMember node run.
Proof.
  intros d system nodes root representative excluded remaining faces block run
    Hrun.
  eapply face_basis_nodes_cover.
  - exact (replacement_generates block).
  - exact (replacement_basis_cover block).
  - exact Hrun.
Qed.

Lemma replacement_blocks_cover : forall d (system : IBVAS d)
    (nodes : list (DirectedIRun system)) (root : WitnessVertex nodes)
    (representative : DirectedIRun system) excluded remaining faces
    (blocks : list (FaceReplacementBlock nodes root representative excluded
      remaining faces)),
  (forall stage, (0 < stage)%nat -> (stage < length faces)%nat ->
    exists block, List.In block blocks /\ replacement_stage block = stage) ->
  forall stage run,
    (0 < stage)%nat -> (stage < length faces)%nat ->
    ResidualRun nodes root (DirectedClosedPeriod representative)
      excluded remaining faces stage run ->
    exists node,
      List.In (stage, node) (tagged_replacement_nodes blocks) /\
      DirectedRunMember node run.
Proof.
  intros d system nodes root representative excluded remaining faces blocks
    Hblocks stage run Hpositive Hbounded Hrun.
  destruct (Hblocks stage Hpositive Hbounded) as [block [Hblock Hstage]].
  subst stage.
  destruct (replacement_block_nodes_cover d system nodes root representative
    excluded remaining faces block run Hrun) as [node [Hnode Hmember]].
  exists node. split; [|exact Hmember].
  apply in_tagged_replacement_nodes_iff.
  exists block. auto.
Qed.

Lemma replacement_node_stage_properties : forall d (system : IBVAS d)
    (nodes : list (DirectedIRun system)) (root : WitnessVertex nodes)
    representative_vertex (representative : DirectedIRun system)
    excluded remaining faces
    (blocks : list (FaceReplacementBlock nodes root representative excluded
      remaining faces)) stage node,
  HomogeneousWitnessNodes nodes ->
  BottomSCCRoot (WitnessEdge nodes) root ->
  BottomSCC (WitnessEdge nodes) root representative_vertex ->
  witness_vertex_node nodes representative_vertex representative ->
  OrderedStrippingFaces (DirectedClosedPeriod representative) faces ->
  (forall index face,
    (index < length faces)%nat -> nth_error faces index = Some face ->
    FinitaryQCylindric
      (FacePeriod (DirectedClosedPeriod representative) face)
      (StrippingSlice (DirectedClosedPeriod representative)
        excluded remaining faces index)) ->
  List.In (stage, node) (tagged_replacement_nodes blocks) ->
  (0 < stage)%nat /\ (stage < length faces)%nat /\
  (forall run, DirectedRunMember node run ->
    StrippingSlice (DirectedClosedPeriod representative)
      excluded remaining faces stage (nvec_to_zvec (irun_target run))) /\
  (directed_irun_rank node < directed_irun_rank representative)%nat.
Proof.
  intros d system nodes root representative_vertex representative excluded
    remaining faces blocks stage node Hhom Hroot Hrepresentative
    Hrepresentative_node Hordered Hslices Hin.
  apply in_tagged_replacement_nodes_iff in Hin as
    [block [Hblock [Hstage Hnode]]].
  subst stage.
  unfold replacement_block_nodes in Hnode.
  apply in_map_iff in Hnode as [base [Heq Hbase]]. subst node.
  repeat split.
  - exact (replacement_stage_positive block).
  - exact (replacement_stage_bounded block).
  - intros run Hmember.
    eapply (face_basis_node_members_slice d system nodes root
      representative_vertex representative excluded remaining faces
      (replacement_stage block) (replacement_face block)
      (replacement_generators block) (replacement_nonnegative block) base).
    + exact Hhom.
    + exact Hroot.
    + exact Hrepresentative.
    + exact Hrepresentative_node.
    + exact Hordered.
    + exact (replacement_face_at block).
    + exact (replacement_generates block).
    + apply Hslices; [apply replacement_stage_bounded|apply replacement_face_at].
    + exact Hmember.
  - eapply (face_directed_irun_rank_lt d system representative faces
      (replacement_stage block) (replacement_face block)
      (replacement_generators block) (proj1_sig base)
      (residual_run_valid d system nodes root
        (DirectedClosedPeriod representative) excluded remaining faces
        (replacement_stage block) (proj1_sig base) (proj2_sig base))
      (replacement_nonnegative block)).
    + exact Hordered.
    + apply replacement_stage_positive.
    + apply replacement_face_at.
    + apply replacement_generates.
Qed.

Lemma replacement_node_embeds_bottom : forall d (system : IBVAS d)
    (nodes : list (DirectedIRun system)) (root : WitnessVertex nodes)
    representative_vertex (representative : DirectedIRun system)
    excluded remaining faces
    (blocks : list (FaceReplacementBlock nodes root representative excluded
      remaining faces)) stage node,
  HomogeneousWitnessNodes nodes ->
  BottomSCC (WitnessEdge nodes) root representative_vertex ->
  witness_vertex_node nodes representative_vertex representative ->
  OrderedStrippingFaces (DirectedClosedPeriod representative) faces ->
  List.In (stage, node) (tagged_replacement_nodes blocks) ->
  forall run, DirectedRunMember node run ->
    exists vertex old_node,
      BottomSCC (WitnessEdge nodes) root vertex /\
      witness_vertex_node nodes vertex old_node /\
      DirectedRunMember old_node run.
Proof.
  intros d system nodes root representative_vertex representative excluded
    remaining faces blocks stage node Hhom Hrepresentative
    Hrepresentative_node Hordered Hin run Hrun.
  apply in_tagged_replacement_nodes_iff in Hin as
    [block [Hblock [Hstage Hnode]]].
  subst stage. unfold replacement_block_nodes in Hnode.
  apply in_map_iff in Hnode as [base [Heq Hbase]]. subst node.
  destruct (proj2_sig base) as
    [[member_vertex [member_node [Hmember_bottom
      [Hmember_node Hbase_member]]]] Hbase_slice].
  destruct Hrun as [Hvalid [offset [Hle [Htarget Hface_cone]]]].
  cbn in Hle, Htarget, Hface_cone.
  assert (Hface_of : FaceOf (Cone (DirectedClosedPeriod representative))
      (replacement_face block)).
  { apply (proj1 (proj2 (proj2 Hordered))).
    apply nth_error_In with (n := replacement_stage block).
    exact (replacement_face_at block). }
  assert (Hrepresentative_cone :
      DirectedCone representative (nvec_to_qvec offset)).
  { apply directed_closed_period_cone_included.
    apply (face_subset d (Cone (DirectedClosedPeriod representative))
      (replacement_face block) Hface_of).
    apply (proj2 (replacement_generates block (nvec_to_qvec offset))).
    exact Hface_cone. }
  assert (Hmember_cone : DirectedCone member_node (nvec_to_qvec offset)).
  { apply (proj1 (bottom_scc_common_cone d system nodes root
      representative_vertex representative member_vertex member_node
      Hhom Hrepresentative Hmember_bottom Hrepresentative_node
      Hmember_node (nvec_to_qvec offset))).
    exact Hrepresentative_cone. }
  exists member_vertex, member_node. split; [exact Hmember_bottom|].
  split; [exact Hmember_node|].
  apply (lemma_7_4_directed_irun_rebase_member d system member_node
    (proj1_sig base) Hbase_member run).
  split; [exact Hvalid|]. exists offset. split; [exact Hle|].
  split; [exact Htarget|]. cbn. exact Hmember_cone.
Qed.

Lemma in_replacement_nodes_iff : forall d (system : IBVAS d)
    (nodes : list (DirectedIRun system)) (root : WitnessVertex nodes)
    (representative : DirectedIRun system) excluded remaining faces blocks
    node,
  List.In node
    (@replacement_nodes d system nodes root representative excluded remaining
      faces blocks) <->
  exists stage, List.In (stage, node) (tagged_replacement_nodes blocks).
Proof.
  intros. unfold replacement_nodes, tagged_replacement_nodes. split.
  - intro Hin. apply in_concat in Hin as [component [Hcomponent Hnode]].
    apply in_map_iff in Hcomponent as [block [Heq Hblock]]. subst component.
    exists (replacement_stage block).
    apply in_concat. exists (tagged_replacement_block_nodes block). split.
    + apply in_map_iff. exists block. auto.
    + apply in_map_iff. exists node. auto.
  - intros [stage Hin]. apply in_concat in Hin as
      [component [Hcomponent Hpair]].
    apply in_map_iff in Hcomponent as [block [Heq Hblock]]. subst component.
    apply in_map_iff in Hpair as [found [Heq Hfound]].
    inversion Heq. subst stage found.
    apply in_concat. exists (replacement_block_nodes block). split.
    + apply in_map_iff. exists block. auto.
    + exact Hfound.
Qed.

Lemma witness_vertex_node_in : forall d (system : IBVAS d)
    (nodes : list (DirectedIRun system)) vertex node,
  witness_vertex_node nodes vertex node -> List.In node nodes.
Proof.
  intros d system nodes vertex node Hnode.
  apply nth_error_In with (n := proj1_sig (Fin.to_nat vertex)). exact Hnode.
Qed.

Lemma replacement_edge_stays_new_and_nondecreasing : forall d
    (system : IBVAS d) safe (witness : SafetyWitness system safe)
    root representative_vertex representative offset faces
    (blocks : list (FaceReplacementBlock (witness_nodes witness) root
      representative
      (NSetAsZ (BottomSCCLinearSlice (witness_nodes witness) root representative
        (witness_attractor witness) offset))
      (NSetAsZ (BottomSCCRegion (witness_nodes witness) root representative))
      faces))
    (retained : list (DirectedIRun system))
    source_stage source target,
  BottomSCCRoot (WitnessEdge (witness_nodes witness)) root ->
  BottomSCC (WitnessEdge (witness_nodes witness)) root representative_vertex ->
  witness_vertex_node (witness_nodes witness) representative_vertex
    representative ->
  DirectedOffset representative offset ->
  BottomSCCStrippingPackage (witness_nodes witness) root representative
    (witness_attractor witness) offset faces ->
  (forall node, List.In node retained <->
    RetainedOldNode (witness_nodes witness) root node) ->
  List.In (source_stage, source) (tagged_replacement_nodes blocks) ->
  List.In target (retained ++ replacement_nodes blocks) ->
  DirectedIRunEdge source target ->
  exists target_stage,
    List.In (target_stage, target) (tagged_replacement_nodes blocks) /\
    (source_stage <= target_stage)%nat.
Proof.
  intros d system safe witness root representative_vertex representative
    offset faces blocks retained source_stage source target Hroot
    Hrepresentative Hrepresentative_node Hoffset Hpackage Hretained Hsource
    Htarget Hedge.
  destruct Hpackage as [Hordered [Hhead [Hslices [Hcomplete
    [Hfirst Hdiagonal]]]]].
  destruct (in_app_or _ _ _ Htarget) as [Htarget_old|Htarget_new].
  - exfalso.
    apply Hretained in Htarget_old as
      [target_vertex [Htarget_outside Htarget_node]].
    destruct Hedge as [source_run [target_run
      [Hsource_run [Htarget_run Hoccurrence]]]].
    destruct (replacement_node_embeds_bottom d system
      (witness_nodes witness) root representative_vertex representative
      (NSetAsZ (BottomSCCLinearSlice (witness_nodes witness) root representative
        (witness_attractor witness) offset))
      (NSetAsZ (BottomSCCRegion (witness_nodes witness) root representative))
      faces blocks source_stage source
      (@witness_nodes_homogeneous d system safe witness) Hrepresentative
      Hrepresentative_node Hordered Hsource source_run Hsource_run) as
      [source_vertex [source_old [Hsource_bottom
        [Hsource_old_node Hsource_old_member]]]].
    assert (Hedge_old : WitnessEdge (witness_nodes witness)
        source_vertex target_vertex).
    { exists source_old, target. repeat split; try assumption.
      exists source_run, target_run. auto. }
    apply Htarget_outside.
    eapply bottom_scc_closed; eauto.
  - apply in_replacement_nodes_iff in Htarget_new as
      [target_stage Htarget_tagged].
    exists target_stage. split; [exact Htarget_tagged|].
    eapply lemma_7_5_new_node_edge_direction.
    + intros run Hmember.
      exact (proj1 (proj2 (proj2
        (replacement_node_stage_properties d system
          (witness_nodes witness) root representative_vertex representative
          (NSetAsZ (BottomSCCLinearSlice (witness_nodes witness) root
            representative (witness_attractor witness) offset))
          (NSetAsZ (BottomSCCRegion (witness_nodes witness) root
            representative)) faces blocks source_stage source
          (@witness_nodes_homogeneous d system safe witness) Hroot Hrepresentative
          Hrepresentative_node Hordered Hslices Hsource))) run Hmember).
    + intros run Hmember.
      exact (proj1 (proj2 (proj2
        (replacement_node_stage_properties d system
          (witness_nodes witness) root representative_vertex representative
          (NSetAsZ (BottomSCCLinearSlice (witness_nodes witness) root
            representative (witness_attractor witness) offset))
          (NSetAsZ (BottomSCCRegion (witness_nodes witness) root
            representative)) faces blocks target_stage target
          (@witness_nodes_homogeneous d system safe witness) Hroot Hrepresentative
          Hrepresentative_node Hordered Hslices Htarget_tagged))) run Hmember).
    + exact Hdiagonal.
    + exact (proj1 (proj2
        (replacement_node_stage_properties d system
          (witness_nodes witness) root representative_vertex representative
          (NSetAsZ (BottomSCCLinearSlice (witness_nodes witness) root
            representative (witness_attractor witness) offset))
          (NSetAsZ (BottomSCCRegion (witness_nodes witness) root
            representative)) faces blocks source_stage source
          (@witness_nodes_homogeneous d system safe witness) Hroot Hrepresentative
          Hrepresentative_node Hordered Hslices Hsource))).
    + exact (proj1 (proj2
        (replacement_node_stage_properties d system
          (witness_nodes witness) root representative_vertex representative
          (NSetAsZ (BottomSCCLinearSlice (witness_nodes witness) root
            representative (witness_attractor witness) offset))
          (NSetAsZ (BottomSCCRegion (witness_nodes witness) root
            representative)) faces blocks target_stage target
          (@witness_nodes_homogeneous d system safe witness) Hroot Hrepresentative
          Hrepresentative_node Hordered Hslices Htarget_tagged))).
    + exact Hedge.
Qed.

Lemma replacement_node_stage_unique : forall d (system : IBVAS d)
    (nodes : list (DirectedIRun system)) (root : WitnessVertex nodes)
    (representative : DirectedIRun system) (excluded remaining : ZSet d)
    (faces : list (QSet d))
    (blocks : list (FaceReplacementBlock nodes root representative excluded
      remaining faces))
    first second node,
  OrderedStrippingFaces (DirectedClosedPeriod representative) faces ->
  List.In (first, node) (tagged_replacement_nodes blocks) ->
  List.In (second, node) (tagged_replacement_nodes blocks) ->
  first = second.
Proof.
  intros d system nodes root representative excluded remaining faces blocks
    first second node Hordered Hfirst Hsecond.
  apply in_tagged_replacement_nodes_iff in Hfirst as
    [first_block [Hfirst_block [Hfirst_stage Hfirst_node]]].
  apply in_tagged_replacement_nodes_iff in Hsecond as
    [second_block [Hsecond_block [Hsecond_stage Hsecond_node]]].
  subst first second.
  unfold replacement_block_nodes in Hfirst_node, Hsecond_node.
  apply in_map_iff in Hfirst_node as [first_base [Hfirst_eq Hfirst_base]].
  apply in_map_iff in Hsecond_node as [second_base [Hsecond_eq Hsecond_base]].
  assert (Hgenerator_eq : replacement_generators first_block =
      replacement_generators second_block).
  { pose proof (f_equal (@directed_generators d system)
      (eq_trans Hfirst_eq (eq_sym Hsecond_eq))) as Heq.
    cbn in Heq. exact Heq. }
  assert (Hfaces_same : SameSet (replacement_face first_block)
      (replacement_face second_block)).
  { intro point. rewrite (replacement_generates first_block point),
      (replacement_generates second_block point), Hgenerator_eq.
    reflexivity. }
  destruct (Nat.eq_dec (replacement_stage first_block)
      (replacement_stage second_block)) as [Heq|Hneq]; [exact Heq|].
  exfalso.
  exact ((proj1 (proj2 (proj2 (proj2 (proj2 Hordered)))))
    (replacement_stage first_block) (replacement_stage second_block)
    (replacement_face first_block) (replacement_face second_block)
    (replacement_face_at first_block) (replacement_face_at second_block)
    Hneq Hfaces_same).
Qed.

Lemma replacement_graph_reach_nondecreasing : forall d
    (system : IBVAS d) safe (witness : SafetyWitness system safe)
    root representative_vertex representative offset faces
    (blocks : list (FaceReplacementBlock (witness_nodes witness) root
      representative
      (NSetAsZ (BottomSCCLinearSlice (witness_nodes witness) root representative
        (witness_attractor witness) offset))
      (NSetAsZ (BottomSCCRegion (witness_nodes witness) root representative))
      faces))
    (retained : list (DirectedIRun system))
    source_vertex target_vertex source_node target_node source_stage,
  BottomSCCRoot (WitnessEdge (witness_nodes witness)) root ->
  BottomSCC (WitnessEdge (witness_nodes witness)) root representative_vertex ->
  witness_vertex_node (witness_nodes witness) representative_vertex
    representative ->
  DirectedOffset representative offset ->
  BottomSCCStrippingPackage (witness_nodes witness) root representative
    (witness_attractor witness) offset faces ->
  (forall node, List.In node retained <->
    RetainedOldNode (witness_nodes witness) root node) ->
  witness_vertex_node (retained ++ replacement_nodes blocks)
    source_vertex source_node ->
  witness_vertex_node (retained ++ replacement_nodes blocks)
    target_vertex target_node ->
  List.In (source_stage, source_node) (tagged_replacement_nodes blocks) ->
  GraphReach (WitnessEdge (retained ++ replacement_nodes blocks))
    source_vertex target_vertex ->
  exists target_stage,
    List.In (target_stage, target_node) (tagged_replacement_nodes blocks) /\
    (source_stage <= target_stage)%nat.
Proof.
  intros d system safe witness root representative_vertex representative
    offset faces blocks retained source_vertex target_vertex source_node
    target_node source_stage Hroot Hrepresentative Hrepresentative_node Hoffset
    Hpackage Hretained Hsource_node Htarget_node Hsource Hpath.
  revert target_node Htarget_node source_node source_stage Hsource_node Hsource.
  induction Hpath as [|middle target_vertex Hprefix IH Hedge];
    intros target_node Htarget_node source_node source_stage Hsource_node Hsource.
  - assert (Heq : source_node = target_node).
    { eapply witness_vertex_node_unique; eauto. }
    subst target_node. exists source_stage. auto.
  - destruct Hedge as [middle_node [edge_target
      [Hmiddle_node [Hedge_target Hedge_nodes]]]].
    assert (Htarget_eq : edge_target = target_node).
    { eapply witness_vertex_node_unique; eauto. }
    subst edge_target.
    destruct (witness_vertex_node_exists d system
      (retained ++ replacement_nodes blocks) middle) as
      [prefix_target Hprefix_target].
    destruct (IH prefix_target Hprefix_target source_node source_stage
      Hsource_node Hsource) as
      [middle_stage [Hmiddle_tagged Hstage_le]].
    assert (Hmiddle_eq : middle_node = prefix_target).
    { eapply witness_vertex_node_unique; eauto. }
    subst middle_node.
    destruct (replacement_edge_stays_new_and_nondecreasing d system safe
      witness root representative_vertex representative offset faces blocks
      retained middle_stage prefix_target target_node Hroot Hrepresentative
      Hrepresentative_node Hoffset Hpackage Hretained Hmiddle_tagged
      (witness_vertex_node_in d system
        (retained ++ replacement_nodes blocks) target_vertex target_node
        Htarget_node) Hedge_nodes) as
      [target_stage [Htarget_tagged Hmiddle_target]].
    exists target_stage. split; [exact Htarget_tagged|lia].
Qed.

Lemma replacement_same_stage_cone : forall d (system : IBVAS d)
    (nodes : list (DirectedIRun system)) (root : WitnessVertex nodes)
    (representative : DirectedIRun system) (excluded remaining : ZSet d)
    (faces : list (QSet d))
    (blocks : list (FaceReplacementBlock nodes root representative excluded
      remaining faces))
    stage left right,
  List.In (stage, left) (tagged_replacement_nodes blocks) ->
  List.In (stage, right) (tagged_replacement_nodes blocks) ->
  SameSet (DirectedCone left) (DirectedCone right).
Proof.
  intros d system nodes root representative excluded remaining faces blocks
    stage left right Hleft Hright.
  apply in_tagged_replacement_nodes_iff in Hleft as
    [left_block [Hleft_block [Hleft_stage Hleft_node]]].
  apply in_tagged_replacement_nodes_iff in Hright as
    [right_block [Hright_block [Hright_stage Hright_node]]].
  assert (Hright_stage_eq : replacement_stage right_block =
      replacement_stage left_block) by congruence.
  assert (Hface_eq : replacement_face left_block = replacement_face right_block).
  { pose proof (replacement_face_at left_block) as Hleft_face.
    pose proof (replacement_face_at right_block) as Hright_face.
    rewrite Hright_stage_eq in Hright_face. congruence. }
  unfold replacement_block_nodes in Hleft_node, Hright_node.
  apply in_map_iff in Hleft_node as [left_base [Hleft_eq Hleft_base]].
  apply in_map_iff in Hright_node as [right_base [Hright_eq Hright_base]].
  rewrite <- Hleft_eq, <- Hright_eq. intro point. cbn.
  rewrite <- (replacement_generates left_block point),
    <- (replacement_generates right_block point).
  now rewrite Hface_eq.
Qed.

Lemma retained_graph_reach_transfer : forall d (system : IBVAS d) safe
    (witness : SafetyWitness system safe) root representative_vertex
    representative offset faces
    (blocks : list (FaceReplacementBlock (witness_nodes witness) root
      representative
      (NSetAsZ (BottomSCCLinearSlice (witness_nodes witness) root representative
        (witness_attractor witness) offset))
      (NSetAsZ (BottomSCCRegion (witness_nodes witness) root representative))
      faces))
    (retained : list (DirectedIRun system)) source_vertex target_vertex
    source_node target_node old_source old_target,
  BottomSCCRoot (WitnessEdge (witness_nodes witness)) root ->
  BottomSCC (WitnessEdge (witness_nodes witness)) root representative_vertex ->
  witness_vertex_node (witness_nodes witness) representative_vertex
    representative ->
  DirectedOffset representative offset ->
  BottomSCCStrippingPackage (witness_nodes witness) root representative
    (witness_attractor witness) offset faces ->
  (forall node, List.In node retained <->
    RetainedOldNode (witness_nodes witness) root node) ->
  witness_vertex_node (retained ++ replacement_nodes blocks)
    source_vertex source_node ->
  witness_vertex_node (retained ++ replacement_nodes blocks)
    target_vertex target_node ->
  List.In source_node retained ->
  List.In target_node retained ->
  ~ List.In source_node (replacement_nodes blocks) ->
  ~ List.In target_node (replacement_nodes blocks) ->
  witness_vertex_node (witness_nodes witness) old_source source_node ->
  witness_vertex_node (witness_nodes witness) old_target target_node ->
  GraphReach (WitnessEdge (retained ++ replacement_nodes blocks))
    source_vertex target_vertex ->
  source_node = target_node \/
  GraphReach (WitnessEdge (witness_nodes witness)) old_source old_target.
Proof.
  intros d system safe witness root representative_vertex representative
    offset faces blocks retained source_vertex target_vertex source_node
    target_node old_source old_target Hroot Hrepresentative Hrepresentative_node Hoffset Hpackage
    Hretained Hsource_node Htarget_node Hsource_old Htarget_old
    Hsource_notnew Htarget_notnew Hold_source Hold_target Hpath.
  revert target_node old_target Htarget_node Htarget_old Htarget_notnew Hold_target.
  refine (@GraphReach_ind _
    (WitnessEdge (retained ++ replacement_nodes blocks)) source_vertex
    (fun target_vertex => forall target_node old_target,
      witness_vertex_node (retained ++ replacement_nodes blocks)
        target_vertex target_node ->
      List.In target_node retained ->
      ~ List.In target_node (replacement_nodes blocks) ->
      witness_vertex_node (witness_nodes witness) old_target target_node ->
      source_node = target_node \/
      GraphReach (WitnessEdge (witness_nodes witness)) old_source old_target)
    (fun target_node old_target Htarget_node _ _ _ =>
      or_introl (witness_vertex_node_unique d system
        (retained ++ replacement_nodes blocks) source_vertex source_node
        target_node Hsource_node Htarget_node))
    (fun middle next_vertex Hprefix IHstep Hstep => _)
    target_vertex Hpath).
  intros next_node next_old
      Hnext_node Hnext_old Hnext_notnew Hold_next.
    destruct Hstep as [middle_node [edge_target
      [Hmiddle_node [Hedge_target Hedge_nodes]]]].
    assert (Htarget_eq : edge_target = next_node).
    { eapply witness_vertex_node_unique; eauto. }
    subst edge_target.
    assert (Hmiddle_in : List.In middle_node
        (retained ++ replacement_nodes blocks)).
    { eapply witness_vertex_node_in; eauto. }
    assert (Hmiddle_notnew : ~ List.In middle_node (replacement_nodes blocks)).
    { intro Hmiddle_new.
      apply in_replacement_nodes_iff in Hmiddle_new as
        [middle_stage Hmiddle_tagged].
      destruct (replacement_edge_stays_new_and_nondecreasing d system safe
        witness root representative_vertex representative offset faces blocks
        retained middle_stage middle_node next_node Hroot Hrepresentative
        Hrepresentative_node Hoffset Hpackage Hretained Hmiddle_tagged
        (in_or_app _ _ _ (or_introl Hnext_old)) Hedge_nodes) as
        [target_stage [Htarget_tagged _]].
      apply Hnext_notnew, in_replacement_nodes_iff.
      now exists target_stage. }
    assert (Hmiddle_old : List.In middle_node retained).
    { apply in_app_or in Hmiddle_in as [H|H]; [exact H|contradiction]. }
    destruct (proj1 (Hretained middle_node) Hmiddle_old) as
      [old_middle [Hmiddle_outside Hold_middle]].
    destruct (IHstep middle_node old_middle Hmiddle_node
      Hmiddle_old Hmiddle_notnew Hold_middle) as
      [Heq|Hold_path].
  - subst middle_node.
    right.
    apply graph_reach_edge. exists source_node, next_node. auto.
  - right.
    eapply graph_reach_step; [exact Hold_path|].
    exists middle_node, next_node. auto.
Qed.

Theorem replacement_nodes_homogeneous : forall d (system : IBVAS d) safe
    (witness : SafetyWitness system safe) root representative_vertex
    representative offset faces
    (blocks : list (FaceReplacementBlock (witness_nodes witness) root
      representative
      (NSetAsZ (BottomSCCLinearSlice (witness_nodes witness) root representative
        (witness_attractor witness) offset))
      (NSetAsZ (BottomSCCRegion (witness_nodes witness) root representative))
      faces)) retained,
  BottomSCCRoot (WitnessEdge (witness_nodes witness)) root ->
  BottomSCC (WitnessEdge (witness_nodes witness)) root representative_vertex ->
  witness_vertex_node (witness_nodes witness) representative_vertex
    representative ->
  DirectedOffset representative offset ->
  BottomSCCStrippingPackage (witness_nodes witness) root representative
    (witness_attractor witness) offset faces ->
  (forall node, List.In node retained <->
    RetainedOldNode (witness_nodes witness) root node) ->
  HomogeneousWitnessNodes (retained ++ replacement_nodes blocks).
Proof.
  intros d system safe witness root representative_vertex representative
    offset faces blocks retained Hroot Hrepresentative Hrepresentative_node
    Hoffset Hpackage Hretained left_vertex right_vertex left_node right_node
    [Hleft_right Hright_left] Hleft_node Hright_node.
  assert (Hleft_in : List.In left_node
      (retained ++ replacement_nodes blocks))
    by exact (witness_vertex_node_in d system
      (retained ++ replacement_nodes blocks) left_vertex left_node Hleft_node).
  assert (Hright_in : List.In right_node
      (retained ++ replacement_nodes blocks))
    by exact (witness_vertex_node_in d system
      (retained ++ replacement_nodes blocks) right_vertex right_node Hright_node).
  destruct (classic (List.In left_node (replacement_nodes blocks))) as
    [Hleft_new|Hleft_notnew].
  - apply in_replacement_nodes_iff in Hleft_new as
      [left_stage Hleft_tagged].
    destruct (replacement_graph_reach_nondecreasing d system safe witness
      root representative_vertex representative offset faces blocks retained
      left_vertex right_vertex left_node right_node left_stage Hroot
      Hrepresentative Hrepresentative_node Hoffset Hpackage Hretained
      Hleft_node Hright_node Hleft_tagged Hleft_right) as
      [right_stage [Hright_tagged Hle]].
    destruct (replacement_graph_reach_nondecreasing d system safe witness
      root representative_vertex representative offset faces blocks retained
      right_vertex left_vertex right_node left_node right_stage Hroot
      Hrepresentative Hrepresentative_node Hoffset Hpackage Hretained
      Hright_node Hleft_node Hright_tagged Hright_left) as
      [left_stage' [Hleft_tagged' Hge]].
    assert (Hstage_unique : left_stage' = left_stage).
    { eapply replacement_node_stage_unique; eauto.
      exact (proj1 Hpackage). }
    subst left_stage'. assert (Hstage : left_stage = right_stage) by lia.
    subst right_stage.
    eapply replacement_same_stage_cone; eauto.
  - assert (Hleft_old : List.In left_node retained).
    { apply in_app_or in Hleft_in as [H|H]; [exact H|contradiction]. }
    assert (Hright_notnew : ~ List.In right_node (replacement_nodes blocks)).
    { intro Hright_new. apply in_replacement_nodes_iff in Hright_new as
        [right_stage Hright_tagged].
      destruct (replacement_graph_reach_nondecreasing d system safe witness
        root representative_vertex representative offset faces blocks retained
        right_vertex left_vertex right_node left_node right_stage Hroot
        Hrepresentative Hrepresentative_node Hoffset Hpackage Hretained
        Hright_node Hleft_node Hright_tagged Hright_left) as
        [left_stage [Hleft_tagged _]].
      apply Hleft_notnew, in_replacement_nodes_iff. now exists left_stage. }
    assert (Hright_old : List.In right_node retained).
    { apply in_app_or in Hright_in as [H|H]; [exact H|contradiction]. }
    destruct (classic (left_node = right_node)) as [Heq|Hneq].
    + subst right_node. intro point. reflexivity.
    + destruct (proj1 (Hretained left_node) Hleft_old) as
        [old_left [Hleft_outside Hold_left]].
      destruct (proj1 (Hretained right_node) Hright_old) as
        [old_right [Hright_outside Hold_right]].
      destruct (retained_graph_reach_transfer d system safe witness root
        representative_vertex representative offset faces blocks retained
        left_vertex right_vertex left_node right_node old_left old_right
        Hroot Hrepresentative
        Hrepresentative_node Hoffset Hpackage Hretained Hleft_node Hright_node
        Hleft_old Hright_old Hleft_notnew Hright_notnew Hold_left Hold_right
        Hleft_right) as [Heq|Hold_lr]; [contradiction|].
      destruct (retained_graph_reach_transfer d system safe witness root
        representative_vertex representative offset faces blocks retained
        right_vertex left_vertex right_node left_node old_right old_left
        Hroot Hrepresentative
        Hrepresentative_node Hoffset Hpackage Hretained Hright_node Hleft_node
        Hright_old Hleft_old Hright_notnew Hleft_notnew Hold_right Hold_left
        Hright_left) as [Heq|Hold_rl]; [symmetry in Heq; contradiction|].
      eapply (@witness_nodes_homogeneous d system safe witness old_left
        old_right left_node right_node).
      * split; [exact Hold_lr|exact Hold_rl].
      * exact Hold_left.
      * exact Hold_right.
Qed.

Theorem replacement_nodes_run_coverage : forall d (system : IBVAS d) safe
    (witness : SafetyWitness system safe) root representative_vertex
    representative offset faces
    (blocks : list (FaceReplacementBlock (witness_nodes witness) root
      representative
      (NSetAsZ (BottomSCCLinearSlice (witness_nodes witness) root representative
        (witness_attractor witness) offset))
      (NSetAsZ (BottomSCCRegion (witness_nodes witness) root representative))
      faces)) retained,
  BottomSCCRoot (WitnessEdge (witness_nodes witness)) root ->
  BottomSCC (WitnessEdge (witness_nodes witness)) root representative_vertex ->
  witness_vertex_node (witness_nodes witness) representative_vertex
    representative ->
  DirectedOffset representative offset ->
  BottomSCCStrippingPackage (witness_nodes witness) root representative
    (witness_attractor witness) offset faces ->
  (forall stage, (0 < stage)%nat -> (stage < length faces)%nat ->
    exists block, List.In block blocks /\ replacement_stage block = stage) ->
  (forall node, List.In node retained <->
    RetainedOldNode (witness_nodes witness) root node) ->
  forall run, ValidIRun system run ->
    BottomSCCExtendedAttractor (witness_nodes witness) root representative
      (witness_attractor witness) offset (irun_target run) \/
    exists node,
      List.In node (retained ++ replacement_nodes blocks) /\
      DirectedRunMember node run.
Proof.
  intros d system safe witness root representative_vertex representative
    offset faces blocks retained Hroot Hrepresentative Hrepresentative_node
    Hoffset Hpackage Hblocks Hretained run Hvalid.
  destruct (@witness_run_coverage d system safe witness run Hvalid) as
    [Hattractor|[old_node [Hold_in Hold_member]]].
  - left. now left.
  - destruct (old_node_bottom_or_retained d system (witness_nodes witness)
      root old_node Hold_in) as
      [[old_vertex [Hold_bottom Hold_vertex]]|Hold_retained].
    2:{ right. exists old_node. split; [apply in_or_app; left;
          apply (proj2 (Hretained old_node)); exact Hold_retained|exact Hold_member]. }
    assert (Hregion : BottomSCCRegion (witness_nodes witness) root
        representative (irun_target run)).
    { exact (bottom_scc_member_targets_region d system (witness_nodes witness)
        root representative_vertex representative old_vertex old_node run
        (@witness_nodes_homogeneous d system safe witness) Hroot
        Hrepresentative Hold_bottom Hrepresentative_node Hold_vertex
        Hold_member). }
    destruct (classic (BottomSCCLinearSlice (witness_nodes witness) root
      representative (witness_attractor witness) offset (irun_target run)))
      as [Hslice|Hnot_slice].
    - left. now right.
    - destruct Hpackage as [Hordered [Hhead [Hslices [Hcomplete
        [Hfirst Hdiagonal]]]]].
      assert (Hregion_z : NSetAsZ
          (BottomSCCRegion (witness_nodes witness) root representative)
          (nvec_to_zvec (irun_target run))).
      { exists (irun_target run). auto. }
      assert (Hnot_slice_z : ~ NSetAsZ
          (BottomSCCLinearSlice (witness_nodes witness) root representative
            (witness_attractor witness) offset)
          (nvec_to_zvec (irun_target run))).
      { intros [natural [Heq Hnatural]]. apply Hnot_slice.
        apply nvec_to_zvec_injective_update in Heq. now subst natural. }
      destruct (proj1 (Hcomplete (nvec_to_zvec (irun_target run)))
        (conj Hregion_z Hnot_slice_z)) as
        [stage [Hstage Hstage_slice]].
      assert (Hpositive : (0 < stage)%nat).
      { destruct stage; [exfalso; exact (Hfirst _ Hstage_slice)|lia]. }
      assert (Hresidual : ResidualRun (witness_nodes witness) root
          (DirectedClosedPeriod representative)
          (NSetAsZ (BottomSCCLinearSlice (witness_nodes witness) root
            representative (witness_attractor witness) offset))
          (NSetAsZ (BottomSCCRegion (witness_nodes witness) root representative))
          faces stage run).
      { split.
        - exists old_vertex, old_node. split; [exact Hold_bottom|].
          split; [exact Hold_vertex|exact Hold_member].
        - exact Hstage_slice. }
      destruct (replacement_blocks_cover d system (witness_nodes witness) root
        representative
        (NSetAsZ (BottomSCCLinearSlice (witness_nodes witness) root
          representative (witness_attractor witness) offset))
        (NSetAsZ (BottomSCCRegion (witness_nodes witness) root representative))
        faces blocks Hblocks stage run Hpositive Hstage Hresidual) as
        [new_node [Hnew_in Hnew_member]].
      right. exists new_node. split.
      + apply in_or_app. right. apply in_replacement_nodes_iff.
        now exists stage.
      + exact Hnew_member.
Qed.

Fixpoint witness_node_at {d} {system : IBVAS d}
    (nodes : list (DirectedIRun system)) :
    WitnessVertex nodes -> DirectedIRun system :=
  match nodes as actual return WitnessVertex actual -> DirectedIRun system with
  | [] => fun vertex => Fin.case0 (fun _ => DirectedIRun system) vertex
  | head :: tail => fun vertex =>
      Fin.caseS' vertex (fun _ => DirectedIRun system) head
        (fun tail_vertex => witness_node_at tail tail_vertex)
  end.

Lemma fin_to_nat_fs_value : forall count (vertex : Fin.t count),
  proj1_sig (Fin.to_nat (Fin.FS vertex)) =
    S (proj1_sig (Fin.to_nat vertex)).
Proof.
  intros count vertex. cbn [Fin.to_nat].
  destruct (Fin.to_nat vertex). reflexivity.
Qed.

Lemma witness_node_at_spec : forall d (system : IBVAS d)
    (nodes : list (DirectedIRun system)) vertex,
  witness_vertex_node nodes vertex (witness_node_at nodes vertex).
Proof.
  intros d system. fix IH 1. intros nodes vertex.
  destruct nodes as [|head tail].
  - inversion vertex.
  - refine (Fin.caseS' vertex (fun index =>
      witness_vertex_node (head :: tail) index
        (witness_node_at (head :: tail) index)) _ _).
    + reflexivity.
    + intro tail_vertex. unfold witness_vertex_node.
      cbn [Fin.to_nat].
      destruct (Fin.to_nat tail_vertex) as [index Hindex] eqn:Hnat. cbn.
      pose proof (IH tail tail_vertex) as Htail.
      unfold witness_vertex_node in Htail.
      assert (Hvalue : proj1_sig (Fin.to_nat tail_vertex) = index).
      { rewrite Hnat. reflexivity. }
      rewrite <- Hvalue.
      exact Htail.
Qed.

Lemma map_witness_node_at_finite_vertices : forall d (system : IBVAS d)
    (nodes : list (DirectedIRun system)),
  List.map (witness_node_at nodes) (finite_vertices (length nodes)) = nodes.
Proof.
  intros d system nodes. induction nodes as [|head tail IH]; [reflexivity|].
  cbn. f_equal. rewrite List.map_map.
  change (List.map (witness_node_at tail)
    (finite_vertices (length tail)) = tail).
  exact IH.
Qed.

Lemma finite_predicate_partition_map : forall A B (items : list A)
    (predicate : A -> Prop) (f : A -> B),
  exists yes no : list B,
    Permutation (List.map f items) (yes ++ no) /\
    (forall value, List.In value yes <->
      exists item, List.In item items /\ predicate item /\ f item = value) /\
    (forall value, List.In value no <->
      exists item, List.In item items /\ ~ predicate item /\ f item = value).
Proof.
  intros A B items. induction items as [|item items IH]; intros predicate f.
  - exists [], []. split; [constructor|]. split.
    + intro value. split; intro H.
      * inversion H.
      * destruct H as [found [Hfound _]]. inversion Hfound.
    + intro value. split; intro H.
      * inversion H.
      * destruct H as [found [Hfound _]]. inversion Hfound.
  - destruct (IH predicate f) as [yes [no [Hperm [Hyes Hno]]]].
    destruct (classic (predicate item)) as [Hitem|Hitem].
    + exists (f item :: yes), no. split.
      * cbn. now apply perm_skip.
      * split.
        -- intro value. cbn. rewrite Hyes. firstorder congruence.
        -- intro value. rewrite Hno. firstorder congruence.
    + exists yes, (f item :: no). split.
      * cbn. eapply Permutation_trans; [apply perm_skip; exact Hperm|].
        apply Permutation_middle.
      * split.
        -- intro value. rewrite Hyes. firstorder congruence.
        -- intro value. cbn. rewrite Hno. firstorder congruence.
Qed.

Theorem bottom_scc_occurrence_partition : forall d (system : IBVAS d)
    (nodes : list (DirectedIRun system)) root,
  exists bottom retained : list (DirectedIRun system),
    Permutation nodes (bottom ++ retained) /\
    (forall node, List.In node bottom <->
      exists vertex, BottomSCC (WitnessEdge nodes) root vertex /\
        witness_vertex_node nodes vertex node) /\
    (forall node, List.In node retained <-> RetainedOldNode nodes root node).
Proof.
  intros d system nodes root.
  destruct (finite_predicate_partition_map (WitnessVertex nodes)
    (DirectedIRun system) (finite_vertices (length nodes))
    (BottomSCC (WitnessEdge nodes) root) (witness_node_at nodes)) as
    [bottom [retained [Hperm [Hbottom Hretained]]]].
  exists bottom, retained. split.
  - eapply (Permutation_trans
      (l' := List.map (witness_node_at nodes)
        (finite_vertices (length nodes)))).
    + rewrite map_witness_node_at_finite_vertices. apply Permutation_refl.
    + exact Hperm.
  - split; intro node.
    + rewrite Hbottom. split.
      * intros [vertex [Hin [Hbottom_vertex Hnode]]].
        exists vertex. split; [exact Hbottom_vertex|].
        subst node. apply witness_node_at_spec.
      * intros [vertex [Hbottom_vertex Hnode]].
        exists vertex. split; [apply finite_vertices_complete|]. split;
          [exact Hbottom_vertex|].
        eapply witness_vertex_node_unique; [apply witness_node_at_spec|eauto].
    + rewrite Hretained. unfold RetainedOldNode. split.
      * intros [vertex [Hin [Houtside Hnode]]]. exists vertex. split.
        -- exact Houtside.
        -- subst node. apply witness_node_at_spec.
      * intros [vertex [Houtside Hnode]]. exists vertex.
        split; [apply finite_vertices_complete|]. split; [exact Houtside|].
        eapply witness_vertex_node_unique; [apply witness_node_at_spec|eauto].
Qed.

Lemma nodes_at_rank_permutation_update : forall d (system : IBVAS d)
    rank (left right : list (DirectedIRun system)),
  Permutation left right ->
  nodes_at_rank rank left = nodes_at_rank rank right.
Proof.
  intros d system rank left right Hperm. unfold nodes_at_rank.
  apply (proj1 (Permutation_count_occ Nat.eq_dec _ _)).
  now apply Permutation_map.
Qed.

Lemma nodes_at_rank_forall_eq : forall d (system : IBVAS d) rank
    (nodes : list (DirectedIRun system)),
  List.Forall (fun node => directed_irun_rank node = rank) nodes ->
  nodes_at_rank rank nodes = length nodes.
Proof.
  intros d system rank nodes Hnodes. induction Hnodes as [|node nodes Hnode Hnodes IH].
  - reflexivity.
  - unfold nodes_at_rank in *. cbn. destruct (Nat.eq_dec
      (directed_irun_rank node) rank); [now rewrite IH|congruence].
Qed.

Lemma nodes_at_rank_forall_neq_zero : forall d (system : IBVAS d) rank
    (nodes : list (DirectedIRun system)),
  List.Forall (fun node => directed_irun_rank node <> rank) nodes ->
  nodes_at_rank rank nodes = 0%nat.
Proof.
  intros d system rank nodes Hnodes. induction Hnodes as [|node nodes Hnode Hnodes IH].
  - reflexivity.
  - unfold nodes_at_rank in *. cbn. destruct (Nat.eq_dec
      (directed_irun_rank node) rank); [contradiction|exact IH].
Qed.

Lemma witness_rank_tuple_less_at_dimension : forall dimension d
    (system : IBVAS d) rank (next previous : list (DirectedIRun system)),
  (rank <= dimension)%nat ->
  (nodes_at_rank rank next < nodes_at_rank rank previous)%nat ->
  (forall higher, (rank < higher <= dimension)%nat ->
    nodes_at_rank higher next = nodes_at_rank higher previous) ->
  high_rank_less dimension (witness_rank_tuple dimension next)
    (witness_rank_tuple dimension previous).
Proof.
  induction dimension as [|dimension IH]; intros d system rank next previous
    Hbound Hstrict Hhigher.
  - assert (rank = 0)%nat by lia. subst rank. exact Hstrict.
  - cbn. destruct (Nat.eq_dec rank (S dimension)) as [Heq|Hneq].
    + subst rank. apply Coq.Relations.Relation_Operators.left_slex.
      exact Hstrict.
    + assert (Htop : nodes_at_rank (S dimension) next =
          nodes_at_rank (S dimension) previous) by (apply Hhigher; lia).
      rewrite Htop.
      apply Coq.Relations.Relation_Operators.right_slex.
      apply (IH d system rank next previous); try lia.
      intros higher Hrange. apply Hhigher. lia.
Qed.

Lemma witness_rank_tuple_less_at : forall d (system : IBVAS d)
    rank (next previous : list (DirectedIRun system)),
  (rank <= d)%nat ->
  (nodes_at_rank rank next < nodes_at_rank rank previous)%nat ->
  (forall higher, (rank < higher <= d)%nat ->
    nodes_at_rank higher next = nodes_at_rank higher previous) ->
  WitnessRankLess next previous.
Proof.
  intros d system rank next previous Hbound Hstrict Hhigher.
  exact (witness_rank_tuple_less_at_dimension d d system rank next previous
    Hbound Hstrict Hhigher).
Qed.

Lemma forall_rank_eq_neq : forall d (system : IBVAS d) rank higher
    (nodes : list (DirectedIRun system)),
  rank <> higher ->
  List.Forall (fun node => directed_irun_rank node = rank) nodes ->
  List.Forall (fun node => directed_irun_rank node <> higher) nodes.
Proof.
  intros d system rank higher nodes Hneq Hnodes.
  induction Hnodes as [|node nodes Hnode Hnodes IH]; constructor; auto.
  now rewrite Hnode.
Qed.

Lemma forall_rank_lt_neq : forall d (system : IBVAS d) rank higher
    (nodes : list (DirectedIRun system)),
  (rank < higher)%nat ->
  List.Forall (fun node => (directed_irun_rank node < rank)%nat) nodes ->
  List.Forall (fun node => directed_irun_rank node <> higher) nodes.
Proof.
  intros d system rank higher nodes Hlt Hnodes.
  induction Hnodes as [|node nodes Hnode Hnodes IH]; constructor; auto.
  exact (Nat.lt_neq _ _ (Nat.lt_trans _ _ _ Hnode Hlt)).
Qed.

Lemma bottom_replacement_rank_decreases : forall d (system : IBVAS d)
    (previous bottom retained replacement : list (DirectedIRun system)) rank,
  Permutation previous (bottom ++ retained) ->
  bottom <> [] ->
  List.Forall (fun node => directed_irun_rank node = rank) bottom ->
  List.Forall (fun node => (directed_irun_rank node < rank)%nat) replacement ->
  (rank <= d)%nat ->
  WitnessRankLess (retained ++ replacement) previous.
Proof.
  intros d system previous bottom retained replacement rank Hperm Hbottom_nonempty
    Hbottom_rank Hreplacement_rank Hrank_bound.
  apply (witness_rank_tuple_less_at d system rank).
  - exact Hrank_bound.
  - rewrite nodes_at_rank_app.
    rewrite (nodes_at_rank_permutation_update d system rank previous
      (bottom ++ retained) Hperm).
    rewrite nodes_at_rank_app.
    rewrite (nodes_at_rank_forall_eq d system rank bottom Hbottom_rank).
    assert (Hreplacement_zero : nodes_at_rank rank replacement = 0%nat).
    { apply nodes_at_rank_forall_neq_zero.
      eapply List.Forall_impl; [|exact Hreplacement_rank].
      intros node Hlt. exact (Nat.lt_neq _ _ Hlt). }
    rewrite Hreplacement_zero.
    assert (Hbottom_length : (0 < length bottom)%nat).
    { destruct bottom; [contradiction|cbn; lia]. }
    rewrite Nat.add_0_r. exact (Nat.lt_add_pos_l _ _ Hbottom_length).
  - intros higher [Hrank_higher Hhigher_bound].
    rewrite nodes_at_rank_app.
    rewrite (nodes_at_rank_permutation_update d system higher previous
      (bottom ++ retained) Hperm).
    rewrite nodes_at_rank_app.
    assert (Hbottom_zero : nodes_at_rank higher bottom = 0%nat).
    { apply nodes_at_rank_forall_neq_zero.
      eapply forall_rank_eq_neq; [|exact Hbottom_rank].
      exact (Nat.lt_neq _ _ Hrank_higher). }
    assert (Hreplacement_zero : nodes_at_rank higher replacement = 0%nat).
    { apply nodes_at_rank_forall_neq_zero.
      eapply forall_rank_lt_neq; eauto. }
    now rewrite Hbottom_zero, Hreplacement_zero, Nat.add_0_l, Nat.add_0_r.
Qed.

(** The face decomposition and the safe attractor extension must use the
    same safe-linearization offset.  Keeping the facts in one existential
    package prevents an invalid recombination of two independently chosen
    offsets. *)
Theorem bottom_scc_face_stripping_with_extension : forall d
    (system : IBVAS d) safe (witness : SafetyWitness system safe)
    root representative representative_node,
  BottomSCCRoot (WitnessEdge (witness_nodes witness)) root ->
  BottomSCC (WitnessEdge (witness_nodes witness)) root representative ->
  witness_vertex_node (witness_nodes witness) representative
    representative_node ->
  exists offset faces,
    DirectedOffset representative_node offset /\
    Semilinear (BottomSCCExtendedAttractor (witness_nodes witness) root
      representative_node (witness_attractor witness) offset) /\
    Attractor system (BottomSCCExtendedAttractor (witness_nodes witness) root
      representative_node (witness_attractor witness) offset) /\
    (forall value,
      BottomSCCExtendedAttractor (witness_nodes witness) root
        representative_node (witness_attractor witness) offset value ->
      safe value) /\
    BottomSCCStrippingPackage (witness_nodes witness) root
      representative_node (witness_attractor witness) offset faces.
Proof.
  intros d system safe witness root representative representative_node
    Hroot Hrepresentative Hrepresentative_node.
  destruct (bottom_scc_safe_extension d system safe witness root
    representative representative_node Hroot Hrepresentative
    Hrepresentative_node) as
    [offset [Hoffset [Hsafe [Hsemilinear [Hattractor [Hsafe_ext
      [Hfinite_slice Hback]]]]]]].
  assert (Hperiodic : Periodic (DirectedClosedPeriod representative_node)).
  { apply closed_linearization_periodic.
    apply periodic_nset_as_z, directed_offset_periodic. }
  assert (Hfinite : FinitelyGeneratedPeriodic
      (DirectedClosedPeriod representative_node)).
  { apply lemma_3_12_directed_closed_period_finitely_generated. }
  assert (Hfull : FullPeriodic (DirectedClosedPeriod representative_node)).
  { apply closed_linearization_full.
    apply periodic_nset_as_z, directed_offset_periodic. }
  assert (Hsubset : forall integer,
      NSetAsZ (BottomSCCLinearSlice (witness_nodes witness) root
        representative_node (witness_attractor witness) offset) integer ->
      NSetAsZ (BottomSCCRegion (witness_nodes witness) root
        representative_node) integer).
  { intros integer [natural [-> [_ HY]]]. exists natural. auto. }
  assert (HbackZ : BackwardPeriodCover
      (DirectedClosedPeriod representative_node)
      (NSetAsZ (BottomSCCLinearSlice (witness_nodes witness) root
        representative_node (witness_attractor witness) offset))
      (NSetAsZ (BottomSCCRegion (witness_nodes witness) root
        representative_node))).
  { intros integer [natural [-> HY]].
    destruct (Hback natural HY) as [increment [Hincrement HX]].
    exists (nvec_to_zvec increment). split; [exact Hincrement|].
    exists (nvec_add natural increment). split.
    - now rewrite nvec_to_zvec_add.
    - exact HX. }
  destruct (face_stripping_theorem_diagonal d
    (DirectedClosedPeriod representative_node)
    (NSetAsZ (BottomSCCLinearSlice (witness_nodes witness) root
      representative_node (witness_attractor witness) offset))
    (NSetAsZ (BottomSCCRegion (witness_nodes witness) root
      representative_node))
    (SpecialLeafRelationZ system)
    Hperiodic Hfinite Hfull Hfinite_slice
    (bottom_scc_region_z_finitary d system (witness_nodes witness) root
      representative_node) Hsubset
    (special_leaf_relation_z_diagonal d system representative_node)
    (bottom_scc_linear_slice_no_boundary d system (witness_nodes witness)
      root representative_node (witness_attractor witness) offset
      (bottom_scc_linear_reach_attractor d system
        (witness_attractor witness) representative_node offset
        (bottom_scc_invariant_inductive d system (witness_attractor witness)
          (witness_attractor_closed system safe witness)))))
    as [faces [Hstrip Hdiagonal]].
  exists offset, faces. split; [exact Hoffset|].
  split; [exact Hsemilinear|]. split; [exact Hattractor|].
  split; [exact Hsafe_ext|].
  unfold BottomSCCStrippingPackage.
  destruct Hstrip as [Hordered [Hhead [Hinitial [Hfinal
    [Hremainders [Hslices [Hdisjoint [Hcomplete Hfirst]]]]]]]].
  split; [exact Hordered|]. split; [exact Hhead|]. split.
  - intros stage face Hstage Hface.
    exact (proj1 (Hslices stage face Hstage Hface)).
  - split; [exact Hcomplete|]. split.
    + exact (Hfirst HbackZ).
    + exact Hdiagonal.
Qed.

Lemma bottom_partition_same_rank : forall d (system : IBVAS d) safe
    (witness : SafetyWitness system safe) root representative_vertex
    representative bottom,
  BottomSCC (WitnessEdge (witness_nodes witness)) root representative_vertex ->
  witness_vertex_node (witness_nodes witness) representative_vertex
    representative ->
  (forall node, List.In node bottom <->
    exists vertex, BottomSCC (WitnessEdge (witness_nodes witness)) root vertex /\
      witness_vertex_node (witness_nodes witness) vertex node) ->
  List.Forall (fun node =>
    directed_irun_rank node = directed_irun_rank representative) bottom.
Proof.
  intros d system safe witness root representative_vertex representative bottom
    Hrepresentative Hrepresentative_node Hbottom.
  apply List.Forall_forall. intros node Hnode.
  destruct (proj1 (Hbottom node) Hnode) as
    [vertex [Hvertex_bottom Hvertex_node]].
  destruct Hrepresentative as
    [[Hroot_rep Hrep_root] Hroot_bottom].
  destruct Hvertex_bottom as
    [[Hroot_vertex Hvertex_root] Hroot_bottom_copy].
  assert (Hscc : SameSCC (WitnessEdge (witness_nodes witness))
      representative_vertex vertex).
  { split.
    - eapply graph_reach_trans; [exact Hrep_root|exact Hroot_vertex].
    - eapply graph_reach_trans; [exact Hvertex_root|exact Hroot_rep]. }
  pose proof (@witness_nodes_homogeneous d system safe witness
    representative_vertex vertex representative node Hscc
    Hrepresentative_node Hvertex_node) as Hcones.
  symmetry. eapply span_dimension_same_set.
  - exact Hcones.
  - apply directed_irun_rank_span.
  - apply directed_irun_rank_span.
Qed.

Lemma replacement_nodes_lower_rank : forall d (system : IBVAS d) safe
    (witness : SafetyWitness system safe) root representative_vertex
    representative offset faces
    (blocks : list (FaceReplacementBlock (witness_nodes witness) root
      representative
      (NSetAsZ (BottomSCCLinearSlice (witness_nodes witness) root representative
        (witness_attractor witness) offset))
      (NSetAsZ (BottomSCCRegion (witness_nodes witness) root representative))
      faces)),
  BottomSCCRoot (WitnessEdge (witness_nodes witness)) root ->
  BottomSCC (WitnessEdge (witness_nodes witness)) root representative_vertex ->
  witness_vertex_node (witness_nodes witness) representative_vertex
    representative ->
  BottomSCCStrippingPackage (witness_nodes witness) root representative
    (witness_attractor witness) offset faces ->
  List.Forall (fun node =>
    (directed_irun_rank node < directed_irun_rank representative)%nat)
    (replacement_nodes blocks).
Proof.
  intros d system safe witness root representative_vertex representative offset
    faces blocks Hroot Hrepresentative Hrepresentative_node Hpackage.
  apply List.Forall_forall. intros node Hnode.
  apply in_replacement_nodes_iff in Hnode as [stage Htagged].
  destruct Hpackage as [Hordered [Hhead [Hslices [Hcomplete
    [Hfirst Hdiagonal]]]]].
  exact (proj2 (proj2 (proj2
    (replacement_node_stage_properties d system (witness_nodes witness) root
      representative_vertex representative
      (NSetAsZ (BottomSCCLinearSlice (witness_nodes witness) root representative
        (witness_attractor witness) offset))
      (NSetAsZ (BottomSCCRegion (witness_nodes witness) root representative))
      faces blocks stage node (@witness_nodes_homogeneous d system safe witness)
      Hroot Hrepresentative Hrepresentative_node Hordered Hslices Htagged)))).
Qed.

Theorem lemma_7_1_safety_witness_rank_descent :
  forall d (system : IBVAS d) (safe : NSet d)
    (witness : SafetyWitness system safe),
    witness_nodes witness <> [] ->
    exists next : SafetyWitness system safe,
      WitnessRankLess (witness_nodes next) (witness_nodes witness).
Proof.
  intros d system safe witness Hnodes_nonempty.
  destruct (safety_witness_bottom_scc_exists d system safe witness
    Hnodes_nonempty) as [root Hroot].
  assert (Hroot_bottom : BottomSCC (WitnessEdge (witness_nodes witness))
      root root) by (apply bottom_scc_nonempty; exact Hroot).
  destruct (witness_vertex_node_exists d system (witness_nodes witness) root)
    as [representative Hrepresentative_node].
  destruct (bottom_scc_face_stripping_with_extension d system safe witness
    root root representative Hroot Hroot_bottom Hrepresentative_node) as
    [offset [faces [Hoffset [Hextension_semilinear
      [Hextension_attractor [Hextension_safe Hpackage]]]]]].
  pose proof Hpackage as Hpackage_parts.
  destruct Hpackage_parts as
    [Hordered [Hhead [Hslices [Hcomplete [Hfirst Hdiagonal]]]]].
  destruct (face_replacement_blocks_exists d system
    (witness_nodes witness) root representative
    (NSetAsZ (BottomSCCLinearSlice (witness_nodes witness) root representative
      (witness_attractor witness) offset))
    (NSetAsZ (BottomSCCRegion (witness_nodes witness) root representative))
    faces Hordered Hslices) as [blocks Hblocks].
  destruct (bottom_scc_occurrence_partition d system
    (witness_nodes witness) root) as
    [bottom [retained [Hpartition [Hbottom Hretained]]]].
  assert (Hbottom_nonempty : bottom <> []).
  { intro Hempty.
    assert (Hin : List.In representative bottom).
    { apply (proj2 (Hbottom representative)). exists root.
      split; assumption. }
    now rewrite Hempty in Hin. }
  assert (Hbottom_rank : List.Forall (fun node =>
      directed_irun_rank node = directed_irun_rank representative) bottom).
  { eapply bottom_partition_same_rank; eauto. }
  assert (Hreplacement_rank : List.Forall (fun node =>
      (directed_irun_rank node < directed_irun_rank representative)%nat)
      (replacement_nodes blocks)).
  { eapply replacement_nodes_lower_rank; eauto. }
  assert (Hnew_homogeneous : HomogeneousWitnessNodes
      (retained ++ replacement_nodes blocks)).
  { eapply replacement_nodes_homogeneous; eauto. }
  assert (Hnew_coverage : forall run, ValidIRun system run ->
      BottomSCCExtendedAttractor (witness_nodes witness) root representative
        (witness_attractor witness) offset (irun_target run) \/
      exists node, List.In node (retained ++ replacement_nodes blocks) /\
        DirectedRunMember node run).
  { eapply replacement_nodes_run_coverage; eauto. }
  unshelve eexists ({|
    witness_safe_semilinear := @witness_safe_semilinear d system safe witness;
    witness_reach_safe := @witness_reach_safe d system safe witness;
    witness_attractor := BottomSCCExtendedAttractor (witness_nodes witness)
      root representative (witness_attractor witness) offset;
    witness_attractor_semilinear := Hextension_semilinear;
    witness_attractor_closed := Hextension_attractor;
    witness_attractor_safe := Hextension_safe;
    witness_nodes := retained ++ replacement_nodes blocks;
    witness_nodes_homogeneous := Hnew_homogeneous;
    witness_run_coverage := Hnew_coverage
  |}).
  eapply bottom_replacement_rank_decreases.
  - exact Hpartition.
  - exact Hbottom_nonempty.
  - exact Hbottom_rank.
  - exact Hreplacement_rank.
  - apply directed_irun_rank_le_dimension.
Qed.
