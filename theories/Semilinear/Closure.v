From Coq Require Import List Vector VectorSpec ZArith Lia.
From Mell.Core Require Import Vector.
From Mell.Semilinear Require Import Presentation LinearEquations Formula QuantifierFree.
From Mell.Presburger Require Import Syntax Semantics NatSemilinear.

Import ListNotations.

Module StdVector := Coq.Vectors.Vector.

Definition NSet (d : nat) := NVec d -> Prop.

Definition SameSet {A : Type} (X Y : A -> Prop) : Prop :=
  forall x, X x <-> Y x.

Definition Semilinear {d} (X : NSet d) : Prop :=
  exists code : SemiCode d, forall x, X x <-> denote code x.

Module Vector.
  Definition shiftin_left (d e : nat) (value : NVec (d + e)) : NVec d :=
    fst (StdVector.splitat d value).

  Definition shiftin_right (d e : nat) (value : NVec (d + e)) : NVec e :=
    snd (StdVector.splitat d value).
End Vector.

Lemma shiftin_left_append : forall d e (left : NVec d) (right : NVec e),
    Vector.shiftin_left d e (StdVector.append left right) = left.
Proof.
  intros. unfold Vector.shiftin_left. now rewrite VectorSpec.splitat_append.
Qed.

Lemma shiftin_right_append : forall d e (left : NVec d) (right : NVec e),
    Vector.shiftin_right d e (StdVector.append left right) = right.
Proof.
  intros. unfold Vector.shiftin_right. now rewrite VectorSpec.splitat_append.
Qed.

Lemma append_shiftin : forall d e (value : NVec (d + e)),
    StdVector.append (Vector.shiftin_left d e value)
      (Vector.shiftin_right d e value) = value.
Proof.
  intros d e value. unfold Vector.shiftin_left, Vector.shiftin_right.
  destruct (StdVector.splitat d value) as [left right] eqn:Hsplit.
  symmetry. now apply VectorSpec.append_splitat.
Qed.

Lemma denote_app : forall d (left right : SemiCode d) value,
    denote (left ++ right) value <-> denote left value \/ denote right value.
Proof.
  intros d left right value. unfold denote. split.
  - intros [component [Hin Hlinear]]. apply in_app_or in Hin as [Hin|Hin];
      [left|right]; exists component; auto.
  - intros [[component [Hin Hlinear]]|[component [Hin Hlinear]]].
    + exists component. split; [apply in_or_app; now left|exact Hlinear].
    + exists component. split; [apply in_or_app; now right|exact Hlinear].
Qed.

Fixpoint semicode_finite_union {d} (codes : list (SemiCode d)) : SemiCode d :=
  match codes with
  | [] => []
  | code :: tail => code ++ semicode_finite_union tail
  end.

Lemma semicode_finite_union_correct : forall d (codes : list (SemiCode d)) value,
    denote (semicode_finite_union codes) value <->
    exists code, List.In code codes /\ denote code value.
Proof.
  intros d codes. induction codes as [|code codes IH]; intro value; cbn.
  - split; [intro H; exfalso; now apply (denote_empty d value)|].
    intros [found [Hin _]]. inversion Hin.
  - rewrite denote_app, IH. split.
    + intros [Hhead|[found [Hin Hfound]]].
      * exists code. split; [now left|exact Hhead].
      * exists found. split; [now right|exact Hfound].
    + intros [found [[Heq|Hin] Hfound]].
      * subst found. now left.
      * right. exists found. auto.
Qed.

Theorem semilinear_finite_union :
  forall d (sets : list (NSet d)),
    List.Forall Semilinear sets ->
    Semilinear (fun x => exists X, List.In X sets /\ X x).
Proof.
  intros d sets Hsets. induction Hsets as [|X sets HX Hsets IH].
  - exists []. intro x. split.
    + intros [Y [Hin _]]. inversion Hin.
    + intro H. exfalso. now apply (denote_empty d x).
  - destruct HX as [head Hhead]. destruct IH as [tail Htail].
    exists (head ++ tail). intro x. rewrite denote_app. split.
    + intros [Y [[<-|Hin] HY]].
      * left. exact (proj1 (Hhead x) HY).
      * right. apply (proj1 (Htail x)). exists Y. split; assumption.
    + intros [Hx|Hx].
      * exists X. split; [now left|exact (proj2 (Hhead x) Hx)].
      * apply (proj2 (Htail x)) in Hx. destruct Hx as [Y [Hin HY]].
        exists Y. split; [now right|exact HY].
Qed.

Definition component_minkowski {d}
    (left right : LinearComponent d) : LinearComponent d :=
  (nvec_add (fst left) (fst right), snd left ++ snd right).

Definition semicode_minkowski {d}
    (left right : SemiCode d) : SemiCode d :=
  List.flat_map
    (fun left_component => List.map (component_minkowski left_component) right)
    left.

Lemma nvec_add_cross : forall d (a b c e : NVec d),
    nvec_add (nvec_add a b) (nvec_add c e) =
    nvec_add (nvec_add a c) (nvec_add b e).
Proof.
  intros d a b c e. apply (proj1 (StdVector.eq_nth_iff nat d _ _)).
  intros index index' Heq; subst index'. unfold nvec_add.
  repeat rewrite (StdVector.nth_map2 Nat.add _ _ index index index eq_refl eq_refl).
  lia.
Qed.

Lemma weighted_sum_app : forall d (left_coefficients right_coefficients : list nat)
    (left_periods right_periods : list (NVec d)) left_value right_value,
    weighted_sum left_coefficients left_periods = Some left_value ->
    weighted_sum right_coefficients right_periods = Some right_value ->
    weighted_sum (left_coefficients ++ right_coefficients)
      (left_periods ++ right_periods) = Some (nvec_add left_value right_value).
Proof.
  intros d left_coefficients. induction left_coefficients as [|coefficient coefficients IH];
    intros right_coefficients left_periods right_periods left_value right_value
      Hleft Hright; destruct left_periods as [|period periods]; cbn in Hleft;
      try discriminate.
  - inversion Hleft; subst left_value. cbn.
    rewrite Hright, nvec_add_zero_left_local. reflexivity.
  - destruct (weighted_sum coefficients periods) as [tail|] eqn:Htail;
      try discriminate.
    inversion Hleft; subst left_value. cbn.
    rewrite (IH right_coefficients periods right_periods tail right_value Htail Hright).
    rewrite nvec_add_assoc_local. reflexivity.
Qed.

Lemma weighted_sum_app_inv : forall d (coefficients : list nat)
    (left_periods right_periods : list (NVec d)) value,
    weighted_sum coefficients (left_periods ++ right_periods) = Some value ->
    exists left_coefficients right_coefficients left_value right_value,
      coefficients = left_coefficients ++ right_coefficients /\
      weighted_sum left_coefficients left_periods = Some left_value /\
      weighted_sum right_coefficients right_periods = Some right_value /\
      value = nvec_add left_value right_value.
Proof.
  intros d coefficients left_periods. revert coefficients.
  induction left_periods as [|period periods IH];
    intros coefficients right_periods value Hsum.
  - cbn in Hsum. exists [], coefficients, (nvec_zero d), value.
    split; [reflexivity|]. split; [reflexivity|]. split; [exact Hsum|].
    symmetry. apply nvec_add_zero_left_local.
  - destruct coefficients as [|coefficient coefficients]; cbn in Hsum;
      try discriminate.
    destruct (weighted_sum coefficients (periods ++ right_periods))
      as [tail|] eqn:Htail; try discriminate.
    inversion Hsum; subst value.
    destruct (IH coefficients right_periods tail Htail)
      as (left_coefficients & right_coefficients & left_value & right_value &
        Hcoefficients & Hleft & Hright & Htail_value).
    exists (coefficient :: left_coefficients), right_coefficients,
      (nvec_add (nvec_scale coefficient period) left_value), right_value.
    subst coefficients tail. split; [reflexivity|]. split.
    + cbn. now rewrite Hleft.
    + split; [exact Hright|]. now rewrite nvec_add_assoc_local.
Qed.

Lemma component_minkowski_correct : forall d
    (left right : LinearComponent d) value,
    linear_denote (component_minkowski left right) value <->
    exists left_value right_value,
      linear_denote left left_value /\ linear_denote right right_value /\
      value = nvec_add left_value right_value.
Proof.
  intros d [left_base left_periods] [right_base right_periods] value.
  unfold component_minkowski, linear_denote; cbn. split.
  - intros [coefficients [contribution [Hsum Hvalue]]].
    destruct (weighted_sum_app_inv d coefficients left_periods right_periods
      contribution Hsum) as
      (left_coefficients & right_coefficients & left_contribution &
        right_contribution & Hcoefficients & Hleft & Hright & Hcontribution).
    exists (nvec_add left_base left_contribution),
      (nvec_add right_base right_contribution).
    split.
    + exists left_coefficients, left_contribution. split; [exact Hleft|reflexivity].
    + split.
      * exists right_coefficients, right_contribution.
        split; [exact Hright|reflexivity].
      * subst contribution value. symmetry. apply nvec_add_cross.
  - intros (left_value & right_value & Hleft_linear & Hright_linear & Hvalue).
    destruct Hleft_linear as (left_coefficients & left_contribution &
      Hleft & Hleft_value).
    destruct Hright_linear as (right_coefficients & right_contribution &
      Hright & Hright_value).
    exists (left_coefficients ++ right_coefficients),
      (nvec_add left_contribution right_contribution). split.
    + now apply weighted_sum_app.
    + subst left_value right_value value. apply nvec_add_cross.
Qed.

Lemma semicode_minkowski_correct : forall d
    (left right : SemiCode d) value,
    denote (semicode_minkowski left right) value <->
    exists left_value right_value,
      denote left left_value /\ denote right right_value /\
      value = nvec_add left_value right_value.
Proof.
  intros d left right value. unfold semicode_minkowski, denote. split.
  - intros [component [Hin Hlinear]].
    apply in_flat_map in Hin as [left_component [Hleft Hin]].
    apply in_map_iff in Hin as [right_component [Heq Hright]]. subst component.
    apply component_minkowski_correct in Hlinear.
    destruct Hlinear as [left_value [right_value [HL [HR Hvalue]]]].
    exists left_value, right_value. repeat split; try assumption;
      [exists left_component|exists right_component]; auto.
  - intros [left_value [right_value
      [[left_component [Hleft HL]] [[right_component [Hright HR]] Hvalue]]]].
    exists (component_minkowski left_component right_component). split.
    + apply in_flat_map. exists left_component. split; [exact Hleft|].
      apply in_map. exact Hright.
    + apply component_minkowski_correct.
      exists left_value, right_value. auto.
Qed.

Theorem semilinear_minkowski_sum :
  forall d (X Y : NSet d),
    Semilinear X -> Semilinear Y ->
    Semilinear (fun z => exists x y, X x /\ Y y /\ z = nvec_add x y).
Proof.
  intros d X Y [left Hleft] [right Hright].
  exists (semicode_minkowski left right). intro value.
  rewrite semicode_minkowski_correct. split.
  - intros (x & y & HX & HY & Heq). exists x, y.
    split; [exact (proj1 (Hleft x) HX)|].
    split; [exact (proj1 (Hright y) HY)|exact Heq].
  - intros (x & y & HX & HY & Heq). exists x, y.
    split; [exact (proj2 (Hleft x) HX)|].
    split; [exact (proj2 (Hright y) HY)|exact Heq].
Qed.

Definition embed_left_vector {d e} (value : NVec d) : NVec (d + e) :=
  StdVector.append value (nvec_zero e).

Definition embed_right_vector {d e} (value : NVec e) : NVec (d + e) :=
  StdVector.append (nvec_zero d) value.

Definition map_component {d e} (map_vector : NVec d -> NVec e)
    (component : LinearComponent d) : LinearComponent e :=
  (map_vector (fst component), List.map map_vector (snd component)).

Definition map_semicode {d e} (map_vector : NVec d -> NVec e)
    (code : SemiCode d) : SemiCode e :=
  List.map (map_component map_vector) code.

Lemma nvec_scale_append : forall d e coefficient
    (left : NVec d) (right : NVec e),
    nvec_scale coefficient (StdVector.append left right) =
    StdVector.append (nvec_scale coefficient left) (nvec_scale coefficient right).
Proof.
  intros d e coefficient left right. unfold nvec_scale.
  apply StdVector.map_append.
Qed.

Lemma nvec_add_append_local : forall d e
    (left1 left2 : NVec d) (right1 right2 : NVec e),
    nvec_add (StdVector.append left1 right1) (StdVector.append left2 right2) =
    StdVector.append (nvec_add left1 left2) (nvec_add right1 right2).
Proof.
  intros d e left1. induction left1 as [|head d tail IH];
    intros left2 right1 right2.
  - refine (StdVector.case0 (fun left2 => _ = _) _ left2). reflexivity.
  - refine (StdVector.caseS' left2 (fun left2 => _ = _) _).
    intros head2 tail2. cbn. f_equal. apply IH.
Qed.

Lemma nvec_zero_append_local : forall d e,
    nvec_zero (d + e) = StdVector.append (nvec_zero d) (nvec_zero e).
Proof.
  intros d e. unfold nvec_zero. symmetry. apply VectorSpec.append_const.
Qed.

Lemma nvec_scale_zero_vector : forall d coefficient,
    nvec_scale coefficient (nvec_zero d) = nvec_zero d.
Proof.
  intros d coefficient. apply (proj1 (StdVector.eq_nth_iff nat d _ _)).
  intros index index' Heq; subst index'. unfold nvec_scale, nvec_zero.
  rewrite (StdVector.nth_map _ _ index index eq_refl),
    (StdVector.const_nth nat 0%nat d index). lia.
Qed.

Lemma weighted_sum_embed_left_iff : forall d e coefficients periods value,
    weighted_sum coefficients (List.map (@embed_left_vector d e) periods) =
      Some value <->
    exists source,
      weighted_sum coefficients periods = Some source /\
      value = embed_left_vector source.
Proof.
  intros d e coefficients. induction coefficients as [|coefficient coefficients IH];
    intros [|period periods] value.
  - cbn. split.
    + intro H. inversion H; subst value. exists (nvec_zero d). split; [reflexivity|].
      unfold embed_left_vector. rewrite <- nvec_zero_append_local. reflexivity.
    + intros [source [Hsum Hvalue]]. inversion Hsum; subst source value.
      unfold embed_left_vector. rewrite <- nvec_zero_append_local. reflexivity.
  - cbn. split; intro H; [discriminate|].
    destruct H as [source [Hsum _]]. discriminate.
  - cbn. split; intro H; [discriminate|].
    destruct H as [source [Hsum _]]. discriminate.
  - split.
    + cbn. destruct (weighted_sum coefficients
        (List.map (@embed_left_vector d e) periods)) as [tail|] eqn:Htail;
        intro H; try discriminate.
      apply (proj1 (IH periods tail)) in Htail.
      destruct Htail as [source [Hsource Htail]]. subst tail.
      inversion H; subst value.
      exists (nvec_add (nvec_scale coefficient period) source). split.
      * cbn. now rewrite Hsource.
      * unfold embed_left_vector. rewrite nvec_scale_append,
          nvec_add_append_local, nvec_scale_zero_vector,
          nvec_add_zero_left_local.
        reflexivity.
    + intros [result [Hresult Hvalue]]. cbn in Hresult.
      destruct (weighted_sum coefficients periods) as [source|] eqn:Hsource;
        try discriminate.
      inversion Hresult; subst result value. cbn.
      rewrite (proj2 (IH periods (embed_left_vector source))).
      2: { exists source. auto. }
      unfold embed_left_vector. rewrite nvec_scale_append,
        nvec_add_append_local, nvec_scale_zero_vector,
        nvec_add_zero_left_local.
      reflexivity.
Qed.

Lemma weighted_sum_embed_right_iff : forall d e coefficients periods value,
    weighted_sum coefficients (List.map (@embed_right_vector d e) periods) =
      Some value <->
    exists source,
      weighted_sum coefficients periods = Some source /\
      value = embed_right_vector source.
Proof.
  intros d e coefficients. induction coefficients as [|coefficient coefficients IH];
    intros [|period periods] value.
  - cbn. split.
    + intro H. inversion H; subst value. exists (nvec_zero e). split; [reflexivity|].
      unfold embed_right_vector. rewrite <- nvec_zero_append_local. reflexivity.
    + intros [source [Hsum Hvalue]]. inversion Hsum; subst source value.
      unfold embed_right_vector. rewrite <- nvec_zero_append_local. reflexivity.
  - cbn. split; intro H; [discriminate|].
    destruct H as [source [Hsum _]]. discriminate.
  - cbn. split; intro H; [discriminate|].
    destruct H as [source [Hsum _]]. discriminate.
  - split.
    + cbn. destruct (weighted_sum coefficients
        (List.map (@embed_right_vector d e) periods)) as [tail|] eqn:Htail;
        intro H; try discriminate.
      apply (proj1 (IH periods tail)) in Htail.
      destruct Htail as [source [Hsource Htail]]. subst tail.
      inversion H; subst value.
      exists (nvec_add (nvec_scale coefficient period) source). split.
      * cbn. now rewrite Hsource.
      * unfold embed_right_vector. rewrite nvec_scale_append,
          nvec_add_append_local, nvec_scale_zero_vector,
          nvec_add_zero_left_local.
        reflexivity.
    + intros [result [Hresult Hvalue]]. cbn in Hresult.
      destruct (weighted_sum coefficients periods) as [source|] eqn:Hsource;
        try discriminate.
      inversion Hresult; subst result value. cbn.
      rewrite (proj2 (IH periods (embed_right_vector source))).
      2: { exists source. auto. }
      unfold embed_right_vector. rewrite nvec_scale_append,
        nvec_add_append_local, nvec_scale_zero_vector,
        nvec_add_zero_left_local.
      reflexivity.
Qed.

Lemma map_semicode_embed_left_correct : forall d e (code : SemiCode d) value,
    denote (map_semicode (@embed_left_vector d e) code) value <->
    exists source, denote code source /\ value = embed_left_vector source.
Proof.
  intros d e code value. unfold denote, map_semicode. split.
  - intros [mapped [Hin Hlinear]]. apply in_map_iff in Hin as [component [<- Hin]].
    destruct component as [base periods]. unfold map_component, linear_denote in Hlinear.
    cbn in Hlinear. destruct Hlinear as [coefficients [contribution [Hsum Hvalue]]].
    apply weighted_sum_embed_left_iff in Hsum.
    destruct Hsum as [source_contribution [Hsum Hcontribution]]. subst contribution.
    exists (nvec_add base source_contribution). split.
    + exists (base, periods). split; [exact Hin|].
      exists coefficients, source_contribution. auto.
    + subst value. unfold embed_left_vector.
      now rewrite nvec_add_append_local, nvec_add_zero_left_local.
  - intros [source [[component [Hin Hlinear]] Hvalue]].
    exists (map_component (@embed_left_vector d e) component). split.
    + apply in_map. exact Hin.
    + destruct component as [base periods]. unfold linear_denote in *; cbn in *.
      destruct Hlinear as [coefficients [contribution [Hsum Hsource]]].
      exists coefficients, (embed_left_vector contribution). split.
      * apply weighted_sum_embed_left_iff. exists contribution. auto.
      * subst source value. unfold embed_left_vector.
        now rewrite nvec_add_append_local, nvec_add_zero_left_local.
Qed.

Lemma map_semicode_embed_right_correct : forall d e (code : SemiCode e) value,
    denote (map_semicode (@embed_right_vector d e) code) value <->
    exists source, denote code source /\ value = embed_right_vector source.
Proof.
  intros d e code value. unfold denote, map_semicode. split.
  - intros [mapped [Hin Hlinear]]. apply in_map_iff in Hin as [component [<- Hin]].
    destruct component as [base periods]. unfold map_component, linear_denote in Hlinear.
    cbn in Hlinear. destruct Hlinear as [coefficients [contribution [Hsum Hvalue]]].
    apply weighted_sum_embed_right_iff in Hsum.
    destruct Hsum as [source_contribution [Hsum Hcontribution]]. subst contribution.
    exists (nvec_add base source_contribution). split.
    + exists (base, periods). split; [exact Hin|].
      exists coefficients, source_contribution. auto.
    + subst value. unfold embed_right_vector.
      now rewrite nvec_add_append_local, nvec_add_zero_left_local.
  - intros [source [[component [Hin Hlinear]] Hvalue]].
    exists (map_component (@embed_right_vector d e) component). split.
    + apply in_map. exact Hin.
    + destruct component as [base periods]. unfold linear_denote in *; cbn in *.
      destruct Hlinear as [coefficients [contribution [Hsum Hsource]]].
      exists coefficients, (embed_right_vector contribution). split.
      * apply weighted_sum_embed_right_iff. exists contribution. auto.
      * subst source value. unfold embed_right_vector.
        now rewrite nvec_add_append_local, nvec_add_zero_left_local.
Qed.

Definition semicode_product {d e}
    (left : SemiCode d) (right : SemiCode e) : SemiCode (d + e) :=
  semicode_minkowski
    (map_semicode (@embed_left_vector d e) left)
    (map_semicode (@embed_right_vector d e) right).

Lemma semicode_product_correct : forall d e
    (left : SemiCode d) (right : SemiCode e) value,
    denote (semicode_product left right) value <->
    denote left (Vector.shiftin_left d e value) /\
    denote right (Vector.shiftin_right d e value).
Proof.
  intros d e left right value. unfold semicode_product.
  rewrite semicode_minkowski_correct. split.
  - intros [left_value [right_value [Hleft [Hright Hvalue]]]].
    apply map_semicode_embed_left_correct in Hleft.
    apply map_semicode_embed_right_correct in Hright.
    destruct Hleft as [x [Hx Hleft]]. destruct Hright as [y [Hy Hright]].
    subst left_value right_value. unfold embed_left_vector, embed_right_vector in Hvalue.
    rewrite nvec_add_append_local, nvec_add_zero_right_local,
      nvec_add_zero_left_local in Hvalue. subst value.
    now rewrite shiftin_left_append, shiftin_right_append.
  - intros [Hleft Hright].
    exists (embed_left_vector (Vector.shiftin_left d e value)),
      (embed_right_vector (Vector.shiftin_right d e value)).
    repeat split.
    + apply map_semicode_embed_left_correct. exists (Vector.shiftin_left d e value).
      auto.
    + apply map_semicode_embed_right_correct. exists (Vector.shiftin_right d e value).
      auto.
    + unfold embed_left_vector, embed_right_vector.
      rewrite nvec_add_append_local, nvec_add_zero_right_local,
        nvec_add_zero_left_local, append_shiftin. reflexivity.
Qed.

Theorem semilinear_product :
  forall d e (X : NSet d) (Y : NSet e),
    Semilinear X -> Semilinear Y ->
    Semilinear (fun z =>
      X (Vector.shiftin_left d e z) /\ Y (Vector.shiftin_right d e z)).
Proof.
  intros d e X Y [left Hleft] [right Hright].
  exists (semicode_product left right). intro value.
  rewrite semicode_product_correct, Hleft, Hright. reflexivity.
Qed.

Fixpoint nvec_tabulate (d : nat) : (Fin.t d -> nat) -> NVec d :=
  match d return (Fin.t d -> nat) -> NVec d with
  | O => fun _ => @StdVector.nil nat
  | S d' => fun entries =>
      @StdVector.cons nat (entries Fin.F1) d'
        (nvec_tabulate d' (fun index => entries (Fin.FS index)))
  end.

Lemma nvec_tabulate_nth : forall d (entries : Fin.t d -> nat) index,
    StdVector.nth (nvec_tabulate d entries) index = entries index.
Proof.
  intros d. induction d as [|d IH]; intros entries index.
  - exact (Fin.case0 (fun index =>
      StdVector.nth (nvec_tabulate 0 entries) index = entries index) index).
  - refine (Fin.caseS' index
      (fun index => StdVector.nth (nvec_tabulate (S d) entries) index =
        entries index) _ _).
    + reflexivity.
    + intro tail_index. cbn. apply IH.
Qed.

Definition nvec_project {d e} (f : Fin.t e -> Fin.t d)
    (value : NVec d) : NVec e :=
  nvec_tabulate e (fun index => StdVector.nth value (f index)).

Lemma nvec_project_nth : forall d e (f : Fin.t e -> Fin.t d)
    (value : NVec d) index,
    StdVector.nth (nvec_project f value) index = StdVector.nth value (f index).
Proof. intros. unfold nvec_project. apply nvec_tabulate_nth. Qed.

Lemma nvec_project_add : forall d e (f : Fin.t e -> Fin.t d)
    (left right : NVec d),
    nvec_project f (nvec_add left right) =
    nvec_add (nvec_project f left) (nvec_project f right).
Proof.
  intros d e f left right. apply (proj1 (StdVector.eq_nth_iff nat e _ _)).
  intros index index' Heq; subst index'.
  rewrite nvec_project_nth.
  unfold nvec_add.
  rewrite (StdVector.nth_map2 Nat.add _ _ (f index) (f index) (f index)
      eq_refl eq_refl),
    (StdVector.nth_map2 Nat.add _ _ index index index eq_refl eq_refl).
  repeat rewrite nvec_project_nth. reflexivity.
Qed.

Lemma nvec_project_scale : forall d e (f : Fin.t e -> Fin.t d)
    coefficient (value : NVec d),
    nvec_project f (nvec_scale coefficient value) =
    nvec_scale coefficient (nvec_project f value).
Proof.
  intros d e f coefficient value.
  apply (proj1 (StdVector.eq_nth_iff nat e _ _)).
  intros index index' Heq; subst index'.
  rewrite nvec_project_nth.
  unfold nvec_scale.
  rewrite (StdVector.nth_map _ _ (f index) (f index) eq_refl),
    (StdVector.nth_map _ _ index index eq_refl).
  repeat rewrite nvec_project_nth. reflexivity.
Qed.

Lemma nvec_project_zero : forall d e (f : Fin.t e -> Fin.t d),
    nvec_project f (nvec_zero d) = nvec_zero e.
Proof.
  intros d e f. apply (proj1 (StdVector.eq_nth_iff nat e _ _)).
  intros index index' Heq; subst index'. rewrite nvec_project_nth.
  unfold nvec_zero. repeat rewrite StdVector.const_nth. reflexivity.
Qed.

Lemma weighted_sum_project_iff : forall d e (f : Fin.t e -> Fin.t d)
    coefficients periods value,
    weighted_sum coefficients (List.map (nvec_project f) periods) = Some value <->
    exists source,
      weighted_sum coefficients periods = Some source /\
      value = nvec_project f source.
Proof.
  intros d e f coefficients. induction coefficients as [|coefficient coefficients IH];
    intros [|period periods] value.
  - cbn. split.
    + intro H. inversion H; subst value. exists (nvec_zero d). split; [reflexivity|].
      symmetry. apply nvec_project_zero.
    + intros [source [Hsum Hvalue]]. inversion Hsum; subst source value.
      f_equal. symmetry. apply nvec_project_zero.
  - cbn. split; intro H; [discriminate|].
    destruct H as [source [Hsum _]]. discriminate.
  - cbn. split; intro H; [discriminate|].
    destruct H as [source [Hsum _]]. discriminate.
  - split.
    + cbn. destruct (weighted_sum coefficients
        (List.map (nvec_project f) periods)) as [tail|] eqn:Htail;
        intro H; try discriminate.
      apply (proj1 (IH periods tail)) in Htail.
      destruct Htail as [source [Hsource Htail]]. subst tail.
      inversion H; subst value.
      exists (nvec_add (nvec_scale coefficient period) source). split.
      * cbn. now rewrite Hsource.
      * rewrite nvec_project_add, nvec_project_scale. reflexivity.
    + intros [result [Hresult Hvalue]]. cbn in Hresult.
      destruct (weighted_sum coefficients periods) as [source|] eqn:Hsource;
        try discriminate.
      inversion Hresult; subst result value. cbn.
      rewrite (proj2 (IH periods (nvec_project f source))).
      2: { exists source. auto. }
      rewrite nvec_project_add, nvec_project_scale. reflexivity.
Qed.

Definition semicode_projection {d e} (f : Fin.t e -> Fin.t d)
    (code : SemiCode d) : SemiCode e :=
  map_semicode (nvec_project f) code.

Lemma semicode_projection_correct : forall d e (f : Fin.t e -> Fin.t d)
    (code : SemiCode d) value,
    denote (semicode_projection f code) value <->
    exists source, denote code source /\ value = nvec_project f source.
Proof.
  intros d e f code value. unfold semicode_projection, map_semicode, denote. split.
  - intros [mapped [Hin Hlinear]]. apply in_map_iff in Hin as [component [<- Hin]].
    destruct component as [base periods]. unfold map_component, linear_denote in Hlinear.
    cbn in Hlinear. destruct Hlinear as [coefficients [contribution [Hsum Hvalue]]].
    apply weighted_sum_project_iff in Hsum.
    destruct Hsum as [source_contribution [Hsum Hcontribution]]. subst contribution.
    exists (nvec_add base source_contribution). split.
    + exists (base, periods). split; [exact Hin|].
      exists coefficients, source_contribution. auto.
    + subst value. now rewrite nvec_project_add.
  - intros [source [[component [Hin Hlinear]] Hvalue]].
    exists (map_component (nvec_project f) component). split.
    + apply in_map. exact Hin.
    + destruct component as [base periods]. unfold linear_denote in *; cbn in *.
      destruct Hlinear as [coefficients [contribution [Hsum Hsource]]].
      exists coefficients, (nvec_project f contribution). split.
      * apply weighted_sum_project_iff. exists contribution. auto.
      * subst source value. now rewrite nvec_project_add.
Qed.

Lemma nvec_project_characterization : forall d e (f : Fin.t e -> Fin.t d)
    (source : NVec d) (value : NVec e),
    value = nvec_project f source <->
    forall index, StdVector.nth value index = StdVector.nth source (f index).
Proof.
  intros d e f source value. split.
  - intros -> index. apply nvec_project_nth.
  - intro H. apply (proj1 (StdVector.eq_nth_iff nat e _ _)).
    intros index index' Heq; subst index'. rewrite nvec_project_nth. apply H.
Qed.

Theorem semilinear_projection :
  forall d e (f : Fin.t e -> Fin.t d) (X : NSet d),
    Semilinear X ->
    Semilinear (fun y => exists x, X x /\
      forall i, StdVector.nth y i = StdVector.nth x (f i)).
Proof.
  intros d e f X [code Hcode]. exists (semicode_projection f code). intro value.
  rewrite semicode_projection_correct. split.
  - intros [source [HX Hcoordinates]]. exists source. split.
    + exact (proj1 (Hcode source) HX).
    + apply nvec_project_characterization. exact Hcoordinates.
  - intros [source [Hdenote Hproject]]. exists source. split.
    + exact (proj2 (Hcode source) Hdenote).
    + apply nvec_project_characterization. exact Hproject.
Qed.

Lemma nvec_ext_entry_local : forall d (left right : NVec d),
    (forall coordinate, (coordinate < d)%nat ->
      vector_entry left coordinate = vector_entry right coordinate) ->
    left = right.
Proof.
  intros d left right Hentry. apply StdVector.eq_nth_iff.
  intros index index' Heq; subst index'.
  pose (coordinate := proj1_sig (Fin.to_nat index)).
  assert (Hcoordinate : (coordinate < d)%nat).
  { unfold coordinate. exact (proj2_sig (Fin.to_nat index)). }
  specialize (Hentry coordinate Hcoordinate).
  repeat rewrite vector_entry_nth_order with (Hcoordinate := Hcoordinate) in Hentry.
  assert (Hfin : Fin.of_nat_lt Hcoordinate = index).
  { apply Fin.to_nat_inj. rewrite Fin.to_nat_of_nat. reflexivity. }
  unfold StdVector.nth_order in Hentry. now rewrite Hfin in Hentry.
Qed.

Lemma compile_membership_nat_environment_correct : forall d
    (code : SemiCode d) (value : NVec d),
    formula_semantics (nat_environment value) (compile_membership code) <->
    denote code value.
Proof.
  intros d code value. rewrite compile_membership_correct. split.
  - intros [candidate [Hdenote Hmatches]].
    assert (candidate = value) as ->; [|exact Hdenote].
    apply nvec_ext_entry_local. intros coordinate Hcoordinate.
    specialize (Hmatches coordinate Hcoordinate). unfold nat_environment in Hmatches.
    lia.
  - intro Hdenote. exists value. split; [exact Hdenote|].
    intros coordinate Hcoordinate. reflexivity.
Qed.

Theorem semilinear_intersection :
  forall d (X Y : NSet d),
    Semilinear X -> Semilinear Y ->
    Semilinear (fun x => X x /\ Y x).
Proof.
  intros d X Y [left Hleft] [right Hright].
  set (membership := Syntax.ANd (compile_membership left) (compile_membership right)).
  assert (Hclosed : Syntax.formula_closed d membership = true).
  { unfold membership. cbn. rewrite compile_membership_closed,
      compile_membership_closed. reflexivity. }
  destruct (presburger_nat_semilinear d (fun _ => 0%Z) membership Hclosed)
    as [code Hcode].
  exists code. intro value. rewrite <- Hcode. unfold membership. cbn.
  rewrite !compile_membership_nat_environment_correct.
  rewrite <- Hleft, <- Hright. reflexivity.
Qed.

Theorem semilinear_complement :
  forall d (X : NSet d),
    Semilinear X -> Semilinear (fun x => ~ X x).
Proof.
  intros d X [source Hsource].
  set (membership := Syntax.Not (compile_membership source)).
  assert (Hclosed : Syntax.formula_closed d membership = true).
  { unfold membership. cbn. apply compile_membership_closed. }
  destruct (presburger_nat_semilinear d (fun _ => 0%Z) membership Hclosed)
    as [code Hcode].
  exists code. intro value. rewrite <- Hcode. unfold membership. cbn.
  rewrite compile_membership_nat_environment_correct, <- Hsource. reflexivity.
Qed.
