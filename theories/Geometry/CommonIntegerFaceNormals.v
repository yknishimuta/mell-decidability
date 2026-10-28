From Coq Require Import Classical_Prop Fin Lia List QArith Qring Vector ZArith.
From Mell.Core Require Import Vector.
From Mell.Geometry Require Import Faces FiniteFaces LatticeGordanInterface
  MathCompBridge QConeCore QIntegerHRep RationalDefinability.

Import ListNotations.
Open Scope Q_scope.

Definition IntegerNormalOrthogonalToFace {d}
    (face : QSet d) (normal : ZVec d) : Prop :=
  forall point : QVec d,
    face point -> qinner (zvec_to_qvec normal) point == 0.

Lemma qnormal_integer_supporting : forall d (cone : QSet d)
    (normal : QVec d) (integer_normal : ZVec d) (multiplier : positive),
    (forall index : Fin.t d,
      zvec_to_qvec integer_normal index ==
        inject_Z (Z.pos multiplier) * normal index) ->
    SupportingNormal cone normal ->
    SupportingNormal cone (zvec_to_qvec integer_normal).
Proof.
  intros d cone normal integer_normal multiplier Hcoordinates Hsupport
    point Hpoint.
  apply (proj1 (qnormal_integer_nonnegative_iff d normal integer_normal
    multiplier Hcoordinates point)).
  now apply Hsupport.
Qed.

Lemma qnormal_integer_zero_iff : forall d (normal : QVec d)
    (integer_normal : ZVec d) (multiplier : positive),
    (forall index : Fin.t d,
      zvec_to_qvec integer_normal index ==
        inject_Z (Z.pos multiplier) * normal index) ->
    forall point : QVec d,
      (qinner normal point == 0 <->
       qinner (zvec_to_qvec integer_normal) point == 0).
Proof.
  intros d normal integer_normal multiplier Hcoordinates point.
  pose proof (qnormal_integer_inner d normal integer_normal multiplier
    Hcoordinates point) as Hinner.
  assert (Hmultiplier_nonzero : ~ inject_Z (Z.pos multiplier) == 0).
  { intro Hzero. unfold Qeq, inject_Z in Hzero. cbn in Hzero. lia. }
  split; intro Hzero.
  - transitivity (inject_Z (Z.pos multiplier) * qinner normal point).
    + exact Hinner.
    + setoid_rewrite Hzero. ring.
  - assert (Hproduct :
        inject_Z (Z.pos multiplier) * qinner normal point == 0).
    { transitivity (qinner (zvec_to_qvec integer_normal) point).
      - symmetry. exact Hinner.
      - exact Hzero. }
    destruct (Qmult_integral _ _ Hproduct) as [Hbad | Hnormal].
    + contradiction.
    + exact Hnormal.
Qed.

Lemma supporting_normals_integerize : forall d (cone : QSet d)
    (normals : list (QVec d)),
    List.Forall (SupportingNormal cone) normals ->
    exists integer_normals : list (ZVec d),
      List.Forall
        (fun normal => SupportingNormal cone (zvec_to_qvec normal))
        integer_normals /\
      forall point : QVec d,
        (NormalOrthogonal normals point <->
         forall normal,
           List.In normal integer_normals ->
           qinner (zvec_to_qvec normal) point == 0).
Proof.
  intros d cone normals Hsupport.
  induction Hsupport as [|normal normals Hnormal Hnormals IH].
  - exists []. split; [constructor|].
    intro point. split; intros H candidate Hin; inversion Hin.
  - destruct (qnormal_clear_denominators d normal) as
      [multiplier [integer_normal Hcoordinates]].
    destruct IH as [integer_normals [Hinteger_support Horthogonal]].
    exists (integer_normal :: integer_normals). split.
    + constructor.
      * now apply qnormal_integer_supporting with
          (normal := normal) (multiplier := multiplier).
      * exact Hinteger_support.
    + intro point. split.
      * intros H candidate [Heq | Hin].
        -- subst candidate.
           apply (proj1 (qnormal_integer_zero_iff d normal integer_normal
             multiplier Hcoordinates point)).
           apply H. now left.
        -- apply (proj1 (Horthogonal point)).
           ++ intros rational Hrational. apply H. now right.
           ++ exact Hin.
      * intros H rational [Heq | Hin].
        -- subst rational.
           apply (proj2 (qnormal_integer_zero_iff d normal integer_normal
             multiplier Hcoordinates point)).
           apply H. now left.
        -- apply (proj2 (Horthogonal point)).
           ++ intros candidate Hcandidate. apply H. now right.
           ++ exact Hin.
Qed.

Theorem integer_face_witness : forall d (cone face : QSet d),
    FaceOf cone face ->
    exists normals : list (ZVec d),
      (forall normal,
        List.In normal normals ->
        SupportingNormal cone (zvec_to_qvec normal)) /\
      SameSet face
        (fun point =>
          cone point /\
          forall normal,
            List.In normal normals ->
            qinner (zvec_to_qvec normal) point == 0).
Proof.
  intros d cone face [normals [Hsupport Hface]].
  destruct (supporting_normals_integerize d cone normals Hsupport) as
    [integer_normals [Hinteger_support Horthogonal]].
  exists integer_normals. split.
  - intros normal Hin.
    exact (proj1 (List.Forall_forall _ _) Hinteger_support normal Hin).
  - intro point. rewrite (Hface point), (Horthogonal point). reflexivity.
Qed.

Lemma finite_faces_integer_witnesses : forall d (cone : QSet d)
    (faces : list (QSet d)),
    List.Forall (FaceOf cone) faces ->
    exists aggregate : list (ZVec d),
      List.Forall
        (fun normal => SupportingNormal cone (zvec_to_qvec normal))
        aggregate /\
      forall face,
        List.In face faces ->
        exists normals : list (ZVec d),
          (forall normal,
            List.In normal normals -> List.In normal aggregate) /\
          SameSet face
            (fun point =>
              cone point /\
              forall normal,
                List.In normal normals ->
                qinner (zvec_to_qvec normal) point == 0).
Proof.
  intros d cone faces Hfaces.
  induction Hfaces as [|face faces Hface Hfaces IH].
  - exists []. split; [constructor|].
    intros candidate Hin. inversion Hin.
  - destruct (integer_face_witness d cone face Hface) as
      [face_normals [Hface_support Hface_spec]].
    destruct IH as [tail_normals [Htail_support Htail_spec]].
    exists (face_normals ++ tail_normals). split.
    + apply List.Forall_app. split.
      * apply List.Forall_forall. exact Hface_support.
      * exact Htail_support.
    + intros candidate [Heq | Hin].
      * subst candidate. exists face_normals. split.
        -- intros normal Hnormal. apply in_or_app. now left.
        -- exact Hface_spec.
      * destruct (Htail_spec candidate Hin) as
          [normals [Hsubset Hspec]].
        exists normals. split.
        -- intros normal Hnormal. apply in_or_app. right.
           now apply Hsubset.
        -- exact Hspec.
Qed.

Lemma all_faces_integer_witnesses : forall d (cone : QSet d),
    RationalPolyhedralCone cone ->
    exists aggregate : list (ZVec d),
      List.Forall
        (fun normal => SupportingNormal cone (zvec_to_qvec normal))
        aggregate /\
      forall face,
        FaceOf cone face ->
        exists normals : list (ZVec d),
          (forall normal,
            List.In normal normals -> List.In normal aggregate) /\
          SameSet face
            (fun point =>
              cone point /\
              forall normal,
                List.In normal normals ->
                qinner (zvec_to_qvec normal) point == 0).
Proof.
  intros d cone Hpolyhedral.
  destruct (polyhedral_faces_finite d cone Hpolyhedral) as
    [faces [Hfaces_sound Hfaces_complete]].
  assert (Hfaces : List.Forall (FaceOf cone) faces).
  { apply List.Forall_forall. exact Hfaces_sound. }
  destruct (finite_faces_integer_witnesses d cone faces Hfaces) as
    [aggregate [Hsupport Hrepresentatives]].
  exists aggregate. split; [exact Hsupport|].
  intros face Hface.
  destruct (Hfaces_complete face Hface) as
    [representative [Hin Hsame]].
  destruct (Hrepresentatives representative Hin) as
    [normals [Hsubset Hspec]].
  exists normals. split; [exact Hsubset|].
  eapply same_set_trans; [exact Hsame|exact Hspec].
Qed.

Lemma integer_hrep_normals_supporting : forall d (cone : QSet d)
    (normals : list (ZVec d)),
    (forall point : QVec d,
      cone point <->
      forall normal,
        List.In normal normals ->
        0 <= qinner (zvec_to_qvec normal) point) ->
    List.Forall
      (fun normal => SupportingNormal cone (zvec_to_qvec normal))
      normals.
Proof.
  intros d cone normals Hrepresentation.
  apply List.Forall_forall. intros normal Hnormal point Hpoint.
  exact (proj1 (Hrepresentation point) Hpoint normal Hnormal).
Qed.

Theorem polyhedral_common_integer_face_normals :
    forall d (cone : QSet d),
    RationalPolyhedralCone cone ->
    exists normals : list (ZVec d),
      (forall point : QVec d,
        cone point <->
        forall normal,
          List.In normal normals ->
          0 <= qinner (zvec_to_qvec normal) point) /\
      (forall normal,
        List.In normal normals ->
        SupportingNormal cone (zvec_to_qvec normal)) /\
      (forall face : QSet d,
        FaceOf cone face ->
        SameSet face
          (fun point =>
            cone point /\
            forall normal,
              List.In normal normals ->
              IntegerNormalOrthogonalToFace face normal ->
              qinner (zvec_to_qvec normal) point == 0)).
Proof.
  intros d cone Hpolyhedral.
  destruct (polyhedral_cone_integer_hrep d cone Hpolyhedral) as
    [hrep_normals Hhrep].
  destruct (all_faces_integer_witnesses d cone Hpolyhedral) as
    [face_normals [Hface_support Hfaces]].
  assert (Hhrep_support : List.Forall
      (fun normal => SupportingNormal cone (zvec_to_qvec normal))
      hrep_normals).
  { now apply integer_hrep_normals_supporting. }
  exists (hrep_normals ++ face_normals). split.
  - intro point. split.
    + intro Hpoint. intros normal Hin.
      apply in_app_or in Hin as [Hin | Hin].
      * exact (proj1 (List.Forall_forall _ _) Hhrep_support normal Hin
          point Hpoint).
      * exact (proj1 (List.Forall_forall _ _) Hface_support normal Hin
          point Hpoint).
    + intro Hpoint. apply (proj2 (Hhrep point)).
      intros normal Hin. apply Hpoint. apply in_or_app. now left.
  - split.
    + intros normal Hin. apply in_app_or in Hin as [Hin | Hin].
      * exact (proj1 (List.Forall_forall _ _) Hhrep_support normal Hin).
      * exact (proj1 (List.Forall_forall _ _) Hface_support normal Hin).
    + intros face Hface.
    destruct (Hfaces face Hface) as [witnesses [Hwitnesses Hspec]].
    intro point. split.
    + intro Hpoint. split.
      * now apply (face_subset d cone face Hface).
      * intros normal Hin Horthogonal. now apply Horthogonal.
    + intros [Hpoint Hactive]. apply (proj2 (Hspec point)). split.
      * exact Hpoint.
      * intros normal Hin.
        apply Hactive.
        -- apply in_or_app. right. now apply Hwitnesses.
        -- intros face_point Hface_point.
           exact (proj2 (proj1 (Hspec face_point) Hface_point) normal Hin).
Qed.

Lemma face_active_integer_normals : forall d
    (normals : list (ZVec d)) (face : QSet d),
    exists active : list (ZVec d),
      forall normal,
        List.In normal active <->
        List.In normal normals /\
        IntegerNormalOrthogonalToFace face normal.
Proof.
  intros d normals face. induction normals as
      [|head tail [active Hactive]].
  - exists []. intro candidate. split.
    + intro H. inversion H.
    + intros [Hin _]. inversion Hin.
  - destruct (classic (IntegerNormalOrthogonalToFace face head)) as
      [Hnormal | Hnormal].
    + exists (head :: active). intro candidate. split.
      * intros [Heq | Hin].
        -- subst candidate. split; [now left|exact Hnormal].
        -- apply Hactive in Hin as [Hin Horthogonal].
           split; [now right|exact Horthogonal].
      * intros [[Heq | Hin] Horthogonal].
        -- now left.
        -- right. apply Hactive. now split.
    + exists active. intro candidate. split.
      * intro Hin. apply Hactive in Hin as [Hin Horthogonal].
        split; [now right|exact Horthogonal].
      * intros [[Heq | Hin] Horthogonal].
        -- subst candidate. contradiction.
        -- apply Hactive. now split.
Qed.

Lemma face_inactive_integer_normals : forall d
    (normals : list (ZVec d)) (face : QSet d),
    exists inactive : list (ZVec d),
      forall normal,
        List.In normal inactive <->
        List.In normal normals /\
        ~ IntegerNormalOrthogonalToFace face normal.
Proof.
  intros d normals face. induction normals as
      [|head tail [inactive Hinactive]].
  - exists []. intro candidate. split.
    + intro H. inversion H.
    + intros [Hin _]. inversion Hin.
  - destruct (classic (IntegerNormalOrthogonalToFace face head)) as
      [Hnormal | Hnormal].
    + exists inactive. intro candidate. split.
      * intro Hin. apply Hinactive in Hin as [Hin Hnot].
        split; [now right|exact Hnot].
      * intros [[Heq | Hin] Hnot].
        -- subst candidate. contradiction.
        -- apply Hinactive. now split.
    + exists (head :: inactive). intro candidate. split.
      * intros [Heq | Hin].
        -- subst candidate. split; [now left|exact Hnormal].
        -- apply Hinactive in Hin as [Hin Hnot].
           split; [now right|exact Hnot].
      * intros [[Heq | Hin] Hnot].
        -- now left.
        -- right. apply Hinactive. now split.
Qed.
