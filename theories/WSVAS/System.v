From Coq Require Import Vector ZArith Lia.
From KruskalAfProp Require Import af.af.
From Mell.Core Require Import Vector.

Open Scope Z_scope.

Definition zvec_le {d} (left right : ZVec d) : Prop :=
  forall index, (Vector.nth left index <= Vector.nth right index)%Z.

Record WSVAS (d : nat) : Type := {
  ws_transition : Type;
  ws_transition_le : ws_transition -> ws_transition -> Prop;
  ws_transition_le_refl : forall transition,
    ws_transition_le transition transition;
  ws_transition_le_trans : forall left middle right,
    ws_transition_le left middle ->
    ws_transition_le middle right ->
    ws_transition_le left right;
  ws_transition_wqo : KruskalAfProp.af.af.af ws_transition_le;
  ws_transition_action : ws_transition -> ZVec d;
  ws_transition_action_monotone : forall left right,
    ws_transition_le left right ->
    zvec_le (ws_transition_action left) (ws_transition_action right);
  ws_transition_action_diamond : forall root left right,
    ws_transition_le root left ->
    ws_transition_le root right ->
    exists merged,
      ws_transition_le left merged /\
      ws_transition_le right merged /\
      zvec_add (ws_transition_action root) (ws_transition_action merged) =
        zvec_add (ws_transition_action left) (ws_transition_action right)
}.

Arguments ws_transition {d} _.
Arguments ws_transition_le {d} _ _ _.
Arguments ws_transition_le_refl {d} _ _.
Arguments ws_transition_le_trans {d} _ _ _ _ _ _.
Arguments ws_transition_wqo {d} _.
Arguments ws_transition_action {d} _ _.
Arguments ws_transition_action_monotone {d} _ _ _ _.
Arguments ws_transition_action_diamond {d} _ _ _ _ _ _.

Lemma zvec_le_refl : forall d (value : ZVec d), zvec_le value value.
Proof. intros d value index; reflexivity. Qed.

Lemma zvec_le_trans : forall d (left middle right : ZVec d),
    zvec_le left middle -> zvec_le middle right -> zvec_le left right.
Proof. intros d left middle right Hlm Hmr index; specialize (Hlm index); specialize (Hmr index); lia. Qed.
