From Mell.Core Require Import Code Vector.
From Mell.BVAS Require Import Code.
From Mell.Semilinear Require Import Presentation.

Definition component_codec (d : nat) : Codec (LinearComponent d) :=
  pair_codec (nvec_codec d) (list_codec (nvec_codec d)).

Definition semi_codec (d : nat) : Codec (SemiCode d) :=
  list_codec (component_codec d).

Definition encode_semi {d} : SemiCode d -> nat := encode (semi_codec d).
Definition decode_semi (d : nat) : nat -> option (SemiCode d) :=
  decode (semi_codec d).

Lemma decode_semi_encode : forall d (code : SemiCode d),
    decode_semi d (encode_semi code) = Some code.
Proof. intros; apply decode_encode. Qed.
