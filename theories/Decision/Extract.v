From Mell.Decision Require Import MELL.
From Mell.Logic Require Import Code.
From Mell.BVAS Require Import Code.
From Mell.Reduction Require Import Main.

From Coq Require Import Extraction ExtrOcamlNatBigInt ExtrOcamlZBigInt.
Extraction Language OCaml.
Set Extraction Output Directory "docs/review/extraction/final".

(** Use Coq's standard Zarith-backed arbitrary-precision realizations of
    [nat] and [Z].  The fixed-width [ExtrOcamlNatInt]/[ExtrOcamlZInt]
    mappings are intentionally not used. *)
Separate Extraction mell_decide decide_code mell_stage mell_search_fuel
  Mell.Logic.Code.encode_sequent Mell.BVAS.Code.decode_nvec
  Mell.Reduction.Main.decode_integer Mell.Reduction.Main.decode_action
  Mell.Reduction.Main.encode_ibvas Mell.Reduction.Main.decode_reach_instance
  Mell.Reduction.Main.zvector_codec.
