# MiniCooper Coq 8.20.1 port ledger

Upstream repository: <https://github.com/Armael/minicooper>

Pinned commit: `3f051307039456a88cf093921278b0dcf224f7cf`

Only the Gallina core is vendored. `Tactic.v` and its Template-Coq frontend are
excluded.

## Source hashes

| File | Upstream SHA-256 | Vendored SHA-256 |
| --- | --- | --- |
| `MyTactics.v` | `54fa5e62055d314ce8676e1cac41c52449cb5869c3a82624c87086f1a0849edd` | `ccf83950957c3af502fdf7c0726b52369918695856bd480c3a6eea52acaac377` |
| `LinSimpl.v` | `c0ad885e68b90b3be28119ddbade9500f243943ec0aa549457157bd0fd885cf8` | `492cf4db883aa6f318b6daeefcdc3319186e53cb50f304aab85938d4846b124e` |
| `Constant.v` | `2613c7622c90bf77b3cd0b54f01f3d8f067494827e984ae910f38f0d3c1abb37` | `87f70fff63db6542a37cd72bd6c65863b5ad2bd1391ba9e2217b1c7b01742cbe` |
| `Theory.v` | `986f362b0b39af5d7818087a7e7bd1623278e85e57c93176ba2e6f419c4eefac` | `3932b3e132a26621ad15af7eac01ed89a536aac76de6b85a410fbe61d1bc0619` |
| `LICENSE` | `a5681bf9b05db14d86776930017c647ad9e6e56ff6bbcfdf21e5848288dfaf1b` | `e3a994d82e644b03a792a930f574002658412f62407f5fee083f2555c5f23118` |

The license difference is only the addition of a final newline. `LinSimpl.v`
and `Constant.v` likewise differ only by a final newline.

## Proof-only compatibility changes

- `MyTactics.v`: replace the removed `Omega` import with `ZArith Lia`, replace
  each `omega` hint by `lia`, and update the adjacent comment.
- `Theory.v`: replace `omega` invocations by `lia`.
- `Theory.v`: remove a redundant final `nia` in `wf_mul_nonzero` after `eauto`
  closes the Coq 8.20 goal.
- `Theory.v`: give `interpret_mul_nonzero` explicit bullets.
- `Theory.v`: remove the now-unreachable line following `try lia` in
  `In_interval`.
- `Theory.v`: give `interpret_adjust` explicit bullets and make its final
  subgoals explicit.
- `Theory.v`: remove a redundant `nia` after `eauto` closes the corresponding
  goal near the Cooper correctness proof.

No datatype, interpreter, smart constructor, quantifier-elimination function,
or other computational definition was changed.
