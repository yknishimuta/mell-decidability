# T10-C2-G0 実装計画 — 有理H錐と有限生成部分群の交わり（Gordanの補題）

作成: 2026-10-20。実装担当: Codex。**本書は計画であり、Coq実装・検証済みではない。**

## 0. 出発点・承認範囲

- 基準ブランチ: `work/mell-formalization`
- 基準HEAD: `9281d192ddd3f030a5b14f77297e49cf22d3fa01`
- C1完成済み（報告）: `rational_hcone_finitely_generated`、`rational_closed_cone_finitely_generated`
- 再利用するA0-L: `homogeneous_solutions_finitely_generated`。その実際の型とimportを最初に`Check`する。
- **今回実装するのはC2-G0のみ**。Gordanの一般公開型への接続、closed linearization の有限生成性・full性、push-in、center、facesには進まない。
- 旧`vendor/presburger/`の未追跡18ファイル、未コミット監査ログ、T01〜T10-C1の既存ソースを無断変更・stage・削除しない。pushしない。

## 1. 重要な区別

T10-P監査書は、最終的に次の定理を要求している。

```coq
lattice_gordan :
  forall d (G : ZSet d) (C : QSet d),
    FinitelyGeneratedGroup G ->
    RationalPolyhedralCone C ->
    FinitelyGeneratedPeriodic
      (fun z => G z /\ C (zvec_to_qvec z))
```

しかし、`FinitelyGeneratedGroup`と`RationalPolyhedralCone`の**実際の定義と表示型**は、使用箇所まで監査する必要がある。特に既存C1の「有限V表示」を、そのまま有限H表示と同一視してはいけない。一般のV→H変換は現在の証明から直ちには従わない。

今回は、表示が明示的な行列 `A : QMatrix rows d` と群生成元リスト `g : list (ZVec d)` に限定した、独立に役立つ下位結果を証明する。上記の一般公開定理を弱めたり変更したりしない。

## 2. C2-G0 の正確な数学的契約

整数係数の有限生成群を

\[
\operatorname{Group}(g_1,\ldots,g_k)
 = \left\{\sum_{i=1}^{k}z_i g_i:z_i\in\mathbb Z\right\}
\]

とする。有理斉次H錐を

\[
H_A=\{x\in\mathbb Q^d:A x\geq0\}
\]

とする。証明対象は

\[
\boxed{\operatorname{Group}(g_1,\ldots,g_k)\cap H_A\cap\mathbb Z^d
\text{ は有限生成の加法的モノイドである。}}
\]

概念的なCoq契約（実際の型名・含意・`Qeq`は実装で確定する）:

```coq
lattice_gordan_hmatrix :
  forall d rows (A : QMatrix rows d) (g : list (ZVec d)),
    FinitelyGeneratedPeriodic
      (fun z : ZVec d =>
        ZGroupGenerated g z /\
        HConicalConstraints A (zvec_to_qvec z))
```

`ZGroupGenerated`は **整数係数** の有限和で定義する。自然数係数モノイド `zvec_generated`とは区別する。

## 3. 推奨証明：A0-Lによる直接構成

### G0-1. 群の整数係数を正負の自然数係数に分ける

`k = length g`、`F : Z^k -> Z^d`を

\[
F(z)=\sum_{i=1}^k z_i g_i
\]

とする。`F`は加法を保存し、その像は `ZGroupGenerated g`と一致する。

任意の`z ∈ Z^k`を`z=p-n`、`p,n∈N^k`に分解し、分解と復元を証明する。`nat`の飽和減算ではなく、整数への埋め込み後に引く。

### G0-2. 分母除去と同次非負整数方程式

`A`の有限個の係数の正の共通分母`K>0`を選び、`M=K A` を整数係数行列にする。`A x ≥ 0 ↔ M x ≥ 0`を証明する。

`M F`を整数行列（大きさ`rows × k`）として構成し、

\[
B=[\,MF\quad -MF\quad -I_{rows}\,]
\]

と置く。非負整数変数 `h=(p,n,s)` に対して

\[
Bh=0\iff (MF)(p-n)=s,\quad s\in\mathbb N^{rows}.
\]

を証明する。`k=0`、`rows=0`、`d=0`を扱う。括弧付けされたベクトルappend/splitについて往復定理を使う。

### G0-3. A0-Lの有限生成定理を適用する

`homogeneous_solutions_finitely_generated`をこの`B`へ適用し、非負整数解モノイドの有限生成元リスト `h_1,...,h_t`を得る。

各`h_j=(p_j,n_j,s_j)`を

\[
\pi(h_j)=F(p_j-n_j)\in\mathbb Z^d
\]

へ射影し、有限リスト `V = map π [h_1,...,h_t]` を作る。

- **健全性:** `Bh_j=0`から`M π(h_j)=s_j≥0`、従って`π(h_j)∈Group(g)∩H_A`。この交わりは加法と零で閉じている。
- **完全性:** 任意の`x∈Group(g)∩H_A`について、整数係数`z∈Z^k`を取る。`z=p-n`、`s=M x≥0`と置けば`h=(p,n,s)`は`B`の同次非負整数解。A0-Lより`h`は`h_j`の自然数係数和なので、射影して`x`は`π(h_j)`の自然数係数和となる。

生成元リストは行列`A`と群生成元`g`から**先に固定**し、各`x`ごとに取り直さない。

この構成は、一般のMinkowski–Weyl、V→H変換、格子の基底・Smith normal form、bounded fundamental parallelepipedの有限性を必要としない。

## 4. 接続上の保留事項（今回は実装しない）

C2-G1以降で、一般公開定理 `lattice_gordan`に接続するには、`RationalPolyhedralCone C`から有限H表示を取り出せるか確認する。

- もしその定義が**有限H表示**なら、C2-G0から直ちに導く。
- もしその定義が**有限V表示**なら、有限Vから有限Hへの橋渡し、またはV表示に直接対応したGordan証明が別途必要。C1の`rational_closed_cone_finitely_generated`が提供するのは閉・定義可能錐から**V表示**への向きなので、逆を暗黙に用いない。
- 既存の`FinitelyGeneratedGroup G`が提案と異なる場合は型を固定し、正確な変換補題を別途計画する。

C2のclosed-linearizationへ適用するには、さらに `QClosure (Con P)` の定義可能性・閉性・錐性、実際の群`P-P`の有限生成性と、有理多面錐のH/V表示の対応が必要となりうる。これらはC2-G0の成功だけで完成したと報告しない。

## 5. RED・GREEN・監査・回帰

先行する実装契約に合わせて、予定ファイル例は `theories/Geometry/LatticeGordanH.v`、`theories/Audit/LatticeGordanHExamples.v`、`docs/review/t10-c2-g0-audit.md`、`_CoqProject`、`Makefile` とする。既存の実体に重複する場合は改変せず、必要なパス変更を記録する。

少なくとも以下の例を扱う。

1. `d=0`、`rows=0`、`g=[]`（零群）。
2. `G=Z`、`C=Q_{≥0}`：非負整数モノイド。
3. `G=2Z`、`C=Q_{≥0}`：偶数の非負整数モノイド。
4. `G=Z`、`C=Q_{≤0}`：負の整数方向も保持。
5. `G=Z(1,1)⊂Z²`、`C=Q_{≥0}²`：低ランク群。
6. linealityのあるH錐、冗長・零係数行、冗長群生成元、非正規化Q表現。
7. 符号付き係数の群と、自然数係数のモノイドを混同しない反例。

受け入れ条件:

- 公開結果のRED（欠落に由来する失敗）とGREEN（機械検証）を記録。
- `lattice_gordan_hmatrix`に相当する一般定理を、行列/生成元リストの全量化と`d=0`を含めて証明。
- `Check`（完全型）、`Print Assumptions`、対象`.vo`の`coqchk -silent`、関連C1・A0-L・T10-Bの回帰、`git diff --check`、独立レビュー。
- 許容公理は既存の`Classical_Prop.classic`のみ。`Admitted`、新規`Axiom`、`ClassicalEpsilon.constructive_indefinite_description`、UIP/K、`Eq_rect_eq`、未証明oracleは禁止。
- 基準HEADからの無関係な変更なし。`git add -A`なし。対象ファイルだけを明示stageしてcommit。pushしない。
- **C2-G0を完了したら停止し、C2-G1やclosed linearizationには進まない。**

停止対象: 実定理型が想定と根本的に異なる／`FinitelyGeneratedPeriodic`を弱めないと証明できない／未承認の大規模依存追加や既存定理の変更が必要／数学的反例を発見した場合。補題の小規模な線形演算・append/split・有限和は承認範囲に含む。

## 6. 報告形式

(1) 完成定理の完全型。(2) 主要な同値・射影補題。(3) 公理監査の全文。(4) 実際のGREEN/回帰と`coqchk`の終了コード。(5) 独立レビュー所見。(6) コミットID、最終HEAD、残るC2-G1/closed-linearizationの義務。

**注意:** 本書は外部ファイルとして作成された計画案であり、Codexローカルリポジトリには自動配置されない。実装用原本として使う場合は配置・ハッシュ照合し、同一内容の契約として追跡する。
