# T10-C2-G1 改訂実装計画：有理V錐に対する格子版Gordanと公開契約

作成：2026-10-20。実装担当：Codex。**計画書であり、新規Coq証明を実施したという記録ではない。**

## 0. 基準状態と判断

- ブランチ：`work/mell-formalization`。
- 基準HEAD：`413803be4cd7e8019468cfaed594daf0e40ea93e`（相違する場合は無断checkout/resetしない）。
- 検証報告済みのG0：`lattice_gordan_hmatrix`（明示的H行列、整数群生成元リスト）。
- 検証報告済みのC1：`rational_hcone_finitely_generated`、`rational_closed_cone_finitely_generated`。
- 今回はG1のみ。C2-L（closed linearization）、C3、T10-D以降は対象外。
- 未追跡`vendor/presburger/`18ファイルと既存の未コミット監査ログには触れない。対象ファイルだけstage・commitし、pushしない。

**設計上の選択：`RationalPolyhedralCone`は有限V表示を基本契約にする。**

理由：C1の結論はV表示であり、C2-Lでも閉錐にC1を適用して得るものはV表示である。H表示だけを定義にすると、C1→G1の間に未証明のV→H橋渡しが残る。V表現は有理多面錐の標準的な表示であり、元の`lattice_gordan`の数学的対象を狭める意図はない。H→Vは完成済みC1-HLで接続できる。一般のV→H同値そのものは証明済みと主張しない。

## 1. 固定する公開契約

既存の具体型に合わせるが、数学的意味・量化範囲は変更しない。

```coq
Definition FinitelyGeneratedGroup {d} (G : ZSet d) : Prop :=
  exists generators : list (ZVec d),
    SameSet G (ZGroupGenerated generators).

Definition RationalPolyhedralCone {d} (C : QSet d) : Prop :=
  exists generators : list (QVec d),
    SameSet C (qcone_generated generators).

lattice_gordan :
  forall d (G : ZSet d) (C : QSet d),
    FinitelyGeneratedGroup G ->
    RationalPolyhedralCone C ->
    FinitelyGeneratedPeriodic
      (fun z => G z /\ C (zvec_to_qvec z)).
```

上の定義はCoq風の契約であり、実コード中の`SameSet`の暗黙引数・`Qeq`外延性・module pathを監査して具体化する。`ZGroupGenerated`は整数係数の生成**群**、`FinitelyGeneratedPeriodic`は自然数係数の生成**モノイド**であり、混同しない。

## 2. 実装段階と数学的証明

### G1-I：表現インターフェース（最初に実施する）

1. 上記2定義を導入し、`ZGroupGenerated`と`qcone_generated`の外延性を確認する。
2. `lattice_gordan_hmatrix`に対し、H表示集合が`RationalPolyhedralCone`であることを`rational_hcone_finitely_generated`から導く小さなadapterを作る。
3. C1の結論から`RationalPolyhedralCone C`を導く補題を証明する（元のC1型は不変）。
4. `lattice_gordan`のRED型契約を監査に固定する。**この段階では一般のV表示に対するGordanを証明済みとしない。**
5. 既存C1・G0の回帰と公開定理型、`Print Assumptions`を確認する。

### G1-Hilbert：整数格子と有限V錐の交わり

中間契約：任意の有限`W : list (QVec k)`に対し

```coq
integer_points_vcone_finitely_generated :
  forall k (W : list (QVec k)),
    FinitelyGeneratedPeriodic
      (fun z : ZVec k =>
         qcone_generated W (zvec_to_qvec z)).
```

- 各有理生成元の正の分母を払って整数生成元`w_i`を得る。錐の数値的同一性を証明する。
- `x∈Z^k∩cone(W)`を`x=Σ_i α_i w_i`、`α_i∈Q_{≥0}`と表す。
- `n_i=floor(α_i)∈N`、`0≤β_i=α_i-n_i<1`とし、整数の剰余`r=x-Σ n_i w_i=Σ β_i w_i`を得る。
- 各座標で`|r_j|≤Σ_i |w_{i,j}|`。有限の整数box内で錐に入る剰余`r`の有限リストを存在的に選ぶ（`classic`による有限リストfilterを許す）。
- `w_i`とその剰余の有限リストが、交わり集合の有限モノイド生成系になることを両方向に証明する。
- 非pointed、lineality、負の整数座標、零次元、空W、零生成元に対応する。基底の一意性・最小性は不要。

これは一般のV→H変換を使わない、有限基本平行多面体（bounded remainder）によるGordanの証明である。

### G1-Pullback：群生成元の係数空間への引き戻し

`g : list (ZVec d)`を群生成元、`v : list (QVec d)`を錐生成元とし、`k=length g, m=length v`と置く。整数係数空間の写像`F_Z: Z^k→Z^d`と、有理拡張`F_Q: Q^k→Q^d`を作る。

`(z,λ)∈Q^(k+m)`に対して

```
λ_j ≥ 0  (各j)
F_Q(z) = Σ_j λ_j v_j
```

を定める。これは斉次有理H制約なのでC1-HLを適用できる。有限生成元を`z`座標へ射影し、有限`U : list (QVec k)`を得る。

必要な双方向の同値は

```
∀z:QVec k,
  qcone_generated U z <->
  qcone_generated v (F_Q z)
```

である。H錐からの射影が非負有理線形結合を保存すること、および存在する`λ`との正確な対応を証明する。`z`自体に非負性は課さない。等号は`Qeq`/`QVecEq`で一貫させる。

### G1-Main：最終公開定理

`G∩C`の点`x`は、群の整数係数表示`x=F_Z(z)`を持つ。`x∈cone(v)`なら上の引き戻しから`z∈cone(U)`。Hilbert補題により、そのような整数`z`は固定された有限系で生成される。これを`F_Z`で写して、G∩Cの有限生成元を得る。

逆向きでは各生成元がGとCの両方に属し、両者が零と加法で閉じることを示す。`G`の整数係数と`FinitelyGeneratedPeriodic`の非負整数係数を取り違えない。

`lattice_gordan`を元のT10-P型のまま証明し、G0-Hの場合はC1-HLによって新公開型にも接続されることを監査する。一般のV→H同値は、この定理の証明上不要。

## 3. G1の受入・境界条件

- `d=0`、`k=0`、`m=0`、群`{0}`、錐`{0}`、全空間、一次元半直線。
- 低ランク部分群、重複した群生成元、群の負の生成元、非pointed錐、linealityを持つ錐。
- `G=2Z, C=Q_{≥0}`：交わりは`2N`。`G=Z^2, C=cone((1,0),(0,1))`：`N²`。
- H表示の特殊ケースが元のG0と整合すること。
- finite cover/分母/有限boxの存在から`Type`上の実行時oracleを作らない。存在定理は`Prop`でよい。
- RED/GREEN、focused regression、Coq `Check`/`Print`、`Print Assumptions`、`coqchk -silent`、独立レビュー、`git diff --check`。
- 未証明Axiom、Admitted、UIP/K、`Eq_rect_eq`、外部oracle、新しいライブラリ依存は禁止。古典論理依存は正確に報告。
- 既存T01〜T10-C2-G0の公開型を弱めない。予期しない型・数学的blockerでは作業保持のまま停止する。

## 4. Codexへの直近指示（G1-Iのみ）

基準HEAD `413803be4cd7e8019468cfaed594daf0e40ea93e`から、まず**G1-Iだけ**実施する。`FinitelyGeneratedGroup`と`RationalPolyhedralCone`を上の意味で実定義し、C1とG0のadapterを証明する。`lattice_gordan`の公開契約をRED監査に固定し、G1-Hilbert以降は実施せず停止・報告する。変更対象は、新しいインターフェース・adapter・監査文書・必要最小のbuild設定と本計画に限定。既存未コミット監査ログ・未追跡vendorファイルは触れず、対象のみcommit、pushしない。異なるHEADや既存の相反する定義があれば勝手に上書きせず停止する。

## 5. 後続C2-Lへの接続と非目標

C2-Lでは`CLin(P)=(P-P)∩QClosure(Con(P))`を用いる。C1のV表示からG1のV版Gordanへ直接接続できるが、別途、`QClosure(Con(P))`の定義可能性・閉性・錐性および`P-P`の有限生成群性を証明する必要がある。C2-G1の成功でこれらを証明したことにはしない。V→H表示の一般同値は今回必須ではないが、faceのH表示など別タスクが要求する場合は改めて計画する。

## 6. 参考

- T10-P監査書`docs/review/t10-planning-audit.md` の`lattice_gordan`契約。
- C1-HL `rational_hcone_finitely_generated`、C1最終`rational_closed_cone_finitely_generated`、G0 `lattice_gordan_hmatrix`（ユーザー報告された宣言）。
- Gordanの補題の整数基本平行多面体証明（例えば整数点を整数生成元の線形結合と有限有界剰余へ分解する標準証明）。
