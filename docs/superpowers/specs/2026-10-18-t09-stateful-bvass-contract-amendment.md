# T09 設計変更：状態付きBVASS・実行順序・有限被覆の公開契約

作成日：2026-10-18
対象：MELL決定可能性のCoq形式化、T09のみ
基準：`work/mell-formalization`、HEAD `826ce7e4942742cfc872260f31ff5ba7aad3437f`
状態：**数学的・実装上の公開契約案を承認**。Coqの実際の定義名と構文はリポジトリの型に合わせてよいが、数学的意味・量化範囲は変更不可。この文書自体はコンパイル済みCoqソースではない。

## 0. 判断

Option 2を以下の補足条件付きで承認する。

- 状態なし `IBVAS d`／`IRun`／`Reach` と、T06で修正済みの `IRunLe`・合併性を保全する。
- 状態付き系 `SBVAS d q`、状態付き実行・到達関係、文脈挿入順序を独立して追加する。`RootConfigLe`を状態なしの木に無理に定義しない。
- 原論文の規則の子状態は **多重集合**。実装の`list (Fin.t q)`は有限表現であり、リスト順序によって到達可能性が変化しないことを証明する。任意の内部節点の子は並べ替え可能とする。
- 非空入力規則と、有限の初期配置を分ける。0項規則は初期配置と同じ意味であり、脱落させない。
- 有限basisは **各固定systemの全有効な実行木** に対する存在命題とし、basis自体の計算可能性は主張しない。
- `RootConfigLe ∧ OrderedDecorEmbed` を強い補助関係とし、**元の文脈挿入順序への片方向の含意**を証明する。等価性を無条件に主張しない（監査 R05）。
- `IRunLe`（Appendix B.1 / R03）と状態付き `ContextOrder`（FoSSaCS / R05）は別の順序である。T11の利用先を混同しない。

## 1. データと意味論

### 1.1 Coq風の型契約（擬似コード）

```coq
(* Fin.t q は有限状態。q = 0 の空状態集合も定義上許し、
   状態を要する定理はその実例があるときのみ適用。 *)
Definition SConfig (d q : nat) := (Fin.t q * NVec d)%type.

Record SRule (d q : nat) := {
  input_states : list (Fin.t q);
  input_nonempty : input_states <> [];
  output_state : Fin.t q;
  delta : ZVec d
}.

Record SBVAS (d q : nat) := {
  initial_configs : list (SConfig d q);
  rules : list (SRule d q)
}.
```

`SRule` のリストは固定された入力多重集合の**表現**。状態の重複を含めた多重度が重要。リスト順序は観測できる意味論に影響させず、子の配置の並べ替え・規則状態列との整合性の同値を証明する。Raw tree側で規則indexや子の順序があることは差し支えない。原論文の0項transitionは、その更新ベクトルが非負である場合に`initial_configs`へ翻訳する。負の初期更新は有効な葉を生成しない。

### 1.2 状態付き到達性

目標となる帰納的関係は、以下の数学的内容と完全一致させる。

- 初期：`(s,x) ∈ initial_configs S` なら `SReach S s x`。
- 規則：`r∈rules S`、`input_states r=[s1,...,sn]` で、子の到達配置が`(s_i,x_i)`に対応し、`y = δ(r)+Σ_i x_i`が全成分非負なら、`SReach S (output_state r) y`。子の順序を変更しても到達関係は変わらない。
- 実行木：各内部節点でこの規則条件を満たし、葉は初期配置の**発生**を持つ。各節点のカウンターは `NVec d`。

公開契約：

```text
SReach : forall {d q}, SBVAS d q -> Fin.t q -> NVec d -> Prop
ValidSRun : forall {d q}, SBVAS d q -> SRun d q -> Prop
stateful_run_reach_iff :
  forall d q (S : SBVAS d q) s x,
    SReach S s x <->
    exists r, ValidSRun S r /\ root_config r = (s,x)
```

実行の木の順序と生の規則番号は区別する。葉のみ、初期集合空、次元0、状態集合空、同一状態の重複入力、負更新、適用不能な中間配置をテストに含める。

## 2. 状態除去（fresh gate）

元の規則 `τ : (s1,x1),...,(sn,xn) ↦ (s,a+Σxi)` ごとに新しいgate `gτ` を用意し、通常状態座標の集合とgate座標の集合を互いに素にする。`erase_states`は通常座標 `d` に状態tag `q` 個・規則gate `|rules S|` 個を加えた状態なし `IBVAS (d+q+|rules S|)` を構成する。

- 初期 `(s,x)` を `(x,e_s,0_gates)` へ写す。
- 規則のn項前半を `(a, -Σ_i e_si, +e_gτ)` とする。
- 後半の単項規則を `(0,+e_s,-e_gτ)` とする。
- 生成した中間節点にもtag総和1が成り立つ。
- 前半節点は、子の状態tagの**多重集合**が規則の要求と一致するときのみ可能。gateを要求状態の代用にできない。
- 後半節点は対応するgateだけを消費できる。

公開契約（`Fin`添字やベクトル次元の括りは実装の既存APIに合わせる）：

```text
erase_states : forall {d q}, SBVAS d q ->
  IBVAS (d + q + number_of_rules S)

encode_state_config : forall (S : SBVAS d q),
  Fin.t q -> NVec d -> NVec (d + q + number_of_rules S)

erase_states_correct :
  forall d q (S : SBVAS d q) (s : Fin.t q) (x : NVec d),
     SReach S s x
     <-> Reach (erase_states S) (encode_state_config S s x)
```

`erase_states_correct` の逆向きでは、到達する中間gate配置と通常状態配置を**同時構造帰納法**で分類する。単に到達集合を射影した同値に弱めない。状態tagに余計な座標が立っていないことを目標の符号化で保証する。

追加する回帰例：状態 `q,r`、初期 `(r,0)`、規則 `q --(+1)--> q`。naiveに状態を捨てた場合の偽の `(r,1)` をfresh-gate版が生成しないこと。規則二つが同じ変位を持つ場合、重複入力状態、自己ループも確認する。

## 3. 状態付き実行順序（R05）

### 3.1 三つの関係を区別

```text
RootConfigLe(c1,c2) := state(c1)=state(c2) /\ counter(c1)≤counter(c2)
OrderedDecorEmbed : 状態・作用・子位置を整合させた装飾木の埋め込み
ContextOrder : hereditarily-positive なcontext familyの挿入により得る**元の**実行順序
```

`RootConfigLe`は状態付きの配置にだけ定義する。

`ContextOrder`は単なる`RootConfigLe`でも、Kruskal型の木埋め込みそのものでもない。元のFoSSaCSの定義に従い、各contextのhole/rootは同じ状態とし、元部分木ごとの挿入効果の和が非負となることを要求する。holeへの経路上に一時的な負カウンターを許す元のcontext定義を、不必要に強い「contextの全節点が非負」へ変更しない。

### 3.2 R05の証明契約

```text
ordered_embed_implies_context_insert :
  forall d q (S : SBVAS d q)
         (alpha beta : ValidSRun S),
    RootConfigLe (root alpha) (root beta) ->
    OrderedDecorEmbed alpha beta ->
    ContextOrder S alpha beta
```

`OrderedDecorEmbed`では子の実際の枝対応を保存する。子カウンターの多重集合比較から、別の枝への対応を使って元のContextOrderを結論しない。根の座標比較は独立に必要であり、根が埋め込み先の内部節点に対応するときも保持する。

また、元の関係の反射性・推移性・必要な合併性を確認し、強い`OrderedDecorEmbed`側の合併性を無条件に仮定しない。既存のT06 `IRunLe`の合併性を状態付きへ無証明で転送しない。

## 4. WQOと有限basisの完全な意味

### 4.1 状態なしIBVAS（R03）

固定した `S:IBVAS d` について、`ValidIRun S`の全要素上に`IRunLe`を制限する。`afs`はCoq-Kruskal等の定義に合わせるが、数学的には「任意の無限列に比較可能な前後の二項がある」こと。

```text
irun_le_wqo :
  forall d (S : IBVAS d), afs (IRunLe_on (ValidIRun S))

irun_le_finite_cover :
  forall d (S : IBVAS d),
    exists (basis : list (ValidIRun S)),
      forall r : ValidIRun S,
        exists b, In b basis /\ IRunLe b r
```

葉のarity 0を装飾ラベルに含める。比較はroot outputの独立した座標比較を伴う。これはT11の初期安全性証人で全IRunsを被覆し、Lemma 5.6の証拠alphabetにも使う。有限basisの存在は`Prop`で述べ、計算可能なbasis生成器を要請しない。比較の反対称性は必須としない。

### 4.2 状態付きBVASS（R05）

固定した `S:SBVAS d q` の **全有効状態付き実行木**を台集合とする。初期配置でない葉を許すraw/open run全体に対する定理と取り違えない。

```text
context_order_wqo :
  forall d q (S : SBVAS d q),
    afs (ContextOrder_on (ValidSRun S))

context_order_finite_cover :
  forall d q (S : SBVAS d q),
    exists (basis : list (ValidSRun S)),
      forall r : ValidSRun S,
        exists b, In b basis /\ ContextOrder S b r
```

`context_order_wqo`は`RootConfigLe ∧ OrderedDecorEmbed`という強い関係のWQOから、`ordered_embed_implies_context_insert`によるorder reflectionで導く。逆向きの同値は主張しない。

`context_order_finite_cover`は、同じ固定systemの有効な実行木を全て被覆する有限basisの**存在**。状態を無視したroot比較や、target集合だけの有限基底で置き換えない。basisの計算可能性は主張せず、T10のBVASS section論証へ意味論的に供給する。

### 4.3 状態なし／状態付きの橋（必要時のみ）

T09の他の証明で必要になった場合に限り、単一状態へのlift `lift_one_state : IBVAS d -> SBVAS d 1` と対応する実行・到達関係の意味保存を補助補題として用意する。T09の公開完了条件へ不要に追加しない。順序を同一視するときは、木の子順序/多重集合の翻訳まで含めた別の証明を要求する。`IRunLe = ContextOrder`を定義上の等式として仮定しない。

## 5. 承認するT09のファイル範囲

新規ファイルは元計画のT09に加え、状態付き系の定義・有効実行を置く`theories/BVASS/Stateful.v`（あるいは同等の単独ファイル）を認める。

- `theories/BVASS/Stateful.v` [追加承認]
- `theories/BVASS/ContextInsertion.v`
- `theories/BVASS/OrderedBridge.v`
- `theories/Reduction/StateErasure.v`
- `theories/Order/AlmostFullBridge.v`
- `theories/Order/FiniteBasis.v`
- `theories/Audit/BridgeExamples.v`
- 必要な`Makefile`、`_CoqProject`等のビルド登録、依存・設計・監査台帳の最小変更

T06で修正済みの`theories/BVAS/RunOrder.v`を再度変更する場合は、その変更がR03の証明導入に必要な最小限の内容であることを示す。`theories/BVAS/Amalgamation.v`と`theories/Audit/RepairExamples.v`の完成したT06証明は原則凍結。T01–T08の無関係なコード変更は禁止。さらに範囲拡大が必要なら停止して具体的な型と理由を報告する。

## 6. 実装順と停止条件

1. **T09.1 定義**：状態付きシステム/葉/有効実行/到達の定義と`stateful_run_reach_iff`。0項規則・multiset表現との整合性を監査。
2. **T09.2 erasure**：fresh gate、token総和1、通常状態/gateの同時帰納、`erase_states_correct`。
3. **T09.3 context**：元の状態付きcontextとhereditary positivity、`RootConfigLe`、ordered labelと子位置、片方向bridge。
4. **T09.4 WQO**：状態付きcontext関係のWQO→有限basis、別系統の`IRunLe` WQO→有限basis。一般のWQO→有限basisの共通補題は一つだけ共有してよい。
5. **T09.5 audit**：反例・根の状態と座標・子の対応・arity 0・重複入力・負更新・空初期配置・d=0を確認し、全型・仮定と`coqchk`を再検査。

途中のコミットは各段階が単独ビルド可能なときに限る。最終的に `make check-bridges`, `make audit-bridges`、関連するT06回帰、`coqchk`を実行する。`Admitted`、独自数学的`Axiom`、未実装oracleで証明を通してはならない。必要に応じ、Coqの古典数学への基礎論的依存は完全な型と`Print Assumptions`に記録する。

`vendor/presburger/`の既存未追跡18ファイルを変更・削除・stageしない。対象ファイルだけを明示的に`git add`し、`git add -A`を使わない。pushしない。**T09の完了後はT10へ進まず報告する。**

## 7. 完了報告の条件

報告に、`SBVAS`と葉の意味論、`erase_states_correct`の完全な型、2種のWQOと2種の有限basisの完全な型、`ordered_embed_implies_context_insert`の完全な型、`Print Assumptions`、検証コマンドの結果、独立レビュー、コミットID、最終HEAD、ワークツリー状態を記載する。

**参照資料（原論文）**

- Bizière–Leroux–Sutre, *Bridging the Gap Between Plain VASS and Branching VASS*, FoSSaCS 2026, Section 2.3およびSection 3: https://link.springer.com/chapter/10.1007/978-3-032-22730-0_4
- Bizière–Leroux–Sutre, *Solving the Reachability Problem for Branching Vector Addition Systems via Semilinear Inductive Invariants*, arXiv:2607.09558v1, Appendix B.1, Lemma B.1、およびSection 3: https://arxiv.org/html/2607.09558v1
- 内部：`2026-10-17-mell-formalization-design.md` R03/R05、`2026-10-17-mell-formalization-plan.md` T09、前回のS監査報告。
