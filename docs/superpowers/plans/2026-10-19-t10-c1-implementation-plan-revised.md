# T10-C1 実装計画（改訂第2版）— 有理定義可能な閉錐の有限生成性

実装担当：Codex。本書は実装計画であり、追加のCoq証明・ビルド・コミットが完了したことを意味しない。各節のCoq風の定理型は、既存の実宣言を確認して具体化するまで契約案である。

この計画が置き換える文書：`2026-10-19-t10-c1-refined-proof-plan.md` の実装順序とC1-Hの必須経路。レビュー根拠：`2026-10-19-t10-c1-plan-review.md`。T10-P監査書の最終公開定理は変更しない。

初期HEAD：`ee181e0e59e52feee7eab41c8d48634f724c7e9b`（Codexの作業開始時に確認する。異なる場合は差分を報告し、黙ってcheckout・resetしない）。

適用範囲：T10-C1のみ。T10-C2以降、T10-D〜F、T11に着手しない。次に実行するのはC1-0の契約監査とC1-HLの実装だけであり、C1-HL完了後に一旦停止する。

## 0. 決定と変更点

### 0.1 維持する最終公開契約

以下の数学的意味と量化範囲を変更しない。

```coq
rational_closed_cone_finitely_generated :
  forall d (C : QSet d),
    QDefinable C -> IsCone C -> TopologicallyClosed C ->
    exists generators : list (QVec d),
      SameSet C (qcone_generated generators)
```

T10-Aで報告された実定義：

```coq
Definition QVec (d : nat) := Fin.t d -> Q.
Definition QSet (d : nat) := QVec d -> Prop.
Definition QDefinable {d} (set : QSet d) : Prop :=
  exists formula : QFormula,
    qformula_closed d formula = true /\
    forall value,
      set value <->
      qformula_semantics (qvec_environment value) formula.
```

`IsCone`、`TopologicallyClosed`、`qcone_generated`はC1開始時点で未宣言との報告である。数学的意味を先に固定して定義し、宣言が既に存在する場合は重複させずその実型を監査する。`SameSet`は点ごとのiffである。`QDefinable`を勝手に`RationalPolyhedralCone`へ置き換えない。

### 0.2 採用する証明経路

```text
既存：T10-A0-L homogeneous_solutions_finitely_generated
         │
         ▼
C1-0    Qeq・生成錐・有理閉性の契約を固定（小さな監査）
         │
         ▼
C1-HL   有理H錐 → 正の分母除去 → 整数斉次非負解 → 有限生成
         │
         ├────────────┐
         ▼            │
C1-QE1  一つの連言・一変数の有理QE（Fourier–Motzkin等）
         ▼            │
C1-QE2  Boolean結合・多重量化・自由変数環境 → 有限セル
         │            │
         └─────┬──────┘
               ▼
C1-Assembly  非空セルの斉次化・閉性・有限リスト合成
               ▼
rational_closed_cone_finitely_generated
```

変更の核心：旧C1-Hの「半空間切断の有限生成元公式」を必須作業から外し、既存A0-Lを利用した斉次有理H錐の有限生成性（C1-HL）を必須作業とする。半空間切断公式は数学的に有効な代替・追加成果として残すが、C1-HLが通る限り実装しない。一般の非斉次Minkowski–Weyl、単一H表示への全体変換、Q ↔ mathcomp ratの全面的なアダプターは必須にしない。

代償と公理境界：A0-L利用により、既報の`Classical_Prop.classic`依存がC1-HLへ伝播しうる。これは記録したうえで許容する。`ClassicalEpsilon.constructive_indefinite_description`、UIP/K、`Eqdep.Eq_rect_eq.eq_rect_eq`、新規公理や実行時oracleは導入しない。

## 1. 共通の型・意味論契約（C1-0）

### 1.1 Qeqによる数値同値

標準Qの数値的同値`Qeq`とCoqのLeibniz等式`eq`を区別する。ベクトルについて

```coq
QVecEq x y := forall i : Fin.t d, Qeq (x i) (y i)
```

を導入し、有限和・加算・スカラー倍・線形形式・生成錐所属が`QVecEq`を保存することを証明する。`QDefinable C`からCの`QVecEq`に関する外延性が得られることも橋渡し補題とする。任意の`C : QSet d`に外延性を無条件に仮定してはいけない。

生成錐`qcone_generated V x`は、リストVの各ベクトルに非負有理係数を付けた有限和がxと`QVecEq`で一致することを意味する。空リストの生成錐は`{0}`。重複元・零生成元を許す。数値的に等しい非正規化Q表現も同じ点として扱う。

### 1.2 錐・線形形式・有理閉性

`IsCone C`は少なくとも次の三条件を含む契約にする。

- 零ベクトルがCに属する。
- `x,y ∈ C`なら`x+y ∈ C`。
- `x ∈ C`、`λ∈Q`、`0≤λ`なら`λx ∈ C`。

線形形式は係数`a : QVec d`による有限内積として表すか、加法・任意有理スカラー倍の保存を証明可能な型で表す。任意の関数`QVec d -> Q`を線形形式とみなさない。

`TopologicallyClosed`は有限次元有理空間の相対位相として固定する。例えば

```coq
QClosure C x :=
  forall delta : Q, 0 < delta ->
    exists y, C y /\ forall i, |x i - y i| < delta

TopologicallyClosed C := forall x, QClosure C x -> C x
```

という座標ごとの有理近似契約を使用できる。既存の位相APIを使う場合はこの条件との同値を証明する。`QClosure`と実数空間の閉包を無証明で同一視しない。C1-HLの数学には閉性は不要だが、最終公開契約の意味論はこの段階で確定する。

### 1.3 実型の確認

作業開始前に以下を`Check`/`Print`および`Set Printing Implicit`で記録する。

- T10-Aの`QVec`、`QSet`、`QDefinable`、`QFormula`、`qformula_closed`、`qformula_semantics`。
- T10-A0-Lの`ZMatrix`、`HomogeneousSolution`、`GeneratedBy`、`homogeneous_solutions_finitely_generated`と、`GeneratedBy`を有限係数表示へ展開する実際の補題。
- 既存のQベクトル演算・自然数ベクトルのappend/split・有限和API。
- `IsCone`、`TopologicallyClosed`、`qcone_generated`がまだ未実装かどうか。

数学的な型が両立しない場合は、名前だけ合わせるラッパーで誤魔化さず、正確な型・差分を報告して停止する。

## 2. C1-HL：A0-Lを再利用する斉次有理H錐の有限生成性

### 2.1 必須の出力契約

`QMatrix rows d`を有理係数行列として、`H_A(x)`を各行の線形形式が非負である述語とする。以下を証明する。

```coq
rational_hcone_finitely_generated :
  forall rows d (A : QMatrix rows d),
    exists V : list (QVec d),
      forall x : QVec d,
        HConicalConstraints A x <-> qcone_generated V x
```

この型はCoq風の目標契約であり、名称・引数順序は実コードの行列型に合わせて確定する。数学的意味と全行に対する非負不等式は維持する。`rows=0`、`d=0`を除外しない。

### 2.2 補題HL-1：共通分母の正値除去

任意の`A : QMatrix rows d`に対して、正の整数Kと整数行列`M : ZMatrix rows d`を作り、

```text
K>0,    ι(M_ij) = K A_ij
```

を全要素について`Qeq`で証明する。正の分母の有限積で十分で、最小公倍数は不要。さらに

```text
∀x∈Q^d, Ax≥0 ↔ Mx≥0
```

を証明する。右辺のMによる線形作用は、有理数へ埋め込んだ整数係数で評価する。`Qden`や`Qnum`の数値同値との整合も含む。

### 2.3 補題HL-2：同次方程式への変換

整数行列`M : ZMatrix rows d`に対して、変数を

```text
u,v∈N^d, s∈N^rows
```

とし、整数行列

```text
B=[ M  -M  -I_rows ]
```

を構成する。Coq側の変数の括弧付けは`d + (d + rows)`に固定し、既存append/splitとの往復を証明する。

```text
Bh=0 ↔ M(u-v)=s
```

を示す。`u-v`はZへ埋め込んだ符号付き差であり、自然数の切り捨て減算ではない。

同時に、`h=(u,v,s)`から

```text
π(h)=ι(u)-ι(v)∈Q^d
```

を構成し、`Bh=0`なら`Mπ(h)≥0`を示す。射影は自然数加算を有理ベクトル加算へ移し、有限和と可換であることを証明する。

### 2.4 補題HL-3：A0-Lから生成元を得る

既存の

```coq
homogeneous_solutions_finitely_generated :
  forall rows d (matrix : ZMatrix rows d),
    exists generators : list (NVec d),
      (forall generator,
        List.In generator generators ->
        HomogeneousSolution matrix generator) /\
      (forall value,
        HomogeneousSolution matrix value <->
        GeneratedBy generators value)
```

をBへ適用し、固定の有限リストGを得る。`V := map pi G`とする。GとVは行列Aから先に固定し、任意の点xごとに取り直さない。

- 健全性：各`g∈G`に対し`Bg=0`、よって`M(pi g)≥0`。非負線形結合の閉包性から`cone(V)⊆H_A`。
- 完全性：`x∈H_A`について正整数Nを選び`z=Nx∈Z^d`とする。`z=u-v`となる自然数ベクトルを取り、`s=Mz≥0`と置く。`h=(u,v,s)`はBの同次非負整数解。`GeneratedBy G h`から`h=Σ_g n_g g`を得て、piを適用し、`x=Σ_g(n_g/N)pi(g)`とする。

`N>0`、有理係数`n_g/N≥0`、生成元の列と係数の対応、`QVecEq`による各等式を明示的に証明する。この段階に新たなGordan・一般Minkowski–Weyl・有理QEは不要。

### 2.5 C1-HLの境界例と回帰

- `d=0`、`rows=0`、全空間（`rows=0`）、零錐（相反する制約）、負係数。
- 一次元非負半直線と非正半直線。
- linealityを持つ半空間：例`d=2`で`y≥0`、x軸方向が両側に伸びるケース。
- 重複・冗長なH制約、零係数行、数値的に等しい異なるQ表現。
- 負の座標のまま`NVec`へ強制変換しないこと。

### 2.6 C1-HLの受入条件（ここでいったん停止）

- [ ] 公開補題・境界事例のREDを作り、未実装で失敗することを確認する。
- [ ] HL-1〜HL-3の意味保存と`rational_hcone_finitely_generated`を証明する。
- [ ] `make check-t10-c1-hl`・`make audit-t10-c1-hl`等の新規ターゲットを用意し、実際の成功コマンド・終了コードを記録する。
- [ ] 全対象`.vo`の`coqchk -silent`、完全な型、`Print Assumptions`、独立レビューを実施する。
- [ ] 追加の公理依存が`Classical_Prop.classic`だけか監査する。違えば停止して依存を報告する。
- [ ] C1-HLファイルと必要最小限のMakefile・`_CoqProject`・監査文書・本計画のみを明示的にstage/commit。pushしない。
- [ ] 完了後はC1-QE1に進まず停止・報告する。

## 3. C1-QE1：有理アフィン連言からの一変数消去

C1-HLが受理された後の別タスク。この節以降の実装は現時点では未承認の着手対象。

既存`QFormula`を監査し、各原子が有理アフィン等式・不等式であることを確認する。変数同士の乗算を許す構文なら、ここで停止して定理の前提と不足部分を報告する。Q上の量化子のみを扱い、整数MiniCooperの`u<v ↔ u+1≤v`は使わない。

出力契約：アフィンな弱/厳密不等式からなる有限の連言Bについて、一つの有理変数zを存在量化した意味と同値な、zを含まない有限DNFを返す変換を定義し、任意の自由変数環境に対する意味保存を証明する。

- 項のアフィン正規化とその評価保存、係数零の処理。
- 等式の処理：代入または上下の弱不等式への変換。
- Fourier–Motzkin：下界・上界の全組を比較し、いずれか一方が厳密なら比較も厳密にする。片側だけの境界、境界なし、弱境界同士の一致、厳密境界の一致を区別する。
- 密なQでの中点証人、および上下界のない場合の有理解の存在を証明する。
- 一段のbinder除去に伴うde Bruijn変数のshift/renamingと、任意環境での意味保存。

C1-QE1の作業チェック：

- [ ] アフィン項・原子式の意味保存を単体証明する。
- [ ] 一連言の一変数消去を実装し、弱/厳密境界の全分岐を証明する。
- [ ] de Bruijn renamingを含む任意環境での意味保存を証明する。
- [ ] focused RED/GREEN、coqchk、公理監査、独立レビューを実施して、対象ファイルのみコミットする。
- [ ] 単一の存在変数消去に留めて停止し、全称量化・複数段QEには進まない。

## 4. C1-QE2：一般QFormulaを有限セルへ

C1-QE1に続く別タスク。

出力契約：`QDefinable C`の証拠から、有限セルリスト`cells`が存在し、任意の`x:QVec d`について

```text
C(x) ↔ ∃D∈cells, CellSemantics(D,x)
```

が成り立つ。各セルは有理アフィン弱・厳密不等式の有限連言（空連言を許す）である。

- 原子の正規化：等式は弱不等式の連言、非等式は厳密不等式の選言にする。大小・否定・真偽を保持。
- Boolean結合の正規化と有限DNFの正当性。
- ∃にはC1-QE1、∀には`¬∃¬`を利用し、構造帰納で複数・交替量化を処理。
- `qformula_closed d`、自由変数環境、de Bruijn index、抽象定数が存在する場合の扱いを元の意味論どおり保持。
- 細部の表示形式にかかわらず、`Qeq`と集合所属のextensionalityを保存。

非目標：QEの実行性能、セル重複除去、非空性判定器、整数Presburgerへ移した量化子消去、実数への一般化。

C1-QE2の作業チェック：

- [ ] 原子式の正規化と負の原子式の意味保存を証明する。
- [ ] Boolean結合と多重量化を一般式へ帰納し、自由変数のスコープを保存する。
- [ ] `QDefinable C`から有限セルリストの存在と同値を証明する。
- [ ] focused RED/GREEN、coqchk、公理監査、独立レビュー、対象ファイルのコミット後に停止する。

## 5. C1-Assembly：非空セルの斉次化と閉錐への回収

C1-HLとC1-QE2が完成した後の最終C1タスク。

### 5.1 セル斉次化の正確な契約

セル

```text
D={y:A y≥b, B y>c}
```

に対し、非空の証人`y0∈D`を前提として、

```text
K_D={(t,x):t≥0, A x≥tb, B x≥tc}
```

を定義する。`K_D`は斉次の弱い有理H制約の錐であることを証明し、C1-HLの有限生成定理を適用する。strictな行も斉次化したH制約では`≥`に置き換わる。元セルの厳密性は後述の`y0`により回復する。

空セルは必ず除外する。空セル`0>0`を斉次化すると、本来の集合を越えた錐を作りうる。セルリストについてclassicで非空性を場合分けすることは許容するが、一般の選択公理・計算可能な非空判定を要求しない。

### 5.2 閉性により投影がC内に戻る補題

`D⊆C`、`IsCone C`、`TopologicallyClosed C`、`y0∈D`、`(t,x)∈K_D`なら **`x∈C`** を示す。

任意の有理`ε>0`に対し、

```text
y_ε=(x+εy0)/(t+ε)
```

はDに属する。従って

```text
x+εy0=(t+ε)y_ε∈C.
```

任意の`δ>0`に対し

```text
ε=δ/(1+Σ_i |(y0)_i|)
```

を選べば、有限個の全座標について`|ε(y0)_i|<δ`である。`QClosure`の定義と閉性から`x∈C`が従う。`t=0`の場合も同じ補題で処理する。`t≥0`と`ε>0`から分母`(t+ε)>0`を証明する。

逆向き：`y∈D`なら`(1,y)∈K_D`、従って斉次H錐の生成元の投影でyを表せる。

### 5.3 全セルの統合

`QDefinable C`から有限セルリストを得る。セルごとに、空ならスキップ、非空なら上記の生成元を投影した有限リストを選ぶ。有限個のリストを連結してVとする。

- 健全性：それぞれの投影生成元はCに属し、`IsCone C`が非負有理線形結合に閉じているので`cone(V)⊆C`。
- 完全性：任意の`x∈C`はあるセルDに属すため`(1,x)∈K_D`、よって`x∈cone(V)`。

C1-Assemblyの作業チェック：

- [ ] 空セルの斉次化を不正とする反例をテストし、非空性を補題の前提に置く。
- [ ] 斉次化H錐の構成、`(1,y)`の包含、ε近似と閉性の補題を証明する。
- [ ] 有限セルごとの生成元リストの結合と両方向の包含を証明する。
- [ ] 最終公開型・全公理監査・coqchk・独立レビューの後、対象ファイルだけをコミットする。

これにより、契約を変更せず

```coq
rational_closed_cone_finitely_generated :
  forall d (C : QSet d),
    QDefinable C -> IsCone C -> TopologicallyClosed C ->
    exists generators : list (QVec d),
      SameSet C (qcone_generated generators)
```

を証明する。単一H表示への変換は不要。`d=0`、零錐、全空間、非pointed錐、空セル、重複セル、非閉だが錐である反例（`{0} ∪ {(x,y): x>0, y>0}`）について回帰と前提監査を行う。

## 6. C2への橋渡し：記録するがC1の完成条件にはしない

T10-C2以降では`CLin(P)=(P-P)∩QClosure(Con(P))`を扱う。C1の定理を`QClosure(Con(P))`へ適用するには、別途以下が必要である。

```coq
QDefinable C -> QDefinable (QClosure C)
IsCone C -> IsCone (QClosure C)
TopologicallyClosed (QClosure C)
```

これらはC2開始時の独立した証明義務として台帳に残す（必要な`QClosure`の基本補題がC1でできていれば再利用する）。`Con(P)`の定義可能性や`P-P`の格子構造をC1で証明したことにしてはならない。`P-P`を全整数格子に置き換えない。位相閉包を実数閉包へ黙って変更しない。

## 7. 実装ファイル・所有権・コミット境界

以下は提案する新規ファイル名であり、Codexは最初に既存ファイルとの衝突を確認する。既存の命名・モジュール参照を尊重し、目的と型を変えずに必要な最小の修正だけを認める。

| 段階 | 新規/変更を認める場所（案） | 完了時の提出物 |
|---|---|---|
| C1-0 + C1-HL | `theories/Geometry/QConeCore.v`, `theories/Geometry/RationalHToV.v`, `theories/Audit/RationalHToVExamples.v`, `Makefile`, `_CoqProject`, `docs/review/t10-c1-hl-audit.md`, 本計画 | H→V定理、共通定義、型・公理監査 |
| C1-QE1 | `theories/Geometry/RationalQEOne.v`, `theories/Audit/RationalQEOneExamples.v`, ビルド/監査文書 | 一変数存在消去の意味保存 |
| C1-QE2 | `theories/Geometry/RationalQENormalForm.v`, `theories/Audit/RationalQENormalFormExamples.v`, ビルド/監査文書 | `QDefinable`の有限セル表現 |
| C1-Assembly | `theories/Geometry/RationalConeAssembly.v`, `theories/Audit/RationalConeAssemblyExamples.v`, ビルド/監査文書 | 最終C1定理 |

任意の段階で、リスト・ベクトル・数値同値に関する共通補題はその段階の所有ファイル内に置くか、追加の独立ファイルが不可欠なら先に範囲変更を報告する。既存T01〜T10-Bの公開型・実装は変更しない。個別タスク完了時は対象ファイルのみ明示的にstageし、コミット後に停止する。`git add -A`、push、既存未追跡資産の消去をしない。

次の作業者への依頼時にはこの改訂版をリポジトリ内`docs/superpowers/plans/2026-10-19-t10-c1-implementation-plan-revised.md`へ実際にコピーし、内容を読み取れることを確認する。ファイル未配置を理由に推測で実装してはならない。

## 8. 全段階共通の検証・停止条件

### 8.1 各段階の検証

1. RED：公開契約を要求する未実装テストを実行し、意図した理由で失敗することを記録。
2. GREEN：最小の実装後、focus buildと境界例を実行。既存回帰（T10-A0-L、A0-QF、A0-QE、T10-A、T10-B）も確認。
3. Kernel：変更モジュールと依存の`coqchk -silent`を実行。結果・終了コードを記録。
4. Trust：最終公開型（`Set Printing Implicit`込み）、`Print Assumptions`、`Admitted`/`admit`/`Abort`/独自`Axiom`/UIP/K/`Eq_rect_eq`を監査。グローバルな古典論理の依存は完全な名前で記録。
5. Git：`git diff --check`、対象ファイル限定stage/commit、コミット前後`git status --short`、最終HEADの記録。
6. 独立レビュー：実装者以外が、定義の忠実性、等号、量化順序、数学的同値、未証明依存を監査。

### 8.2 停止すべき場合・停止不要の場合

停止：数学的反例がある／元の最終公開型を変える必要がある／新しい大規模定理が不可欠で当段階の証明経路に収まらない／未承認の外部依存や公理が必要／範囲外の既存コードを変更しなければならない／証明義務を弱めないと成立しない／レビューで重大所見が残る。

停止不要：計画内で予定した分母除去、符号分解、有限和、append/split、de Bruijn操作、有理数の基本算術の補助補題が増えるだけの場合。これは予定したタスクの実装範囲内。ただし完成報告には主要補題を列記する。

既存の未コミット監査ログ、`vendor/presburger/`の未追跡18ファイルは変更・削除・stageしない。新規不備があれば作業ツリーを破棄せず、正確な不足定理・反例・影響範囲・現在のGit状態を報告する。

## 9. Codexに渡す次の1タスク（C1-0 + C1-HLだけ）

この段落と本書全体が、次の作業に対する指示契約となる。まだC1-QE1には着手しない。

> 基準HEAD `ee181e0e59e52feee7eab41c8d48634f724c7e9b` を確認し、この改訂版T10-C1計画のC1-0とC1-HLだけを実装してください。
>
> 最初に既存A0-LとQDefinableの完全型を確認し、Qeqの外延性、生成錐、有限和、IsCone、TopologicallyClosedの意味論を固定してください。次にA0-Lの`homogeneous_solutions_finitely_generated`を使い、有理H錐を正分母除去と`B=[M,-M,-I]`の同次非負整数方程式へ帰着させ、H錐の有限生成性を両方向で証明してください。
>
> C1-HLに必要な補助補題は計画の範囲内です。既存Coq-Polyhedraへの依存追加、一般Minkowski–Weylの移植、旧半空間切断アルゴリズムの必須実装は行わないでください。
>
> RED/GREEN、coqchk、完全型、Print Assumptions、独立レビューを行い、承認対象だけをコミットしてください。pushはしないでください。C1-HLが終了したら停止し、C1-QE1以降へは進まないでください。
>
> 対象外のコード、未コミット監査ログ、未追跡`vendor/presburger/`18ファイルは変更しないでください。blocker時は不足定理の正確な型を提出してください。

## 10. 典拠と改訂履歴

- 原実装計画：`2026-10-19-t10-c1-refined-proof-plan.md`（旧C1-H→C1-QE→C1-Assembly）。
- レビュー：`2026-10-19-t10-c1-plan-review.md`（既存A0-Lの利用、半空間切断公式、非空セル斉次化、Qeq/閉性、C2 bridge）。
- T10-P公開契約：`docs/review/t10-planning-audit.md`の`rational_closed_cone_finitely_generated`。
- 原論文の出典位置：Bizière–Leroux–Sutre 2026, arXiv:2607.09558v1 §4.1（Leroux 2011 Theorem 3.5への言及）。これは引用上の対応であり、上記A0-L再利用証明は本計画で採用する別の形式化経路である。
- 第2版の変更：C1-HをC1-HLへ変更、Qeqの共通契約、Q-native分母除去、C1-QE1/QE2の分割、非空セルの統一ε補題、C2橋渡しの明示、段階別ファイル・停止条件の明文化。
