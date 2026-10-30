# NoFlipモデルの n+8 最短性：条件付き合成候補

既提出ACC-P000019のn+8上界構成を参照する、下界・最短性候補の静的点検用snapshot候補です。上界提出とacc-nplus8-leanは変更していません。

私は数学の専門家ではなく、この候補の正しさを自力で判断・保証できません。GPTとClaudeを用いた探索から得た候補と証拠を、判断できる専門家に届けたいと考えています。私の役割は課題・方針の選択、AIへの検証依頼、証拠整理、提出判断です。

対象は自由群F(x,y)で、X=x⁻¹、Y=y⁻¹とし、全ての非負整数nについてS_n=(X y^n x Y^(n+1), xY^n)から厳密な順序付き終点(x,y)への到達を考えます。許す操作は(r,s)に対する(rs,s)、(rs⁻¹,s)、(r,sr)、(r,sr⁻¹)、および一方の成分をg∈{x,X,y,Y}で共役する操作です。成分反転を許さないNoFlipモデルで、各原子の費用は1、原列を左から右へ実行し、自己ループも一手として数えます。[L1](materials/math/PROBLEM.md)

中心候補C25は、明示された既存数学interfaceを前提としたとき、全n≥25で長さL≤n+7のNoFlip列はS_nから(x,y)へ厳密到達しない、という条件付き主張です。前提は、短成功のq還元とc0/c1/q3排除（F-T1/F-0/F-T2/F-T4）、q=n+5の被覆と原列復号（P1/P2/P3）、元整数域でのK1-Q/K1-φ/F-T6およびK7-Q/K7-φです。これらの正確な域・零run・原gap・同gap順序・整除条件はinterface表を保持します。[L2](materials/math/DEPENDENCY_CONTRACTS.md) / [L3](materials/math/COMPOSITION_PROOF.md)

さらに指定有限域F-T3/P7と同モデルの上界Uを前提に接続すると、最小成功長dについてd(0)=4、d(1)=7、d(2)=9、全n≥3でd(n)=n+8という合成候補になります。全ての前提を人間が査読済みとは主張しません。有限結果から全nへ外挿せず、一般AC/Stable ACの証明・反証や、反転等を許す別モデルの最短値へは広げません。[L1](materials/math/PROBLEM.md) / [L2](materials/math/DEPENDENCY_CONTRACTS.md) / [L3](materials/math/COMPOSITION_PROOF.md) / [L6](materials/p7/PROOF.md) / [L7](materials/math/evidence/definitions/Verify/SevenPrefix.lean.txt)

このsnapshotは原Proof、原域・lift・係数証書等の保存資料、上界およびF-T1/F-0の限定Leanソースを収録します。[保存AI評価記録の案内](docs/AI_EVALUATION_RECORD_GUIDE.md)で一部の記録の範囲・限界を示しますが、評価票全文と内部管理記録は含めません。AIの検討結果、Leanの命題と前提、人間専門家の評価は別であり、人間専門家の評価は参照した保存資料では未確認です。全最短性Lean検証済みとはせず、この選抜で新しい数学実行もしていません。[L4](README.ja.md#検証と限界)

お願いしたいのは、明示前提から合成が導かれるか、n域・操作・費用・推論方向・依存の循環や不足を静的に点検していただくことです。前提自体の全再証明を今回完了したとはしていません。点検を引き受けるかどうかは読者の判断であり、指摘は訂正に反映します。

関連提出はACC-P000019です。以下の参照はこのsnapshot内の相対リンクです。manifestや点検記録の状態ラベルは、保存版の作成段階を表します。repoの現在の可視性はGitHubの実設定で確認するもので、この本文は公開予定を既成事実としていません。

## 読む順序

[モデル](materials/math/PROBLEM.md)→[interface表](materials/math/DEPENDENCY_CONTRACTS.md)→[合成本文](materials/math/COMPOSITION_PROOF.md)→[数学証拠索引](materials/math/INDEX.md)を提案します。依頼は明示前提下の合成の静的点検で、全依存の独立再証明を完了したという意味ではありません。必要な方法・形式化範囲・前提・限界は開示し、私的な初回/後読の配布方式をこの公開選択へ自動移植しません。

合成本文は原本の節番号を保って§3から始まり、対象・候補命題・依存interfaceは[PROBLEM.md](materials/math/PROBLEM.md)と[DEPENDENCY_CONTRACTS.md](materials/math/DEPENDENCY_CONTRACTS.md)にあります。一部の原資料には当時の査読者向け文言が残りますが、この選抜へ段階的なアクセス制限を課すものではありません。

[P7原Proof全文](materials/p7/PROOF.md)と[cover抜粋](materials/math/evidence/upstream/cover.md)は別bytesで、除外行の内容を分類せず正確な行投影を[SOURCE_MAP](SOURCE_MAP.json)へ記しました。旧[008](materials/g2/B008/PROOF.txt)/[009](materials/g2/B009/PROOF.txt)は仮定するB009 interfaceの理解用です。P7/G2原Proofの作者段階の状態・OPENは歴史記録であり、ここで提示する明示前提付き合成との区別は[案内§3](docs/AI_EVALUATION_RECORD_GUIDE.md#3-原票のopenと現在の合成候補)を参照してください。[G3原35ソース索引](materials/g3/SOURCE_INDEX.json)は命題と前提を静的に読むためのものです。

## 検証と限界

今回行ったのはfile/hash/文字列/JSON/参照と不要な私的情報のパターン点検だけです。数学checker、対象コード、試験、Lean実行、新計算はしていません。原文中の過去の確認記述は当時の資料作成側/AI担当の記録で、人間専門家の評価や今回の新検証として扱いません。点検を引き受けるかは読者の判断です。

Lean原sourceは上界とF-T1/F-0の限定範囲です。詳細な確認ログ、compiler/kernel/runtime、外部package/source/cache、全repo/Lake rootを実行再現環境として供給していません。全最短性Lean検証済みや未実施コマンド成功を主張しません。G2原Proofの全巨大証書は未同梱で、B009は今回の仮定interfaceです。このsnapshotだけでG2全証書を独立検証できるとはせず、現K2/c4結果で旧固定証拠を代替しません。

選択した原data/Leanと未編集の数学原資料はbytesを保持しました。ただし[k7_q.public.md](materials/math/evidence/upstream/k7_q.public.md)は、原11行の運用受領段落だけを除いた新公開編集版です。他の行はbytesを保ち、基底snapshotの数学索引はそのファイル名だけを直しました。[SOURCE_MAP](SOURCE_MAP.json)で両方の原本/編集後hashを明示し、基底のこの2編集を同bytesとは称しません。interface表の説明補足と評価案内は、それらとは別の文書更新として記録しています。

[MANIFEST](MANIFEST.json)と[公開選抜の限定点検](EXPORT_CHECKS.json)を参照してください。同一性・文字列参照の検査は数学的証明の検証ではありません。指摘は訂正に反映します。[English](README.md)
