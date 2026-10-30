# 段階1の資料索引

先読はPROBLEM.md→DEPENDENCY_CONTRACTS.md→COMPOSITION_PROOF.md。以下は必要箇所を読む原数学資料です。原資料には依存interfaceへの歴史的言及が残る場合がありますが、既存査読の結論や作者の自己点検値をあなたの根拠にしません。

|依存|相対path|範囲|
|---|---|---|
|全q入口・c0/c1・q3接続・五族ψ|evidence/upstream/frontier.md|上流数学本文の選択箇所|
|551被覆・原gap復号・Q/H輸送|evidence/upstream/cover.md|数学本文|
|k1 Q/φ/不達|evidence/upstream/k1_q.md、k1_phi.md、k1_nonarrival.md|数学本文|
|k7 Q/φ|evidence/upstream/k7_q.public.md、k7_phi.md|数学本文|
|B009母域と存在保存chain|evidence/upstream/B009_CONTRACT.json|数学的scope/chain。判定欄は未収録|
|14操作・初期/終点・Q/H・上界|evidence/definitions/|Lean原ソースを.txtとして収録。コンパイルは依頼しない|
|有限機械/551語形|evidence/data/MATRIX_AUTOMATON.json、SKELETON_TEMPLATES.json|機械/語形の実データ|
|原式|evidence/data/K1_SYSTEMS.json、K7_SYSTEMS.json|λ=0/1の各64原式。PREFIX_SYSTEMS_INDEX.json参照|
|k1原Q族と復号|evidence/data/Q_RAW_FAMILIES.jsonl、Q_REDUCED_FAMILIES.jsonl、Q_REDUCED_LIFTS.jsonl、Q_SURVIVOR_OCCURRENCES.jsonl|元族/occurrenceと対応|
|k1φ|evidence/data/k1_phi/|41族の数式と解域。K1_TEMPLATE_INDEX.jsonは551表への参照|
|k7原Q域|evidence/data/Q_RESIDUAL_SOLUTIONS.json|50条件|
|k7元lift|evidence/data/SOLUTION_LIFTS_INDEX.json→k7_raw_lifts/|各fileのoriginal_liftが元588表の一行|
|k7φ係数証明書|evidence/data/K7_PHI_CERTIFICATE_INDEX.json→k7_raw_lifts/|正多項式はsign×phi_parameters[1]。係数を二重収録しない|
|小nの有限結果|evidence/data/Q5_0_24_result.jsonl|保存された有限結果。全列挙の独立再実行とは区別|
|小nの完全性説明・元Q通過列|evidence/upstream/FINITE_RANGE_PROOF.md、evidence/data/frontier_finite/、Q5_0_24_qpass.jsonl|小nの数学的列挙説明と保存行|
|有限検査の数学source|evidence/source_readonly/|C++ sourceを.txtとして収録。実行しない|

FILE_INDEX.jsonにこの段階の全ファイルのbytes/SHAがあります。原数式や原域は残し、日時・環境/入力pin・作者identity_checks等の非数学的メタデータを除いています。相対参照を読んで初めて対応先を実読したことになります。いずれの索引も、原Hからの独立導出やLean検証を意味しません。未収録/未検証境界はEVIDENCE_BOUNDARIES.mdを参照してください。
