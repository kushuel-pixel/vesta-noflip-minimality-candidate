# 依存interface（判断ラベルを与えない契約表）

各契約を仮定した合成の妥当性と、契約自身の原証拠の十分性を区別して所見を出す。原証拠はINDEX.mdおよびFILE_INDEX.jsonの相対path・hash指定から必要箇所だけ読む。

- F-T1: 全n∈Nat、NoFlip厳密成功、L≤n+7 ⇒ q=n+3又はn+5。
- F-0: 共役0回のNoFlip列で可換化終点IならQ中心終端(n²+1,n)、全nで不達。
- F-T2: n≥3、一共役の成功 ⇒ q≥3n+1、L≥3n+2。全8共役・両符号。
- F-T4: 全n≥3、NoFlip、L≤n+7、q=n+3の元成功なし。A一般域n≥19/有限3..18、B有限3..5/B009 n≥6を使う。B009は同じnの短literal B母域の最短成功からCORE成功代表を得る存在保存でありraw全列等式分類ではない。
- P1/P2: q=n+5、厳密SL₂積T_n=[[-n,1],[-1,0]]の全骨格をk1:204/k7:347の551語形で被覆。k=#ID3/4は1又は7。
- P3: 二共役を全原gap、同gap・同slot、零run、event0→event1の順でliteral復号。run指数は非負fragment和。n=m+Σu−5、支持内u=1+x・支持外0、Σx≥30−m−|S|、xは非負整数。
- K1-Q: n≥25,q=n+5,c=2,k=1,L=n+7,I,raw guardの元Q解を39列+二分割族G_r/G_sで必要十分分類。全0≤a≤n、六境界を含む。K1-φでは同原域の通過列はR19/21/22/13/14=F1/2/3/4/5と原列一致。F-T6はこの五族のψ像不一致を全n≥1で与える。
- K1-NA（= K1-N25-NONARRIVAL）: K1-Q・K1-φ・F-T6を接続した不達結果の略称であり、新たな独立前提ではない。全整数n≥25、同じS_n・元操作・NoFlip・厳密順序付き終点(x,y)・原子費用1、q=n+5,c=2,k=1,L=n+7、厳密可換化終点Iの原域で、元成功はない。原guardは展開後の全raw操作列に隣接対(2,3)/(3,2)/(4,5)/(5,4)がないことを指す。共役を消したNielsen部分列のguardへ変更せず、零run・原gap・同gap順序を保持する。原命題と接続は evidence/upstream/k1_nonarrival.md §§2–4。原資料で参照される `inputs/Q_REVIEW.md`、`inputs/PHI_REVIEW.md`、`inputs/T6_REVIEW.md` 等の評価記録全文は、この公開選択には未同梱です。
- K7-Q: 同じn≥25原域のk7全Q解を50条件・588 overlapping liftで必要十分分類。全元非負・予算・分母1/2の整除条件と復号を含む。
- K7-φ: 全588 liftの同じQ域で、第二φ式W₂のσW₂(t)≥C>0を全t_i≥0で与える。実prefix、χ、第二共役actual-z交差項、原ID順、倍率2を保持。λ=(k−1)/6=1。
- 有限域（F-T3 / P7）: d0=4,d1=7,d2=9と3≤n≤24の長さ≤n+7不達。上界Uは全nの[9,3,6,2,2,5,11]++[2]^(n+1)、NoFlip、長さn+8、厳密成功。

参照名の対応：F-T3は0..18の指定有限結果（evidence/upstream/FINITE_RANGE_PROOF.md §4 T3）、P7はq5の有限0..24と上流接続による19..24の距離式（evidence/upstream/cover.md §8 P7）、Uは全nの明示上界（evidence/definitions/Verify/SevenPrefix.lean.txt reaches / word_length）です。原Proof内の「現在」「作者候補」等は執筆時点の記録です。固定依存下の合成、依存自身の確認、後続の判断票を分け、判断票は初回回答保存後に参照します。

P7 / F-T4の歴史的な「既受理」と保存AI評価票の範囲・時点については、初回所見を固定した後に[保存AI評価記録の案内](../../docs/AI_EVALUATION_RECORD_GUIDE.md)を参照します。数学本文と必要前提の開示は、この後読案内とは分けます。

Q積：(a,b,c)(A,B,C)=(a+A,b+B,c+C−bA)。H積：(a,b,c,d)(A,B,C,D)=(a+A,b+B,c+C+aB,d+D+aC+a(a−1)B/2)。φ:x↦hx,y↦hy、ψ:x↦hy,y↦hxという別の群準同型。H.c→Q.cはc_H−abで、φ計算結果の座標交換でψを代用しない。
