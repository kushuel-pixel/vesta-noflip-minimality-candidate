# 依存interface（判断ラベルを与えない契約表）

各契約を仮定した合成の妥当性と、契約自身の原証拠の十分性を区別して所見を出す。原証拠はINDEX.mdおよびFILE_INDEX.jsonの相対path・hash指定から必要箇所だけ読む。

- F-T1: 全n∈Nat、NoFlip厳密成功、L≤n+7 ⇒ q=n+3又はn+5。
- F-0: 共役0回のNoFlip列で可換化終点IならQ中心終端(n²+1,n)、全nで不達。
- F-T2: n≥3、一共役の成功 ⇒ q≥3n+1、L≥3n+2。全8共役・両符号。
- F-T4: 全n≥3、NoFlip、L≤n+7、q=n+3の元成功なし。A一般域n≥19/有限3..18、B有限3..5/B009 n≥6を使う。B009は同じnの短literal B母域の最短成功からCORE成功代表を得る存在保存でありraw全列等式分類ではない。
- P1/P2: q=n+5、厳密SL₂積T_n=[[-n,1],[-1,0]]の全骨格をk1:204/k7:347の551語形で被覆。k=#ID3/4は1又は7。
- P3: 二共役を全原gap、同gap・同slot、零run、event0→event1の順でliteral復号。run指数は非負fragment和。n=m+Σu−5、支持内u=1+x・支持外0、Σx≥30−m−|S|、xは非負整数。
- K1-Q: n≥25,q=n+5,c=2,k=1,L=n+7,I,raw guardの元Q解を39列+二分割族G_r/G_sで必要十分分類。全0≤a≤n、六境界を含む。K1-φでは同原域の通過列はR19/21/22/13/14=F1/2/3/4/5と原列一致。F-T6はこの五族のψ像不一致を全n≥1で与える。
- K7-Q: 同じn≥25原域のk7全Q解を50条件・588 overlapping liftで必要十分分類。全元非負・予算・分母1/2の整除条件と復号を含む。
- K7-φ: 全588 liftの同じQ域で、第二φ式W₂のσW₂(t)≥C>0を全t_i≥0で与える。実prefix、χ、第二共役actual-z交差項、原ID順、倍率2を保持。λ=(k−1)/6=1。
- 有限域（F-T3 / P7）: d0=4,d1=7,d2=9と3≤n≤24の長さ≤n+7不達。上界Uは全nの[9,3,6,2,2,5,11]++[2]^(n+1)、NoFlip、長さn+8、厳密成功。

参照名の対応：F-T3は0..18の指定有限結果（evidence/upstream/FINITE_RANGE_PROOF.md §4 T3）、P7はq5の有限0..24と上流接続による19..24の距離式（evidence/upstream/cover.md §8 P7）、Uは全nの明示上界（evidence/definitions/Verify/SevenPrefix.lean.txt reaches / word_length）です。原Proof内の「現在」「作者候補」等は執筆時点の記録です。固定依存下の合成、依存自身の確認、後続の判断票を分け、判断票は初回回答保存後に参照します。

Q積：(a,b,c)(A,B,C)=(a+A,b+B,c+C−bA)。H積：(a,b,c,d)(A,B,C,D)=(a+A,b+B,c+C+aB,d+D+aC+a(a−1)B/2)。φ:x↦hx,y↦hy、ψ:x↦hy,y↦hxという別の群準同型。H.c→Q.cはc_H−abで、φ計算結果の座標交換でψを代用しない。
