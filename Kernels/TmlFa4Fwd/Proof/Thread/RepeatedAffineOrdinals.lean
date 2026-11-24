-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.RepeatedScoreRoundProgress
public import Kernels.TmlFa4Fwd.Proof.Thread.RepeatedStatisticsProgress
public import Lemmas.Order.WarpBarOrdinal
public import Lemmas.Order.ElectOrdinal
import all Kernels.TmlFa4Fwd.Proof.Thread.Softmax
import Lemmas.Flow.CountTake

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Flow PTX.Proof Correction Thread.Scores

private theorem tcAndOtherCount (xs : List Event) :
    xs.countP isTcColl + xs.countP (fun e => !isTcColl e) = xs.length := by
  induction xs with
  | nil => rfl
  | cons e es ih =>
    cases h : isTcColl e <;> simp only [List.countP_cons,h,
      Bool.not_false,Bool.not_true,Bool.false_eq_true,ite_false,ite_true,List.length_cons] <;> omega

/-- The interval across the actual score packing cursor contains only TMEM collectives. -/
theorem PackedScorePrefix.keepsOtherCount {l : Launch} {X : Execution} {g n : Nat}
    {mode : Repeated} {stage : Fin 2} {F : List (Nat × Value)}
    {input : OpeningTripCursor l X g (scorePc mode.round 0) F}
    (c : PackedScorePrefix l X g mode stage n input) (test : Event → Bool)
    (hTest : ∀ e, test e = true → isTcColl e = false) :
    ((X.tr g).take c.cursor.pos).countP test = ((X.tr g).take input.pos).countP test := by
  have hPre := tcAndOtherCount ((X.tr g).take input.pos)
  have hPost := tcAndOtherCount ((X.tr g).take c.cursor.pos)
  simp only [List.length_take,Nat.min_eq_left input.bounded] at hPre
  simp only [List.length_take,Nat.min_eq_left c.cursor.bounded] at hPost
  have hOther : ((X.tr g).take c.cursor.pos).countP (fun e => !isTcColl e) =
      ((X.tr g).take input.pos).countP (fun e => !isTcColl e) := by
    have hTc := c.ordinal
    have hPos := c.position
    omega
  have hLe : input.pos ≤ c.cursor.pos := c.position.symm ▸ Nat.le_add_right _ _
  have hSub := countP_take_sub_le (p := test) (q := fun e => !isTcColl e)
    (fun e he => by rw [hTest e he]; rfl) (X.tr g) hLe
  have hNat := countP_take_mono test (X.tr g) hLe
  omega

/-- A reached rescale store and named statistics notice leave the three warp
collective ordinals unchanged in both repeated modes. -/
theorem repeatedStatisticsKeepOrdinals
    {X : Execution} {g pos : Nat} (mode : Repeated) {a : Acc} {data : List Byte}
    (hStore : StatisticsStore X (g,pos) (rescaleStore (mode = .biased)) a data)
    (hNotice : Publishes X (g,pos+1) (if mode = .biased then .biased else .plain)) :
    ((X.tr g).take (pos+2)).countP isTcColl = ((X.tr g).take pos).countP isTcColl ∧
      warpBars X g (pos+2) = warpBars X g pos ∧ elections X g (pos+2) = elections X g pos := by
  obtain ⟨e,he,hKind⟩ := hNotice
  obtain ⟨_,id,cnt,hm⟩ := noticeSite hKind
  have hGet : X.get (g,pos+1) = some ⟨e.pc,.bar id cnt .arrive⟩ := by
    obtain ⟨pc,kind⟩ := e
    change kind = .bar id cnt .arrive at hm
    subst kind
    exact he
  have hStep (test : Event → Bool)
      (hW : test ⟨(statsStore (rescaleStore (mode = .biased))).pc,.wr a data⟩ = false)
      (hBar : test ⟨e.pc,.bar id cnt .arrive⟩ = false) :
      ((X.tr g).take (pos+2)).countP test = ((X.tr g).take pos).countP test := by
    exact (countP_take_succ_false hGet hBar).trans (countP_take_succ_false hStore hW)
  exact ⟨hStep _ rfl rfl,hStep _ rfl rfl,hStep _ rfl rfl⟩

/-- The scalar rescale write leaves the abstract warp's statistics ordinal
unchanged up to its immediately following arrival. -/
theorem statisticsNoticeRankAfterStore
    {X : Execution} {g pos : Nat} (mode : Repeated) {a : Acc} {data : List Byte}
    (hStore : StatisticsStore X (g,pos) (rescaleStore (mode = .biased)) a data) :
    (before X (g,pos+1)).notices = (before X (g,pos)).notices := by
  simp only [beforeNotices]
  exact countP_take_succ_false hStore rfl

end PTX.Kernels.TmlFa4Fwd.Softmax
