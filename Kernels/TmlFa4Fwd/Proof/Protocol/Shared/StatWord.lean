-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.Shared.ShFrame
public import Kernels.TmlFa4Fwd.Proof.Protocol.Credit.Named
public import Lemmas.Protocol.RegionOrder
import Kernels.TmlFa4Fwd.Proof.Correction.Export.StatCount
import Kernels.TmlFa4Fwd.Proof.Protocol.Credit.Handoff
import Kernels.TmlFa4Fwd.Proof.Softmax.Export.StatCount
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The statistics words are ordered

Each word of `[sb + 368, sb + 2416)` is written by one softmax lane and read by the correction lane
of its row. A store of round `G` (the lane's `G`-th arrival on its named barrier follows it) is
before a load after the correction lane's `bar.sync` of ordinal `G` (`stat_wr_rd`); a load whose
last `bar.sync` has an ordinal less than `G` is before the store, through the credit arrival it
precedes and the lane's credit poll (`stat_rd_wr`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow AsyncCopy MbarRing

noncomputable section

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- A byte of a CTA's statistics words. -/
def InStat (L : Launch) (l : Loc) : Prop :=
  l.space = .shared ∧ L.sharedBase + 368 ≤ l.addr ∧ l.addr < L.sharedBase + 2416

section
variable (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow p L X)
include hp hX hFw

/-- **A store and a load of one statistics word are ordered.** -/
theorem stat_wr_rd {h i y j pc pc' : Nat} {a a' : Acc} {bs : List Byte}
    {bs' : List (Option Byte)} (st : Fin 2) (hw : Prologue.warpIndex L h < 8)
    (hy : 8 ≤ Prologue.warpIndex L y) (hy1 : Prologue.warpIndex L y ≤ 11)
    (hc : h / L.block = y / L.block) (hst : Prologue.warpIndex L h / 4 = st.val)
    (hrow : h % L.block % 128 = y % L.block % 128)
    (he : X.get (h, i) = some ⟨pc, .wr a bs⟩) (he' : X.get (y, j) = some ⟨pc', .rd a' bs'⟩)
    (hcnt : barOrd X y j (Prologue.warpIndex L y - 5 + 4 * st.val) =
        arrivals (obj L y (192 + 8 * st.val)) ((X.tr y).take j) + 1) :
    baseCausality L X (h, i) (y, j) ∨ baseCausality L X (y, j) (h, i) := by
  have hst2 := st.isLt
  have hb := hp.block
  obtain ⟨k, hk, hwy, hwh⟩ : ∃ k < 4, Prologue.warpIndex L y = 8 + k ∧
      Prologue.warpIndex L h = k + 4 * st.val := by
    refine ⟨Prologue.warpIndex L y - 8, by omega, by omega, ?_⟩
    simp only [Prologue.warpIndex, hb] at hy hy1 hw hst hrow ⊢
    omega
  have hyl := Frame.lt_of_get hX he'
  have hhl := Frame.lt_of_get hX he
  have hcr := soft_stat_wr hp hX hFw hw he
  have hob : sobj L h 192 = obj L y (192 + 8 * st.val) := by
    rw [sobj, ← obj_cta hc]; congr 1; omega
  rw [hob, show Prologue.warpIndex L h + 3 = statId st.val k by unfold statId; omega] at hcr
  rw [show Prologue.warpIndex L y - 5 + 4 * st.val = statId st.val k by
    unfold statId; omega] at hcnt
  set A := arrivals (obj L y (192 + 8 * st.val)) ((X.tr y).take j) with hA
  set G := ((X.tr h).take i).countP (Execution.isBarId (statId st.val k)) with hG
  obtain ⟨z, pcz, cntz, mz, hzj, hzget, hzo⟩ := exists_bar (X := X) (g := y) (x := j)
    (id := statId st.val k) (c := A) hcnt.ge
  obtain ⟨rfl, hmz⟩ := stat_of_bar hp hX hFw hk hst2 hzget
  obtain rfl : mz = .sync := by
    rcases hmz with ⟨h1, -⟩ | ⟨-, h2⟩
    · omega
    · exact h2
  have hjl := len_of_get he'
  simp only at hjl
  have hpass : z + 1 < (X.tr y).length := by omega
  by_cases hle : G ≤ A
  · left
    obtain ⟨i', pci, hi', hord, -⟩ := stat_rendezvous hp hX hFw hst2 hk hzget hpass hc hwh
    have hii : i < i' := by
      by_contra hcon
      rcases Nat.lt_or_ge i' i with hlt | hge
      · have h1 : barOrd X h (i' + 1) (statId st.val k) ≤ G := by
          unfold barOrd
          exact (List.take_sublist_take_left hlt).countP_le
        have h2 : barOrd X h (i' + 1) (statId st.val k) = barOrd X h i' (statId st.val k) + 1 := by
          unfold barOrd
          rw [List.take_add_one, show (X.tr h)[i']? = _ from hi', Option.toList_some,
            List.countP_append]
          simp [Execution.isBarId]
        omega
      · obtain rfl : i = i' := by omega
        rw [he] at hi'
        cases hi'
    exact (stat_sources hp hX hFw hst2 hk).arrive_sync_baseCausality hX (stat_shape hp hst2 hk)
      ⟨hhl, hyl, hc⟩ hi' hzget hpass hord hii hzj hjl
  · right
    have hil := len_of_get he
    refine (creditHandoff hp hX hFw y st).baseCausality_of_counts (h := h) (g := y) (e := j)
      (f := i) (q := A) ⟨hhl, hc, hw, hst⟩ ?_ hA.ge ?_ hil
    · exact corrLane_of hp rfl ⟨hy, hy1⟩
    · rw [hcr]; omega

/-- **The accesses of the statistics words.** -/
theorem stat_cases {r : Ref} {a : Acc} {w : Bool} {l : Loc} (hi : X.Intent r a w)
    (hc : a.Covers l) (hl : InStat L l) :
    (∃ g k pc bs, r = .thread (g, k) ∧ w = true ∧ Prologue.warpIndex L g < 8 ∧
      X.get (g, k) = some ⟨pc, .wr a bs⟩ ∧ Softmax.StatAt L g a) ∨
    ∃ g k pc bs, r = .thread (g, k) ∧ w = false ∧ 8 ≤ Prologue.warpIndex L g ∧
      Prologue.warpIndex L g ≤ 11 ∧ X.get (g, k) = some ⟨pc, .rd a bs⟩ := by
  obtain ⟨hl0, hl1, hl2⟩ := hl
  have hs : a.loc.space = .shared := hc.1.symm.trans hl0
  obtain ⟨-, -, h1, h2⟩ := id hc
  have hA := sh_intent hp hX hFw hi hs
  have thr : ∀ {g k : Nat}, r = .thread (g, k) → (∃ pc bs, w = true ∧
      X.get (g, k) = some ⟨pc, .wr a bs⟩) ∨ ∃ pc bs, w = false ∧
      X.get (g, k) = some ⟨pc, .rd a bs⟩ := by
    rintro g k rfl
    rcases hi with ⟨bs, ⟨pc, he⟩, rfl⟩ | ⟨bs, ⟨pc, he⟩, rfl⟩ | ⟨o, n, pc, he⟩
    · exact .inr ⟨pc, bs, rfl, he⟩
    · exact .inl ⟨pc, bs, rfl, he⟩
    · exact (no_rmw hX he).elim
  cases hA with
  | statWr hw h =>
    rcases thr rfl with ⟨pc, bs, -, he⟩ | ⟨_, _, h0, -⟩
    · exact .inl ⟨_, _, pc, bs, rfl, rfl, hw, he, h⟩
    · cases h0
  | statRd hw hw1 n st h =>
    rcases thr rfl with ⟨_, _, h0, -⟩ | ⟨pc, bs, -, he⟩
    · cases h0
    · exact .inr ⟨_, _, pc, bs, rfl, rfl, hw, hw1, he⟩
  | allocWr hw h | allocRd hw h =>
    obtain ⟨hz, hl⟩ := h
    rw [hl] at h1 h2; simp only at h1 h2; omega
  | biasRd _ h => obtain ⟨-, -, -, h3, -⟩ := h; omega
  | fstWr _ _ st h => obtain ⟨-, q, -, w, -, hl⟩ := h; rw [hl] at h1; simp only at h1; omega
  | rowCp _ _ h =>
    obtain ⟨i, j, -, hl⟩ := h.dst
    rw [hl] at h1; simp only [Loader.cpAddr] at h1; omega
  | tmaWr _ _ _ _ _ j hlo _ => rcases tload_off_apart j with h | h <;> omega
  | mmaA _ _ _ _ hl => rw [hl] at h1; simp only at h1; omega
  | mmaB _ _ _ _ hl => rw [hl] at h1; simp only at h1; omega
  | storeRd _ _ _ _ st bx _ hlo _ => omega

/-- A store and a load of a common byte. -/
theorem stat_pair {h i y j pc pc' : Nat} {a a' : Acc} {bs : List Byte}
    {bs' : List (Option Byte)} {l : Loc} (hw : Prologue.warpIndex L h < 8)
    (hA : Softmax.StatAt L h a) (hy : 8 ≤ Prologue.warpIndex L y)
    (hy1 : Prologue.warpIndex L y ≤ 11) (he : X.get (h, i) = some ⟨pc, .wr a bs⟩)
    (he' : X.get (y, j) = some ⟨pc', .rd a' bs'⟩) (hl : l.space = .shared)
    (hc : a.Covers l) (hc' : a'.Covers l) :
    baseCausality L X (h, i) (y, j) ∨ baseCausality L X (y, j) (h, i) := by
  obtain ⟨n, st, hz', hl', hcnt⟩ := corr_stat_rd hp hX hFw hy hy1 he' (hc'.1.symm.trans hl)
  obtain ⟨hz, n', hn', hl0⟩ := hA
  have hb := hp.block
  have hst := st.isLt
  have hn := n.isLt
  obtain ⟨-, c2, c3, c4⟩ := hc
  obtain ⟨-, d2, d3, d4⟩ := hc'
  rw [hz] at c4
  rw [hz'] at d4
  rw [hl0] at c2 c3 c4
  rw [hl'] at d2 d3 d4
  simp only [Correction.rowN, Softmax.stN, hb] at c2 c3 c4 d2 d3 d4
  have h8 : h % 512 / 32 < 8 := by
    simpa only [Prologue.warpIndex, hb] using hw
  refine stat_wr_rd hp hX hFw st hw hy hy1 (by rw [hb]; omega) ?_ ?_ he he' hcnt
  · simp only [Prologue.warpIndex, hb]
    split at c3 <;> split at c4 <;> omega
  · rw [hb]
    split at c3 <;> split at c4 <;> omega

omit hp hX hFw in
theorem ev_acc {g k pc : Nat} {a : Acc} {bs : List Byte}
    (he : X.get (g, k) = some ⟨pc, .wr a bs⟩) : (X.get (g, k)).bind Event.acc = some a := by
  rw [he]
  rfl

/-- **The statistics words are ordered.** -/
theorem stat_ordered : ConflictsOrdered L X (InStat L) := by
  intro e f a b l hcon ha hb' hl
  obtain ⟨hne, we, wf, he, hf, hw, -⟩ := hcon
  have hB := hp.block
  rcases stat_cases hp hX hFw he ha hl with ⟨g, k, pc, bs, rfl, rfl, w1, g1, s1⟩ |
    ⟨g, k, pc, bs, rfl, rfl, w1, w1', g1⟩ <;>
  rcases stat_cases hp hX hFw hf hb' hl with ⟨g', k', pc', bs', rfl, rfl, w2, g2, s2⟩ |
    ⟨g', k', pc', bs', rfl, rfl, w2, w2', g2⟩
  · have hgg : g = g' := by
      obtain ⟨hz, n, hn, hl1⟩ := s1
      obtain ⟨hz', n', hn', hl2⟩ := s2
      obtain ⟨-, c2, c3, c4⟩ := ha
      obtain ⟨-, d2, d3, d4⟩ := hb'
      rw [hz] at c4
      rw [hz'] at d4
      rw [hl1] at c2 c3 c4
      rw [hl2] at d2 d3 d4
      simp only [Softmax.stN, hB] at c2 c3 c4 d2 d3 d4
      simp only [Prologue.warpIndex, hB] at w1 w2
      split at c3 <;> split at c4 <;> split at d3 <;> split at d4 <;> omega
    subst hgg
    rcases Nat.lt_trichotomy k k' with h | rfl | h
    · exact .inl (.of_base L (.single (.inl ⟨rfl, h, len_of_get g2,
        fun hs => hs.not_overlap rfl h (ev_acc g1) (ev_acc g2) ⟨l, ha, hb'⟩⟩)))
    · exact (hne rfl).elim
    · exact .inr (.of_base L (.single (.inl ⟨rfl, h, len_of_get g1,
        fun hs => hs.not_overlap rfl h (ev_acc g2) (ev_acc g1) ⟨l, hb', ha⟩⟩)))
  · exact (stat_pair hp hX hFw w1 s1 w2 w2' g1 g2 hl.1 ha hb').imp (.of_base L) (.of_base L)
  · exact (stat_pair hp hX hFw w2 s2 w1 w1' g2 g1 hl.1 hb' ha).symm.imp (.of_base L) (.of_base L)
  · rcases hw with h | h <;> cases h

end

end
end PTX.Kernels.TmlFa4Fwd.Proof
