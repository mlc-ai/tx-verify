-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsMmaPolls
public import Kernels.FlashAttn4Fwd.Proof.Interface.Cover
public import Lemmas.Flow.CountWindow

@[expose] public section

/-! # The MMAs of a thread, by their count

An MMA of the MMA thread is numbered by its count of earlier MMAs, `32 n i + 8 (blk b t) + j`
(`MmaSt.mmas`), and the number decodes the item `i`, the block `b`, the trip `t` and the step `j`
(`Mma.num_decode`). So the thread made the MMA of every smaller number before it
(`mma_at_val`), and the QK MMAs of stage `st` after as many S-full commits as an MMA of step `j`
are the `j` MMAs before it in its block: `qkStep` is `j` (`qkStep_eq`); the PV MMAs after as
many P-ready polls likewise (`pvStep_eq`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Proof PTX.Flow TcMma

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

namespace Mma

/-- A number below `n` past a multiple of `n` decodes. -/
theorem mul_add_inj {n i i' x x' : Nat} (hx : x < n) (hx' : x' < n)
    (he : n * i + x = n * i' + x') : i = i' ∧ x = x' := by
  have h1 : (n * i + x) / n = i := by
    rw [Nat.mul_add_div (by omega), Nat.div_eq_of_lt hx, Nat.add_zero]
  have h2 : (n * i' + x') / n = i' := by
    rw [Nat.mul_add_div (by omega), Nat.div_eq_of_lt hx', Nat.add_zero]
  have hi : i = i' := by rw [← h1, ← h2, he]
  subst hi
  exact ⟨rfl, by omega⟩

/-- **The MMA number decodes.** -/
theorem num_decode {n i i' t t' j j' : Nat} {b b' : Fin 8} (hn : 1 ≤ n) (h : TripAt n b t)
    (h' : TripAt n b' t') (hj : j < 8) (hj' : j' < 8)
    (he : 32 * n * i + 8 * blk b t + j = 32 * n * i' + 8 * blk b' t' + j') :
    i = i' ∧ b = b' ∧ t = t' ∧ j = j' := by
  have hb := blk_lt hn h
  have hb' := blk_lt hn h'
  obtain ⟨rfl, hx⟩ := mul_add_inj (n := 32 * n) (x := 8 * blk b t + j)
    (x' := 8 * blk b' t' + j') (by omega) (by omega) (by rw [← Nat.add_assoc, he, Nat.add_assoc])
  have hbe : blk b t = blk b' t' := by omega
  obtain ⟨rfl, rfl⟩ := blk_inj h h' hbe
  exact ⟨rfl, rfl, rfl, by omega⟩

theorem sv_own_lt {n t : Nat} {b : Fin 8} (hp : isPv b = false) (h : TripAt n b t) (hn : 1 ≤ n) :
    sv (mmaStage b) b t < n := by
  unfold TripAt at h
  fin_cases b <;> simp [isPv] at hp <;> simp [sv, mmaStage] at h ⊢ <;> omega

/-- The S-full count of a QK MMA of its own stage decodes the item, the block and the trip. -/
theorem qk_inj {n i i' t t' : Nat} {b b' : Fin 8} (hn : 1 ≤ n) (hp : isPv b = false)
    (hp' : isPv b' = false) (hs : mmaStage b = mmaStage b') (h : TripAt n b t)
    (h' : TripAt n b' t')
    (he : n * i + sv (mmaStage b) b t = n * i' + sv (mmaStage b') b' t') :
    i = i' ∧ b = b' ∧ t = t' := by
  obtain ⟨hi, hv⟩ := mul_add_inj (sv_own_lt hp h hn) (sv_own_lt hp' h' hn) he
  refine ⟨hi, ?_⟩
  unfold TripAt at h h'
  fin_cases b <;> fin_cases b' <;> simp [isPv] at hp hp' <;>
    simp [sv, mmaStage] at hs hv h h' ⊢ <;> omega

theorem pv_own {t : Nat} {b : Fin 8} (hp : isPv b = true) : pv (mmaStage b) b t = 1 + t :=
  (pv_le hp t).2.2.2

/-- The P-ready count of a PV MMA of its own stage decodes the item, the block and the trip. -/
theorem pv_inj {n i i' t t' : Nat} {b b' : Fin 8} (hn : 1 ≤ n) (hp : isPv b = true)
    (hp' : isPv b' = true) (hs : mmaStage b = mmaStage b') (h : TripAt n b t)
    (h' : TripAt n b' t')
    (he : n * i + pv (mmaStage b) b t = n * i' + pv (mmaStage b') b' t') :
    i = i' ∧ b = b' ∧ t = t' := by
  rw [pv_own hp, pv_own hp'] at he
  have ht : t < n := by unfold TripAt at h; split_ifs at h <;> omega
  have ht' : t' < n := by unfold TripAt at h'; split_ifs at h' <;> omega
  obtain ⟨hi, hv⟩ := mul_add_inj (n := n) (i := i) (i' := i') (x := t) (x' := t') ht ht'
    (by omega)
  subst hv
  refine ⟨hi, ?_, rfl⟩
  unfold TripAt at h h'
  fin_cases b <;> fin_cases b' <;> simp [isPv] at hp hp' <;>
    simp [mmaStage] at hs h h' ⊢ <;> omega

end Mma

namespace MmaSt

variable {g k : Nat} {d : Mma.D} {b j : Fin 8}

/-- One state at an event. -/
theorem unique {d' : Mma.D} {b' j' : Fin 8} (h : MmaSt L X g k d b j)
    (h' : MmaSt L X g k d' b' j') : d = d' ∧ b = b' ∧ j = j' := by
  have hs := h.state.symm.trans h'.state
  simp only [Option.some.injEq, Sum.inr.injEq, Role.mma.injEq] at hs
  subst hs
  have := h.site.symm.trans h'.site
  simp only [Mma.Site.mma.injEq] at this
  exact ⟨rfl, this⟩

theorem get (h : MmaSt L X g k d b j) :
    ∃ e, X.get (g, k) = some e ∧ Mma.isMma e = true := by
  obtain ⟨pc, he⟩ := h.issue
  exact ⟨_, he, rfl⟩

/-- A later event follows more MMAs. -/
theorem count_lt (h : MmaSt L X g k d b j) {k' : Nat} (hk : k < k') :
    ((X.tr g).take k).countP Mma.isMma < ((X.tr g).take k').countP Mma.isMma := by
  obtain ⟨e, he, hm⟩ := h.get
  have h1 := countP_take_succ he hm
  have h2 := countP_take_mono Mma.isMma (X.tr g) (show k + 1 ≤ k' by omega)
  omega

end MmaSt

variable (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
include hpre hX

/-- An MMA event's state. -/
theorem mmaSt_of_get (ht : Frame.Tracked (code L) X) {g k : Nat} {e : Event}
    (he : X.get (g, k) = some e) (hm : Mma.isMma e = true) : ∃ d b j, MmaSt L X g k d b j := by
  obtain ⟨pc, kd⟩ := e
  unfold Mma.isMma at hm
  split at hm
  · rename_i dd s acc mask heq
    simp only at heq
    subst heq
    obtain ⟨d, b, j, h, -⟩ := mmaSt_of hpre hX ht (g := g) (k := k) ⟨pc, he⟩
    exact ⟨d, b, j, h⟩
  · cases hm

/-- **The MMA of a smaller number**: a thread with more than `c` MMAs before event `K` made the
MMA of number `c` before `K`, at its item, block, trip and step. -/
theorem mma_at_val (ht : Frame.Tracked (code L) X) {g K i t jj : Nat} {b : Fin 8}
    (htrip : Mma.TripAt (Mma.trips L) b t) (hj : jj < 8)
    (hK : 32 * Mma.trips L * i + 8 * Mma.blk b t + jj + 1 ≤ ((X.tr g).take K).countP Mma.isMma) :
    ∃ k < K, ∃ d, MmaSt L X g k d b ⟨jj, hj⟩ ∧ d.i = i ∧ d.t = t := by
  obtain ⟨k, e, hk, he, hm, hc⟩ := exists_nthEv hK
  obtain ⟨d, b', j', h⟩ := mmaSt_of_get hpre hX ht he hm
  rw [h.mmas] at hc
  obtain ⟨hi, rfl, htt, hjj⟩ := Mma.num_decode (trips_pos hpre) h.tripAt htrip j'.isLt hj hc
  obtain rfl : j' = ⟨jj, hj⟩ := Fin.ext hjj
  exact ⟨k, hk, d, h, hi, htt⟩

/-- A QK MMA of stage `st`, as an MMA state. -/
theorem qkAt_iff (ht : Frame.Tracked (code L) X) {g st k : Nat} (hst : st < 2) :
    QkAt X g st k ↔ ∃ d b j, MmaSt L X g k d b j ∧ Mma.isPv b = false ∧
      (Mma.mmaStage b).val = st := by
  constructor
  · rintro ⟨⟨dd, s, acc, mask, hi⟩, hc⟩
    obtain ⟨d, b, j, h, -⟩ := mmaSt_of hpre hX ht hi
    exact ⟨d, b, j, h, (h.inS_iff hst).mp hc⟩
  · rintro ⟨d, b, j, h, hp⟩
    exact ⟨⟨_, _, _, _, h.issue⟩, (h.inS_iff hst).mpr hp⟩

/-- A PV MMA of stage `st`, as an MMA state. -/
theorem pvAt_iff (ht : Frame.Tracked (code L) X) {g st k : Nat} :
    PvAt X g st k ↔ ∃ d b j, MmaSt L X g k d b j ∧ Mma.isPv b = true ∧
      (Mma.mmaStage b).val = st := by
  constructor
  · rintro ⟨⟨dd, s, acc, mask, hi⟩, hc⟩
    obtain ⟨d, b, j, h, -⟩ := mmaSt_of hpre hX ht hi
    exact ⟨d, b, j, h, h.inO_iff.mp hc⟩
  · rintro ⟨d, b, j, h, hp⟩
    exact ⟨⟨_, _, _, _, h.issue⟩, h.inO_iff.mpr hp⟩

omit hpre hX in
/-- The positions below `k` of the thread's MMAs, by their numbers. -/
theorem any_isMma_iff {g n : Nat} :
    ((X.tr g)[n]?).any Mma.isMma = true ↔ ∃ e, X.get (g, n) = some e ∧ Mma.isMma e = true := by
  show ((X.tr g)[n]?).any Mma.isMma = true ↔ ∃ e, (X.tr g)[n]? = some e ∧ Mma.isMma e = true
  cases (X.tr g)[n]? <;> simp

/-- **The K step of a QK MMA** is its step in its block. -/
theorem qkStep_eq (ht : Frame.Tracked (code L) X) {g k : Nat} {d : Mma.D} {b j : Fin 8}
    (h : MmaSt L X g k d b j) (hp : Mma.isPv b = false) :
    qkStep L X g (Mma.mmaStage b) k = j.val := by
  have hn := trips_pos hpre
  set M := ((X.tr g).take k).countP Mma.isMma with hM
  have hMv : M = 32 * Mma.trips L * d.i + 8 * Mma.blk b d.t + j.val := h.mmas
  have key : ∀ n, n < k →
      ((QkAt X g (Mma.mmaStage b) n ∧
        sCommits L X g (Mma.mmaStage b) n = sCommits L X g (Mma.mmaStage b) k) ↔
      (((X.tr g)[n]?).any Mma.isMma = true ∧
        M - j.val ≤ ((X.tr g).take n).countP Mma.isMma)) := by
    intro n hnk
    constructor
    · rintro ⟨hq, hs⟩
      obtain ⟨d', b', j', h', hp', hst'⟩ := (qkAt_iff hpre hX ht (Mma.mmaStage_lt b)).mp hq
      have hst : Mma.mmaStage b' = Mma.mmaStage b := Fin.ext hst'
      rw [h'.sCommits, h.sCommits] at hs
      obtain ⟨hi, hb, htt⟩ := Mma.qk_inj hn hp' hp hst h'.tripAt h.tripAt (by rw [hst]; exact hs)
      subst b'
      refine ⟨any_isMma_iff.mpr h'.get, ?_⟩
      have hlt := h'.count_lt hnk
      rw [h'.mmas, ← hM, hMv, hi, htt] at hlt
      rw [h'.mmas, hMv, hi, htt]
      omega
    · rintro ⟨hm, hge⟩
      obtain ⟨e, he, hme⟩ := any_isMma_iff.mp hm
      obtain ⟨d', b', j', h'⟩ := mmaSt_of_get hpre hX ht he hme
      have hlt := h'.count_lt hnk
      rw [← hM] at hlt
      rw [h'.mmas] at hlt hge
      obtain ⟨x, hx⟩ : ∃ x, 32 * Mma.trips L * d'.i + 8 * Mma.blk b' d'.t + j'.val =
          M - j.val + x := ⟨_, (Nat.add_sub_cancel' hge).symm⟩
      have hx8 : x < 8 := by omega
      obtain ⟨hi, hb, htt, -⟩ := Mma.num_decode (i := d'.i) (i' := d.i) hn h'.tripAt h.tripAt
        j'.isLt hx8
        (by omega)
      subst b'
      refine ⟨(qkAt_iff hpre hX ht (Mma.mmaStage_lt b)).mpr ⟨d', b, j', h', hp, rfl⟩, ?_⟩
      rw [h'.sCommits, h.sCommits, hi, htt]
  have hw := card_window (X.tr g) Mma.isMma (M - j.val) k
  unfold qkStep
  rw [show j.val = ((X.tr g).take k).countP Mma.isMma - (M - j.val) by omega, ← hw]
  congr 1
  ext n
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨fun ⟨h1, h2⟩ => ⟨h1, (key n h1).mp h2⟩, fun ⟨h1, h2⟩ => ⟨h1, (key n h1).mpr h2⟩⟩

/-- **The K step of a PV MMA** is its step in its block. -/
theorem pvStep_eq (ht : Frame.Tracked (code L) X) {g k : Nat} {d : Mma.D} {b j : Fin 8}
    (h : MmaSt L X g k d b j) (hp : Mma.isPv b = true) :
    pvStep L X g (Mma.mmaStage b) k = j.val := by
  have hn := trips_pos hpre
  set M := ((X.tr g).take k).countP Mma.isMma with hM
  have hMv : M = 32 * Mma.trips L * d.i + 8 * Mma.blk b d.t + j.val := h.mmas
  have key : ∀ n, n < k →
      ((PvAt X g (Mma.mmaStage b) n ∧
        pPolls L X g (Mma.mmaStage b) n = pPolls L X g (Mma.mmaStage b) k) ↔
      (((X.tr g)[n]?).any Mma.isMma = true ∧
        M - j.val ≤ ((X.tr g).take n).countP Mma.isMma)) := by
    intro n hnk
    constructor
    · rintro ⟨hq, hs⟩
      obtain ⟨d', b', j', h', hp', hst'⟩ := (pvAt_iff hpre hX ht).mp hq
      have hst : Mma.mmaStage b' = Mma.mmaStage b := Fin.ext hst'
      rw [h'.pPolls, h.pPolls] at hs
      obtain ⟨hi, hb, htt⟩ := Mma.pv_inj hn hp' hp hst h'.tripAt h.tripAt (by rw [hst]; exact hs)
      subst b'
      refine ⟨any_isMma_iff.mpr h'.get, ?_⟩
      have hlt := h'.count_lt hnk
      rw [h'.mmas, ← hM, hMv, hi, htt] at hlt
      rw [h'.mmas, hMv, hi, htt]
      omega
    · rintro ⟨hm, hge⟩
      obtain ⟨e, he, hme⟩ := any_isMma_iff.mp hm
      obtain ⟨d', b', j', h'⟩ := mmaSt_of_get hpre hX ht he hme
      have hlt := h'.count_lt hnk
      rw [← hM] at hlt
      rw [h'.mmas] at hlt hge
      obtain ⟨x, hx⟩ : ∃ x, 32 * Mma.trips L * d'.i + 8 * Mma.blk b' d'.t + j'.val =
          M - j.val + x := ⟨_, (Nat.add_sub_cancel' hge).symm⟩
      have hx8 : x < 8 := by omega
      obtain ⟨hi, hb, htt, -⟩ := Mma.num_decode (i := d'.i) (i' := d.i) hn h'.tripAt h.tripAt
        j'.isLt hx8
        (by omega)
      subst b'
      refine ⟨(pvAt_iff hpre hX ht).mpr ⟨d', b, j', h', hp, rfl⟩, ?_⟩
      rw [h'.pPolls, h.pPolls, hi, htt]
  have hw := card_window (X.tr g) Mma.isMma (M - j.val) k
  unfold pvStep
  rw [show j.val = ((X.tr g).take k).countP Mma.isMma - (M - j.val) by omega, ← hw]
  congr 1
  ext n
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨fun ⟨h1, h2⟩ => ⟨h1, (key n h1).mp h2⟩, fun ⟨h1, h2⟩ => ⟨h1, (key n h1).mpr h2⟩⟩

end
end PTX.Kernels.FlashAttn4Fwd.Proof
