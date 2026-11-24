-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.Values.CorrStore
public import Kernels.TmlFa4Fwd.Proof.Protocol.Credit.Named
public import Kernels.TmlFa4Fwd.Proof.Softmax.Export.MemWrite
public import Kernels.TmlFa4Fwd.Proof.Protocol.P.Rounds
public import Kernels.TmlFa4Fwd.Proof.Correction.Export.StatRound
import Kernels.TmlFa4Fwd.Proof.Correction.Export.StatCount
import Kernels.TmlFa4Fwd.Proof.Protocol.Credit.Handoff
import Kernels.TmlFa4Fwd.Proof.Protocol.Shared.StatWord
import Kernels.TmlFa4Fwd.Proof.Softmax.Export.StatCount
import Kernels.TmlFa4Fwd.Proof.Softmax.Export.StatLast
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The statistics reads return what the softmax lanes stored

A statistics read of correction lane `y` follows a return of its stage's named barrier with
ordinal `A ≥ 1`. The arrival of the row's softmax lane with that ordinal follows a store of the
word (`soft_stat_sum`, `soft_stat_max`); the last such store is the read's source: an earlier
store is hidden by it, and a store after the arrival follows the read (`stat_arrival`). The read
returns its bytes (`stat_source`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Values
open PTX PTX.Proof PTX.Flow AsyncCopy MbarRing TcMma
open PTX.Kernels.TmlFa4Fwd.Proof.Correction (Site)

noncomputable section

/-- The word `n` (the sum or the maximum) of softmax lane `h`'s row. -/
def statLoc (L : Launch) (h n : Nat) : Loc :=
  ⟨.shared, h / L.block,
    L.sharedBase + 368 + 1024 * n + 4 * (128 * Softmax.stN L h + h % L.block % 128)⟩

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- A byte of a read whose writes are its visible write `w`, visible to `w`, or after the read. -/
theorem read_byte_of (hX : Consistent L kernel Assumptions.all m X)
    {e w : AsyncCopy.Ref} {a dst : Acc} {bs : List (Option Byte)}
    {written : List Byte} (he : X.MemReads e a bs) {k : Nat} (hk : k < a.size)
    (hw : X.MemWrites w dst written) (hc : dst.Covers (a.loc.at k))
    (hv : modelCausality L X (a.loc.at k) w e)
    (hlast : ∀ w' dst' bytes, X.MemWrites w' dst' bytes → dst'.Covers (a.loc.at k) →
      w' = w ∨ modelCausality L X (a.loc.at k) w' w ∨ modelCausality L X (a.loc.at k) e w') :
    bs[k]? = some (wbyte dst written (a.loc.at k)) := by
  have hh := hX.hidden e a bs k w dst written he hk hw hc (.direct hv)
  have hrf := (hX.rf e a bs he).2 k hk
  cases hs : X.rf e k with
  | none => simp [hs] at hh
  | some source =>
    rw [hs] at hh hrf
    obtain ⟨dst', bytes, hsource, hcov, hvalue⟩ := hrf
    rcases hlast source dst' bytes hsource hcov with hsame | hbefore | hafter
    · subst source
      obtain ⟨hfp, hbytes⟩ := hw.unique hsource
      rw [hbytes]
      simp only [wbyte, hfp.1]
      exact hvalue
    · exact False.elim (hh (.direct hbefore))
    · exact absurd (.direct hafter) (hX.noFuture e a bs k source he hk hs)

section
variable (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow p L X)
include hp hX hFw

/-- **A statistics read follows its softmax lane's arrival**, and precedes the lane's stores after
it: the lane `h`, its arrival `i'` with the read's ordinal, and the two orders. -/
theorem stat_arrival {y j pc : Nat} {a : Acc} {bs : List (Option Byte)} (hy : y < L.threads)
    (h8 : 8 ≤ Prologue.warpIndex L y) (h12 : Prologue.warpIndex L y < 12)
    (he : X.get (y, j) = some ⟨pc, .rd a bs⟩) {s : Site} {n st : Fin 2}
    (hs : s.statRd = some (n, st)) (hpc : pc = s.pc) :
    ∃ h i' pc' A, h < L.threads ∧ h / L.block = y / L.block ∧ Prologue.warpIndex L h < 8 ∧
      a.size = 4 ∧ a.loc = statLoc L h n.val ∧
      X.get (h, i') = some ⟨pc', .bar (Prologue.warpIndex L h + 3) (some 64) .arrive⟩ ∧
      barOrd X h i' (Prologue.warpIndex L h + 3) = A ∧ 1 ≤ A ∧
      barOrd X y j (Prologue.warpIndex L y - 5 + 4 * st.val) = A + 1 ∧
      (n = 1 → ∃ T, SoftRounds p L h T ∧ A = T) ∧
      (∀ i < i', baseCausality L X (h, i) (y, j)) ∧
      ∀ i pc2 a2 bs2, i' < i → X.get (h, i) = some ⟨pc2, .wr a2 bs2⟩ →
        baseCausality L X (y, j) (h, i) := by
  have hb := hp.block
  have hst2 := st.isLt
  have hn2 := n.isLt
  obtain ⟨hz, hl, A, hA1, hcnt, hmax⟩ := corr_stat_site hp hX hFw h8 (by omega) he hs hpc
  obtain ⟨n', st', -, hl', hcnt'⟩ := corr_stat_rd hp hX hFw h8 (by omega) he (by rw [hl])
  have hst : st' = st := by
    rw [hl] at hl'
    simp only [Loc.mk.injEq, true_and, Correction.rowN] at hl'
    have := st'.isLt
    have := n'.isLt
    refine Fin.ext ?_
    omega
  subst hst
  obtain ⟨k, hk, hwy⟩ : ∃ k < 4, Prologue.warpIndex L y = 8 + k :=
    ⟨Prologue.warpIndex L y - 8, by omega, by omega⟩
  obtain ⟨h, hc, hwh, hrow⟩ : ∃ h, h / L.block = y / L.block ∧
      Prologue.warpIndex L h = k + 4 * st'.val ∧ h % L.block % 128 = y % L.block % 128 := by
    refine ⟨y / 512 * 512 + (32 * (k + 4 * st'.val) + y % 32), ?_, ?_, ?_⟩ <;>
      simp only [Prologue.warpIndex, hb] at hwy ⊢ <;> omega
  have hw : Prologue.warpIndex L h < 8 := by omega
  have hh : h < L.threads := thread_lt_of_cta hy hc
  have hstN : Softmax.stN L h = st'.val := by
    simp only [Prologue.warpIndex, hb] at hwh
    simp only [Softmax.stN, hb]
    split <;> omega
  have hid : Prologue.warpIndex L h + 3 = statId st'.val k := by unfold statId; omega
  have hid' : Prologue.warpIndex L y - 5 + 4 * st'.val = statId st'.val k := by
    unfold statId; omega
  have hord' : barOrd X y j (Prologue.warpIndex L y - 5 + 4 * st'.val) = A + 1 := hcnt
  rw [hid'] at hcnt hcnt'
  have hjl := len_of_get he
  simp only at hjl
  obtain ⟨z, pcz, cntz, mz, hzj, hzget, hzo⟩ := exists_bar (X := X) (g := y) (x := j)
    (id := statId st'.val k) (c := A) hcnt.ge
  obtain ⟨rfl, hmz⟩ := stat_of_bar hp hX hFw hk hst2 hzget
  obtain rfl : mz = .sync := by
    rcases hmz with ⟨h1, -⟩ | ⟨-, h2⟩
    · omega
    · exact h2
  have hpass : z + 1 < (X.tr y).length := by omega
  obtain ⟨i', pci, hi', hord, -⟩ := stat_rendezvous hp hX hFw hst2 hk hzget hpass hc hwh
  refine ⟨h, i', pci, A, hh, hc, hw, hz, ?_, by rw [hid]; exact hi', by rw [hid, hord, hzo], hA1,
    hord', fun hn => ?_, fun i hi => ?_, fun i pc2 a2 bs2 hi he2 => ?_⟩
  · rw [hl, statLoc, hstN, hc, hrow]
  · obtain ⟨R, hR, rfl⟩ := hmax hn
    obtain ⟨r, bal, hP, -⟩ := id hR
    have hT : SoftRounds p L h _ := ⟨r, bal, Epilogue.Picked.cta hc.symm hP, rfl⟩
    exact ⟨_, hT, (hT.corr hp hy hc hR).symm⟩
  · exact (stat_sources hp hX hFw hst2 hk).arrive_sync_baseCausality hX (stat_shape hp hst2 hk)
      ⟨hh, hy, hc⟩ hi' hzget hpass hord hi hzj hjl
  · have hcr := soft_stat_wr hp hX hFw hw he2
    have hob : sobj L h 192 = obj L y (192 + 8 * st'.val) := by
      rw [sobj, ← obj_cta hc]; congr 1; omega
    rw [hob, hid] at hcr
    have hg : A + 1 ≤ ((X.tr h).take i).countP (Execution.isBarId (statId st'.val k)) := by
      have h1 : barOrd X h (i' + 1) (statId st'.val k) ≤ barOrd X h i (statId st'.val k) := by
        unfold barOrd
        exact (List.take_sublist_take_left hi).countP_le
      have h2 : barOrd X h (i' + 1) (statId st'.val k) = barOrd X h i' (statId st'.val k) + 1 := by
        unfold barOrd
        rw [List.take_add_one, show (X.tr h)[i']? = _ from hi', Option.toList_some,
          List.countP_append]
        simp [Execution.isBarId]
      rw [h2, hord, hzo] at h1
      exact h1
    have hil := len_of_get he2
    refine (creditHandoff hp hX hFw y st').baseCausality_of_counts (h := h) (g := y) (e := j)
      (f := i) (q := A) ⟨hh, hc, hw, by omega⟩ ?_ (by omega) (by omega) hil
    exact corrLane_of hp rfl ⟨h8, by omega⟩

omit hFw hp in
/-- **A read whose writes are one visible write, stores before it, or stores after the read**
returns that write's bytes. -/
theorem read_bytes_of {e w : EvId} {a a' : Acc} {bs : List (Option Byte)} {ws : List Byte}
    {pc pcw : Nat} (he : X.get e = some ⟨pc, .rd a bs⟩) (hw : X.get w = some ⟨pcw, .wr a' ws⟩)
    (hloc : a'.loc = a.loc) (hsz : a'.size = a.size) (hlen : ws.length = a.size)
    (hv : baseCausality L X w e)
    (hlast : ∀ k < a.size, ∀ w' dst' bytes, X.MemWrites w' dst' bytes →
      dst'.Covers (a.loc.at k) → w' = .thread w ∨ modelCausality L X (a.loc.at k) w' (.thread w) ∨
        modelCausality L X (a.loc.at k) (.thread e) w') : bs = ws.map some := by
  have hr : X.MemReads (.thread e) a bs := .inl ⟨pc, he⟩
  have hwr : X.MemWrites (.thread w) a' ws := .inl ⟨pcw, hw⟩
  have hbl : bs.length = a.size := (hX.rf _ a bs hr).1
  apply List.ext_getElem?
  intro k
  by_cases hk : k < a.size
  · have hcov : a'.Covers (a.loc.at k) := by
      rw [← hloc]
      exact Acc.covers_at (by omega)
    rw [read_byte_of hX hr hk hwr hcov (.of_base L hv) (hlast k hk)]
    simp only [wbyte, hloc, Loc.at, Nat.add_sub_cancel_left, List.getElem?_map,
      List.getElem?_eq_getElem (show k < ws.length by omega), Option.map_some]
  · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by simp; omega)]

/-- **A statistics read's source**: a store of the same word by its softmax lane, causally before
the read, whose bytes the read returns. -/
theorem stat_source {y j pc : Nat} {a : Acc} {bs : List (Option Byte)}
    (hy : y < L.threads) (h8 : 8 ≤ Prologue.warpIndex L y) (h12 : Prologue.warpIndex L y < 12)
    (he : X.get (y, j) = some ⟨pc, .rd a bs⟩) {s : Site} {n st : Fin 2}
    (hs : s.statRd = some (n, st)) (hpc : pc = s.pc) :
    ∃ h i pcw aw ws, Prologue.warpIndex L h < 8 ∧ h / L.block = y / L.block ∧
      X.get (h, i) = some ⟨pcw, .wr aw ws⟩ ∧ aw.loc = statLoc L h n.val ∧
      baseCausality L X (h, i) (y, j) ∧ (ws.length = 4 → bs = ws.map some) ∧
      h < L.threads ∧ aw.size = 4 ∧ aw.loc = a.loc ∧
      barOrd X h i (Prologue.warpIndex L h + 3) + 1 =
        barOrd X y j (Prologue.warpIndex L y - 5 + 4 * st.val) ∧
      ∀ w' dst' bytes k, k < 4 → X.MemWrites w' dst' bytes → dst'.Covers (a.loc.at k) →
        w' = .thread (h, i) ∨ modelCausality L X (a.loc.at k) w' (.thread (h, i)) ∨
          modelCausality L X (a.loc.at k) (.thread (y, j)) w' := by
  classical
  have hb := hp.block
  have hn2 := n.isLt
  obtain ⟨h, i', pc', A, hh, hc, hw, hz, hl, hi', hA, hA1, hyj, hmax, hbef, haft⟩ :=
    stat_arrival hp hX hFw hy h8 h12 he hs hpc
  have hex : StatBefore L X h i' n.val := by
    rcases (show n = 0 ∨ n = 1 by fin_cases n <;> simp) with rfl | rfl
    · exact soft_stat_sum hp hX hFw hw hi' (by unfold barOrd at hA; omega)
    · obtain ⟨T, hT, rfl⟩ := hmax rfl
      exact soft_stat_max hp hX hFw hw hi' hT hA
  let Q : Nat → Prop := fun i => i < i' ∧ ∃ pc a bs, X.get (h, i) = some ⟨pc, .wr a bs⟩ ∧
    a.size = 4 ∧ a.loc = statLoc L h n.val
  obtain ⟨i0, hi0, pc0, a0, bs0, hg0, hz0, hl0, hb0⟩ := hex
  have hQ0 : Q i0 := ⟨hi0, pc0, a0, bs0, hg0, hz0, hl0⟩
  have hspec : Q (Nat.findGreatest Q i') := Nat.findGreatest_spec hi0.le hQ0
  have hgr : ∀ i, Q i → i ≤ Nat.findGreatest Q i' := fun i hi => Nat.le_findGreatest hi.1.le hi
  generalize Nat.findGreatest Q i' = i at hspec hgr
  have hi0i := hgr i0 hQ0
  obtain ⟨hii, pcw, aw, ws, hgw, hzw, hlw⟩ := hspec
  have hla : aw.loc = a.loc := by rw [hlw, hl]
  have hord : barOrd X h i (Prologue.warpIndex L h + 3) = A := by
    have h1 : barOrd X h i0 (Prologue.warpIndex L h + 3) ≤
        barOrd X h i (Prologue.warpIndex L h + 3) :=
      (List.take_sublist_take_left hi0i).countP_le
    have h2 : barOrd X h i (Prologue.warpIndex L h + 3) ≤
        barOrd X h i' (Prologue.warpIndex L h + 3) :=
      (List.take_sublist_take_left hii.le).countP_le
    change barOrd X h i0 _ = barOrd X h i' _ at hb0
    omega
  suffices hlast : ∀ w' dst' bytes k, k < 4 → X.MemWrites w' dst' bytes →
      dst'.Covers (a.loc.at k) → w' = .thread (h, i) ∨
        modelCausality L X (a.loc.at k) w' (.thread (h, i)) ∨
        modelCausality L X (a.loc.at k) (.thread (y, j)) w' from
    ⟨h, i, pcw, aw, ws, hw, hc, hgw, hlw, hbef i hii, fun hlen => read_bytes_of hX he hgw hla
      (by omega) (by omega) (hbef i hii) fun k hk w' dst' bytes hw' hcov =>
        hlast w' dst' bytes k (by omega) hw' hcov, hh, hzw, hla, by omega, hlast⟩
  intro w' dst' bytes k hk hw' hcov
  have hin : InStat L (a.loc.at k) := by
    have hst : Softmax.stN L h ≤ 1 := by unfold Softmax.stN; split <;> omega
    have hr : h % L.block % 128 < 128 := Nat.mod_lt _ (by decide)
    rw [hl]
    simp only [InStat, statLoc, Loc.at]
    refine ⟨trivial, by omega, by omega⟩
  rcases stat_cases hp hX hFw hw'.intent hcov hin with
    ⟨g, k2, pc2, bs2, rfl, -, w2, g2, s2⟩ | ⟨g, k2, pc2, bs2, -, h0, -⟩
  swap
  · cases h0
  obtain ⟨hz2, n2, hn2', hl2⟩ := s2
  obtain ⟨hgh, hnn⟩ : g = h ∧ n2 = n.val := by
    obtain ⟨-, d2, d3, d4⟩ := hcov
    rw [hl2] at d2 d3 d4
    rw [hl] at d2 d3 d4
    rw [hz2] at d4
    have hstN : ∀ u : Nat, (u % 512 / 32 ≤ 3 ∧ Softmax.stN L u = 0) ∨
        (3 < u % 512 / 32 ∧ Softmax.stN L u = 1) := by
      intro u
      simp only [Softmax.stN, hb]
      split <;> omega
    have e1 := hstN g
    have e2 := hstN h
    simp only [statLoc, Loc.at, hb] at d2 d3 d4
    simp only [Prologue.warpIndex, hb] at hw w2
    constructor <;> omega
  subst hgh hnn
  rcases Nat.lt_trichotomy k2 i with hlt | rfl | hgt
  · right; left
    refine .of_base L (.single (.inl ⟨rfl, hlt, len_of_get hgw, fun hso =>
      hso.not_overlap rfl hlt (ev_acc g2) (ev_acc hgw) ⟨a.loc.at k, hcov, ?_⟩⟩))
    have : aw.loc = a.loc := by rw [hlw, hl]
    rw [← this]
    exact Acc.covers_at (by omega)
  · exact .inl rfl
  · right; right
    refine .of_base L ?_
    rcases Nat.lt_trichotomy k2 i' with h1 | rfl | h1
    · exact absurd (hgr k2 ⟨h1, pc2, dst', bs2, g2, hz2, hl2⟩) (by omega)
    · rw [g2] at hi'; cases hi'
    · exact haft k2 pc2 dst' bs2 h1 g2

end

end
end PTX.Kernels.TmlFa4Fwd.Proof.Values
