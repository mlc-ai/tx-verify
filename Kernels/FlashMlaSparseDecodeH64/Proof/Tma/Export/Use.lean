-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MemRows.Tma
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.GatherVocab
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.CoordLoad
import Kernels.FlashMlaSparseDecodeH64.Proof.Tma.ClsRd
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Where
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.TmaLane
import Kernels.FlashMlaSparseDecodeH64.Proof.Tma.CoordLoc
import Kernels.FlashMlaSparseDecodeH64.Proof.Tma.ObjCnt
import Kernels.FlashMlaSparseDecodeH64.Proof.Tma.RefStep

@[expose] public section

/-! # The use of a coordinate read

The per-use index of the TMA lane's coordinate reads (the ring region `tmaCoord`): a read of block
`r` is a word of slot `s = r % 4` (`Tma.crd_loc`, as in `MemRow.TmaRd`), after the block's
successful poll of `coordReady s` and before its arrival on `coordFree s` (stage 2 of the block),
so the lane has made `u + 1` successful polls of `coordReady s` and `u = r / 4` arrivals on
`coordFree s` (`tma_rdUse`; the read is past the election, so the lane is the CTA's TMA thread),
read off the reference invariant's counts (`Tma.tcnt_ready`,
`Tma.tcnt_cfree`) and the ledger's (`lane5_okPolls`, `lane5_arrivals`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- The conclusion of `tma_rdUse`. -/
def TmaRdUse (L : Launch) (X : Execution) (g k : Nat) (a : Acc) : Prop :=
  ∃ s : Fin 4, (∃ q < 16, ∃ j < 4, MemRow.WsAcc L (g / L.block)
      (221728 + 256 * s.val + 16 * q + 4 * j) 4 a) ∧
    ∃ u, okPolls (mbarLoc L (g / L.block) (.coordReady s)) ((X.tr g).take k) = u + 1 ∧
      arrivals (mbarLoc L (g / L.block) (.coordFree s)) ((X.tr g).take k) = u

/-- A coordinate read at stage 2 of block `r`, at the block's slot. -/
private theorem rd_use (hp : Pre P L m) {g k pc r rd gs j : Nat} {d : Tma.D} {a : Acc}
    {bs : List (Option Byte)} (hj : j < 4) (hslot : d.slot = W (r % 4))
    (hn : ∀ c, c ≠ .ub →
      ((X.tr g).take k).countP (Tma.cls c) = Tma.cntAt (Tma.objs L g) 3 r 2 rd gs false c)
    (hP : ∀ l, okPolls l ((X.tr g).take k) = ((X.tr g).take k).countP (Tma.cls (.acq l)))
    (hA : ∀ l, arrivals l ((X.tr g).take k) = ((X.tr g).take k).countP (Tma.cls (.arrive l)))
    (q : Fin 16) (h : RdAt L g (Tma.crdB L d) (Tma.coordOff q) 4 j ⟨pc, .rd a bs⟩) :
    TmaRdUse L X g k a := by
  rcases h with ⟨a', bs', hk, hl, hsz⟩ | ⟨f, hf⟩
  · cases hk
    have hr4 : r % 4 < 4 := Nat.mod_lt _ (by decide)
    refine ⟨⟨r % 4, hr4⟩, ⟨q.val, q.isLt, j, hj, ?_, hsz⟩, r / 4, ?_, ?_⟩
    · rw [hl, Tma.crd_loc hp hr4 hslot q]
      simp only [wsLoc, Loc.at, Loc.mk.injEq, true_and]
      omega
    · show okPolls (MbarRow.loc L g (.coordReady ⟨r % 4, hr4⟩)) _ = _
      rw [hP, hn _ (by simp), Tma.tcnt_ready hp]
      simp only [Tma.useAt, Tma.ind, ringUses_here rfl hr4]
      simp
    · show arrivals (MbarRow.loc L g (.coordFree ⟨r % 4, hr4⟩)) _ = _
      rw [hA, hn _ (by simp), Tma.tcnt_cfree hp]
      exact ringUses_here rfl hr4
  · cases hf

/-- A coordinate read is past the election. -/
private theorem pc_gt {pc : Nat} {q : Fin 16} (h : pc = Tma.coordPc q) : 2165 < pc := by
  rw [h]
  unfold Tma.coordPc
  split_ifs <;> omega

/-- **The use of a coordinate read**: a shared read of the TMA lane is a word of a slot `s`, with
`u + 1` successful polls of `coordReady s` and `u` arrivals on `coordFree s` before it. -/
theorem tma_rdUse (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {g k pc : Nat} {a : Acc} {bs : List (Option Byte)}
    (he : X.get (g, k) = some ⟨pc, .rd a bs⟩) (hat : MbarRow.TmaAt L g pc) :
    2165 < pc ∧ TmaRdUse L X g k a := by
  obtain ⟨-, hr⟩ := hat
  obtain ⟨d, hR, -, ⟨hpc, hE⟩, hl, hw⟩ := tma_at hp hX hFw he (fun _ h => by cases h) hr
  have hc := hR (lane5_take_noUb hX he)
  have hP := lane5_okPolls hp hX hFw hw k
  have hA := lane5_arrivals hp hX hFw hw k
  tma_state d
  cases s with
  | coord0 q =>
    obtain ⟨⟨-, -, -, -, -, -, hslot, -⟩, hn⟩ := (Tma.core_loop rfl).mp hc
    exact ⟨pc_gt hpc, rd_use hp (by decide) hslot hn hP hA q hE⟩
  | coord1 q =>
    obtain ⟨⟨-, -, -, -, -, -, hslot, -⟩, hn⟩ := (Tma.core_loop rfl).mp hc
    exact ⟨pc_gt hpc, rd_use hp (by decide) hslot hn hP hA q hE⟩
  | coord2 q =>
    obtain ⟨⟨-, -, -, -, -, -, hslot, -⟩, hn⟩ := (Tma.core_loop rfl).mp hc
    exact ⟨pc_gt hpc, rd_use hp (by decide) hslot hn hP hA q hE⟩
  | coord3 q =>
    obtain ⟨⟨-, -, -, -, -, -, hslot, -⟩, hn⟩ := (Tma.core_loop rfl).mp hc
    exact ⟨pc_gt hpc, rd_use hp (by decide) hslot hn hP hA q hE⟩
  | _ =>
    simp [Tma.EvK, Tma.Poll] at hE
    all_goals exact absurd rfl (hl _)


/-- A coordinate read at stage 2 of block `r`: its place among the reads and its slot word. -/
private theorem rd_blk (hp : Pre P L m) {g k pc r rd gs j : Nat} {d : Tma.D} {a : Acc}
    {bs : List (Option Byte)} (hslot : d.slot = W (r % 4))
    (hn : ∀ c, c ≠ .ub →
      ((X.tr g).take k).countP (Tma.cls c) = Tma.cntAt (Tma.objs L g) 3 r 2 rd gs false c)
    (hP : ∀ l, okPolls l ((X.tr g).take k) = ((X.tr g).take k).countP (Tma.cls (.acq l)))
    (q : Fin 16) (hrd : rd = 4 * q.val + j)
    (h : RdAt L g (Tma.crdB L d) (Tma.coordOff q) 4 j ⟨pc, .rd a bs⟩) :
    ((X.tr g).take k).countP tmaRd = 64 * r + 4 * q.val + j ∧
      MemRow.WsAcc L (g / L.block) (221728 + 256 * (r % 4) + 16 * q.val + 4 * j) 4 a ∧
      okPolls (mbarLoc L (g / L.block) (.coordReady (MbarRow.slot4 r))) ((X.tr g).take k) =
        r / 4 + 1 := by
  rcases h with ⟨a', bs', hk, hl, hsz⟩ | ⟨f, hf⟩
  · cases hk
    have hr4 : r % 4 < 4 := Nat.mod_lt _ (by decide)
    refine ⟨?_, ⟨?_, hsz⟩, ?_⟩
    · have := hn .rd (by simp)
      rw [show Tma.cls .rd = tmaRd from funext Tma.cls_rd] at this
      rw [this]
      simp only [Tma.cntAt, Tma.proCnt, Tma.loopCnt, Bool.false_eq_true, ↓reduceIte]
      omega
    · rw [hl, Tma.crd_loc hp hr4 hslot q]
      simp only [wsLoc, Loc.at, Loc.mk.injEq, true_and]
      omega
    · show okPolls (MbarRow.loc L g (.coordReady ⟨r % 4, hr4⟩)) _ = _
      rw [hP, hn _ (by simp), Tma.tcnt_ready hp]
      simp only [Tma.useAt, Tma.ind, ringUses_here rfl hr4]
      simp
  · cases hf

/-- **The block of a coordinate read**: the read is word `j` of quadruple `q` of block `r`, the
`64 r + 4 q + j`-th read of the lane, at the quadruple's load pc, in the block's ring slot. -/
theorem tma_rdBlock (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {g k pc : Nat} {a : Acc} {bs : List (Option Byte)}
    (he : X.get (g, k) = some ⟨pc, .rd a bs⟩) (hat : MbarRow.TmaAt L g pc) :
    ∃ r q j, q < 16 ∧ j < 4 ∧ pc = coordLoadPc q ∧
      ((X.tr g).take k).countP tmaRd = 64 * r + 4 * q + j ∧
      MemRow.WsAcc L (g / L.block) (221728 + 256 * (r % 4) + 16 * q + 4 * j) 4 a ∧
      okPolls (mbarLoc L (g / L.block) (.coordReady (MbarRow.slot4 r))) ((X.tr g).take k) =
        r / 4 + 1 := by
  obtain ⟨-, hr⟩ := hat
  obtain ⟨d, hR, -, ⟨hpc, hE⟩, hl, hw⟩ := tma_at hp hX hFw he (fun _ h => by cases h) hr
  have hc := hR (lane5_take_noUb hX he)
  have hP := lane5_okPolls hp hX hFw hw k
  tma_state d
  have hpcq : ∀ q : Fin 16, pc = Tma.coordPc q → pc = coordLoadPc q.val := fun q h => by
    rw [h]; simp only [Tma.coordPc, coordLoadPc]
  cases s with
  | coord0 q =>
    obtain ⟨⟨-, -, -, -, -, -, hslot, -⟩, hn⟩ := (Tma.core_loop rfl).mp hc
    obtain ⟨h1, h2, h3⟩ := rd_blk hp hslot hn hP q (by simp [Tma.Site.rdN]) hE
    exact ⟨_, q.val, 0, q.isLt, by decide, hpcq q hpc, h1, h2, h3⟩
  | coord1 q =>
    obtain ⟨⟨-, -, -, -, -, -, hslot, -⟩, hn⟩ := (Tma.core_loop rfl).mp hc
    obtain ⟨h1, h2, h3⟩ := rd_blk hp hslot hn hP q (by simp [Tma.Site.rdN]) hE
    exact ⟨_, q.val, 1, q.isLt, by decide, hpcq q hpc, h1, h2, h3⟩
  | coord2 q =>
    obtain ⟨⟨-, -, -, -, -, -, hslot, -⟩, hn⟩ := (Tma.core_loop rfl).mp hc
    obtain ⟨h1, h2, h3⟩ := rd_blk hp hslot hn hP q (by simp [Tma.Site.rdN]) hE
    exact ⟨_, q.val, 2, q.isLt, by decide, hpcq q hpc, h1, h2, h3⟩
  | coord3 q =>
    obtain ⟨⟨-, -, -, -, -, -, hslot, -⟩, hn⟩ := (Tma.core_loop rfl).mp hc
    obtain ⟨h1, h2, h3⟩ := rd_blk hp hslot hn hP q (by simp [Tma.Site.rdN]) hE
    exact ⟨_, q.val, 3, q.isLt, by decide, hpcq q hpc, h1, h2, h3⟩
  | _ =>
    simp [Tma.EvK, Tma.Poll] at hE
    all_goals exact absurd rfl (hl _)

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
