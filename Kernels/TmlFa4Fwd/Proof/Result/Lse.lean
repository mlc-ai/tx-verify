-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.Epilogue
public import Kernels.TmlFa4Fwd.Proof.CorrectionLseResult
public import Kernels.TmlFa4Fwd.Proof.Thread.ObservationMachine
public import Kernels.TmlFa4Fwd.Proof.EpilogueWarpReady
public import Kernels.TmlFa4Fwd.Proof.OutputAssignedBox
public import Kernels.TmlFa4Fwd.Proof.EpiloguePrefixStartup
public import Kernels.TmlFa4Fwd.Proof.EpilogueCuts
public import Kernels.TmlFa4Fwd.Proof.OutputFrame
public import Kernels.TmlFa4Fwd.Proof.MmaLoopEntryBound
public import Lemmas.Flow.NotClc
public import Lemmas.Step.CtaBar
public import Kernels.TmlFa4Fwd.Proof.SoftmaxLoopEvents
public import Kernels.TmlFa4Fwd.Proof.RoleDispatch
public import Kernels.TmlFa4Fwd.Proof.PrologueDispatchTrace
public import Kernels.TmlFa4Fwd.Proof.PrologueWarp0Prefix
public import Kernels.TmlFa4Fwd.Proof.SoftmaxLoopFlow
public import Kernels.TmlFa4Fwd.Proof.LoaderCountExit
public import Kernels.TmlFa4Fwd.Proof.Thread.DecodedEventFrame
import Kernels.TmlFa4Fwd.Proof.OutputStoreFacts

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Result
open PTX Epilogue Correction

noncomputable section

private theorem packedRowIdentity {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {b b' row row' : Nat} (hb : b < p.batch) (hb' : b' < p.batch)
    (hr : row < p.qLength b) (hr' : row' < p.qLength b')
    (hEq : p.qOffset b + row = p.qOffset b' + row') : b = b' ∧ row = row' := by
  have hMono (i j : Nat) (hij : i ≤ j) (hj : j ≤ p.batch) : p.qOffset i ≤ p.qOffset j := by
    induction j with
    | zero =>
      obtain rfl : i = 0 := by omega
      exact Nat.le_refl _
    | succ j ih =>
      rcases Nat.eq_or_lt_of_le hij with rfl | h
      · exact Nat.le_refl _
      · exact (ih (by omega) (by omega)).trans (hp.lengths j (by omega)).1
  have hEnd := (hp.lengths b hb).1
  have hEnd' := (hp.lengths b' hb').1
  simp only [Params.qLength] at hr hr'
  have hBatch : b = b' := by
    rcases Nat.lt_trichotomy b b' with h | h | h
    · have hs := hMono (b + 1) b' (by omega) hb'.le
      omega
    · exact h
    · have hs := hMono (b' + 1) b (by omega) hb.le
      omega
  subst b'
  exact ⟨rfl, by omega⟩

/-- Every complete LSE byte has a writer. Each covering write supplies the declared value. -/
theorem lseOutputByte {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X) (hComplete : Complete l X)
    (hUsedK : ∀ i < p.batch, ∀ k < 4, ∀ w a bs, X.MemWrites w a bs →
      ¬ a.Covers ((globalLoc (p.usedKBase + 4 * i)).at k))
    (hValues : Correction.LseWriteValues p X)
    {batch head row k : Nat} (hb : batch < p.batch) (hh : head < p.heads)
    (hr : row < p.qLength batch) (hk : k < 4) :
    OutputByte X ((p.lseLoc (p.qOffset batch + row) head).at k)
      ((Value.float .f32 (lse p batch head row)).byteAt k) := by
  refine ⟨lseHasWriter hp hX hComplete hUsedK hb hh hr hk, ?_⟩
  let q := p.qOffset batch + row
  let loc := (p.lseLoc q head).at k
  intro w a bs hw hc
  change a.Covers loc at hc
  have hSpace : a.loc.space = .global := hc.1.symm
  have hq : q < p.totalQ := hp.packedRow_lt hb hr
  rcases Thread.globalWriteSource hX hw.intent hSpace with
    ⟨i, bytes, rfl, hi⟩ | ⟨i, x, y, j, addr, spec, _, hi, hLoc, hSize⟩
  · have hB : bs = bytes := Thread.sameOrdinaryWriteBytes hw hi
    obtain ⟨b', hb', h', hh', r', hr', hAddr, hSize, hValue⟩ := hValues i a bytes hi hSpace
    let k' := loc.addr - a.loc.addr
    have hk' : k' < 4 := by
      have hRange : loc.addr < a.loc.addr + a.size := hc.2.2.2
      dsimp only [k']
      omega
    have hAt : loc = a.loc.at k' := by
      obtain ⟨space, cta, addr⟩ := loc
      rcases a with ⟨⟨baseSpace, baseCTA, baseAddr⟩, _, _, _, _, _, _⟩
      obtain ⟨h₁, h₂, h₃, _⟩ := hc
      change Loc.mk space cta addr = Loc.mk baseSpace baseCTA (baseAddr + k')
      change baseAddr ≤ addr at h₃
      have hK : k' = addr - baseAddr := rfl
      rw [Loc.mk.injEq]
      exact ⟨h₁, h₂, by omega⟩
    have hEq : (p.lseLoc q head).at k = (p.lseLoc (p.qOffset b' + r') h').at k' :=
      hAt.trans (congrArg (fun s => s.at k') hAddr)
    obtain ⟨hRow, rfl, hK⟩ := lseByte_inj hq (hp.packedRow_lt hb' hr') hp.lseStride hk hk' hEq
    obtain ⟨rfl, rfl⟩ := packedRowIdentity hp hb hb' hr hr' hRow
    change bs[k']? = _
    rw [hB, hValue, ← hK]
    have hWidth : (Value.float .f32 (lse p batch head row)).bytes = 4 := rfl
    simp only [Value.toBytes, List.getElem?_map, hWidth, List.getElem?_range hk, Option.map_some]
  · obtain ⟨b, hB, h, hH, tile, stage, box, rfl⟩ :=
      OutputWarp.issuedBox hp hX hi
    rw [Epilogue.writebackWriteLoc hp (g := i.1) (tile := tile) stage box x y j hB hH] at hLoc
    by_cases h : x < 32 ∧ y < 128 ∧ j < 4 ∧ stageRow tile stage + y < p.qLength b
    · rw [ite_eq_left h, Option.some.injEq] at hLoc
      have ho := outputByte_in (hp.packedRow_lt hB h.2.2.2) hH
        (show 32 * box.val + x < 128 by have := box.isLt; omega) h.2.2.1
      have hO : p.oRegion.Contains loc := (Acc.loc_of_one hc hSize) ▸ (hLoc ▸ ho)
      exact (lseByte_apart_output hp hq hh hk hO).elim
    · simp [h] at hLoc

end
end PTX.Kernels.TmlFa4Fwd.Result
