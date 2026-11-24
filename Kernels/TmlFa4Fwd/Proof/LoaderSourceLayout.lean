-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderRecurringSources
public import Kernels.TmlFa4Fwd.Proof.LoaderPrimingKSource

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Flow PTX.Proof

noncomputable section

/-- The source layout selected by a recurring packet's decoded K/V role. -/
def recurringCache (p : Params) (i : Fin 4) : CacheLayout :=
  if i.val % 2 = 0 then p.kLayout else p.vLayout

private theorem recurringCacheRegion {p : Params} (i : Fin 4) :
    (recurringCache p i).region p.pages p.kvHeads ∈ p.inputRegions := by
  unfold recurringCache
  split <;> simp [Params.inputRegions]

/-- A verified saved row pointer leads to the physical K/V layout coordinate in
the first observed copy pair, for either half of the BF16 row. -/
theorem recurringFirstCopySourceLayoutFromSavedRow {p : Params} {l : Launch} {m : Mem0}
    (hp : Pre p l m)
    {g batch head row tid : Nat} (hb : batch < p.batch) (hh : head < p.kvHeads)
    (hTid : tid < 512) (i : Fin 4) (upper : Bool) {s : TState}
    {es : List Event} {vs : List Visit} {sp : AsyncCopy.Spec} :
    let base := ((recurringCache p i).loc (primingScratchPage p batch row) head (row % 16) 0).addr
    At s (recurringSourceStart i) (recurringSourceInputs i base tid) →
    Walk kernel Assumptions.all l g s es vs →
    ⟨packetPlanePc (recurringPacketSite i) 0 upper, .copy sp⟩ ∈
      loaderSliceEvents (recurringSourceStart i) (copyCommitPc (recurringPacketSite i)) vs →
    sp.src.loc = (recurringCache p i).loc (primingScratchPage p batch row)
      head (row % 16) (kvCopyColumn tid upper) := by
  let c := recurringCache p i
  let page := primingScratchPage p batch row
  let base := (c.loc page head (row % 16) 0).addr
  let loc := c.loc page head (row % 16) (kvCopyColumn tid upper)
  change At s _ (recurringSourceInputs i base tid) → _ → _ →
    sp.src.loc = loc
  intro hs hw hSeen
  have hPage := primingScratchPageBound hp (row := row) hb
  have hMem := recurringCacheRegion (p := p) i
  have hRange := hp.ranges (c.region p.pages p.kvHeads) (by simp [c, hMem])
  have hReg : (c.region p.pages p.kvHeads).Contains loc := by
    have hRow : row % 16 < 16 := Nat.mod_lt _ (by decide)
    have hCol := kvCopyColumn_byte_lt (lane := tid) upper (byte := 0) (by decide)
    simpa [loc, Loc.at] using
      (CacheLayout.loc_copy_in_region (c := c) hPage hh hRow hCol)
  have hAddr : loc.addr < 2 ^ 64 := by
    obtain ⟨_, _, _, hEnd⟩ := hReg
    exact hEnd.trans_le hRange
  have hSum : base + 16 * (tid % 8) + packetSrcOff upper = loc.addr := by
    cases upper <;> simp [base, loc, page, c, CacheLayout.loc,
      kvCopyColumn, packetSrcOff, globalLoc] <;> omega
  have hBase : base < 2 ^ 64 := by omega
  rw [recurringFirstCopySource hBase hTid i upper hs hw hSeen, hSum, Nat.mod_eq_of_lt hAddr]
  rfl

end
end PTX.Kernels.TmlFa4Fwd.Loader
