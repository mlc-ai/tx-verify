-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Coord.Observe
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Dequant.Observe
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Mbar.FaultQuery
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Mbar.FaultScore
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Mbar.FaultTma
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Raw.Observe
public import Lemmas.Protocol.GatedFaults
public import Lemmas.Protocol.KindRingGate

@[expose] public section

/-! # No record of an mbarrier object faults

The eleven families of the kernel's objects (`MbarFam`) are of three kinds, and each is
fault-free by the gates of its ring or by the counts of its one lane: the tensor-copy objects
`qTma`, `rawReady` (`qTma_fault`, `rawReady_fault`), the unit objects `lastStoreDone`,
`dequantReady`, `rawFree`, `coordReady`, `coordFree`, `soReady` and the commit objects `qUtccp`,
`qkDone`, `svDone`. One dispatch over the family (`mbar_fault`) gives every object of every
CTA. -/

/-! # The dequantized buffer ring's barriers do not fault

`dequantReady s` is a unit object of the 128 dequant lanes: a lane's arrival of use `t ≥ 1` has
`t + 1` successful polls of `svDone s` before it (`dequant_readyArr`), so by the ring's gate
(`KRing.gateF`) it follows the MMA lane's poll of `dequantReady s` with `t - 1` earlier ones
(`Unit.gated_of_paths`, `Unit.Obj.fault_free`). -/

/-! # The raw ring's barriers do not fault

`rawReady s` is a `TmaUnits` object of the TMA lane (`rawReady_fault`). `rawFree s` is a unit
object of the 128 dequant lanes: a lane's arrival of use `t ≥ 1` has `t + 1`
successful polls of `rawReady s` before it (`RawInputs.deqArr`), so by the ring's gate
(`KRing.gateE`) it follows the TMA lane's poll of `rawFree s` with `t` earlier ones. -/

/-! # The index ring's barriers do not fault

`coordReady s` and `coordFree s` are unit objects (of the 32 index lanes and of the 129
consumers). An arrival of use `t ≥ 1` has `t + 1` successful polls of the other barrier before it
(`CoordInputs.idxArr`, `consArr`), so by the ring's gates (`KRing.gateF`, `gateE`) it follows the
other side's poll of its own barrier. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow PTX.MbarRing PTX.AsyncCopy

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

section
variable (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow P L X)
  (hR : MbarRows P L X) (hI : InitRows L X) (hB : Bar0Rows L X) (hN : CoordInputs L X)
include hp hX hFw hR hI hB hN

/-- **No record of `coordReady s` faults.** -/
theorem coordReady_fault (c : Nat) (s : Fin 4) :
    ∀ r ∈ X.objects (mbarLoc L c (.coordReady s)), r.fault = none := by
  refine (coordReady_obj hp hX hFw hR hI hB c s).fault_free hX
    (Unit.gated_of_paths (K := kernel) (A := Assumptions.all) fun {a i pc sc} he hpos => ?_)
  have hn := hN.idxArr he
  refine ⟨coordCons L X c 0, ?_⟩
  have h := (coordSlot hp hX hFw hR hI hB hN c s).gateF hX (a := a) (i := i)
    (u := arrivals (mbarLoc L c (.coordReady s)) ((X.tr (idxLane L c a)).take i) - 1)
    (len_of_get he) (by simp only [coordSlot]; omega) 0
  simpa only [coordSlot, Nat.add_zero] using h

/-- **No record of `coordFree s` faults.** -/
theorem coordFree_fault (c : Nat) (s : Fin 4) :
    ∀ r ∈ X.objects (mbarLoc L c (.coordFree s)), r.fault = none := by
  refine (coordFree_obj hp hX hFw hR hI hB hN.tmaOne c s).fault_free hX
    (Unit.gated_of_paths (K := kernel) (A := Assumptions.all) fun {a i pc sc} he hpos => ?_)
  have hn := hN.consArr he
  refine ⟨idxLane L c 0, ?_⟩
  have h := (coordSlot hp hX hFw hR hI hB hN c s).gateE hX (b := a) (i := i)
    (t := arrivals (mbarLoc L c (.coordFree s)) ((X.tr (coordCons L X c a)).take i) - 1 + 1)
    (len_of_get he) (by simp only [coordSlot]; omega) (by omega) 0
  simpa only [coordSlot] using h

end

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow PTX.MbarRing PTX.AsyncCopy

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

section
variable (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow P L X)
  (hR : MbarRows P L X) (hI : InitRows L X) (hB : Bar0Rows L X) (hN : RawInputs L X)
include hp hX hFw hR hI hB hN

/-- **No record of `rawFree s` faults.** -/
theorem rawFree_fault (c : Nat) (s : Fin 2) :
    ∀ r ∈ X.objects (mbarLoc L c (.rawFree s)), r.fault = none := by
  refine (rawFree_obj hp hX hFw hR hI hB c s).fault_free hX
    (Unit.gated_of_paths (K := kernel) (A := Assumptions.all) fun {a i pc sc} he hpos => ?_)
  have hn := hN.deqArr he
  refine ⟨tmaThread L X c, ?_⟩
  have h := (rawSlot hp hX hFw hR hI hB hN c s).gateE hX (b := a) (i := i)
    (t := arrivals (mbarLoc L c (.rawFree s)) ((X.tr (deqLane L c a)).take i) - 1 + 1)
    (len_of_get he) (by simp only [rawSlot]; omega) (by omega) 0
  simpa only [rawSlot] using h

/-- **No record of `rawReady s` faults**: the TMA lane's items, gated by its polls of `rawFree s`
(`tma_fault_ring`). -/
theorem rawReady_fault (c : Nat) (s : Fin 2) :
    ∀ r ∈ X.objects (mbarLoc L c (.rawReady s)), r.fault = none :=
  tma_fault_ring hX (rawReady_obj hp hX hFw hR hI hB hN.tmaOne c s) (by decide) (by decide)
    (rawSlot hp hX hFw hR hI hB hN c s) rfl rfl rfl rfl (fun he => hN.tmaArr he)
    (fun he hm => hN.tmaIss he hm)

end

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow PTX.MbarRing PTX.AsyncCopy

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

section
variable (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow P L X)
  (hR : MbarRows P L X) (hI : InitRows L X) (hB : Bar0Rows L X) (hN : DequantInputs L X)
include hp hX hFw hR hI hB hN

/-- **No record of `dequantReady s` faults.** -/
theorem dequantReady_fault (c : Nat) (s : Fin 2) :
    ∀ r ∈ X.objects (mbarLoc L c (.dequantReady s)), r.fault = none := by
  refine (dequantReady_obj hp hX hFw hR hI hB c s).fault_free hX
    (Unit.gated_of_paths (K := kernel) (A := Assumptions.all) fun {a i pc sc} he hpos => ?_)
  have hn := dequant_readyArr hp hX hFw (deqLane_warp hp c a) he
  refine ⟨mmaLane L X c, ?_⟩
  have h := (dqSlot hp hX hFw hR hI hB hN c s).gateF hX (a := a) (i := i)
    (u := arrivals (mbarLoc L c (.dequantReady s)) ((X.tr (deqLane L c a)).take i) - 1)
    (len_of_get he) (by simp only [dqSlot]; omega) 0
  simpa only [dqSlot, Nat.add_zero] using h

end

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **No record of an object of a family faults.** -/
theorem mbar_fault (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hR : MbarRows P L X) (hI : InitRows L X) (hB : Bar0Rows L X)
    (hN : DequantInputs L X) (hRaw : RawInputs L X) (hCo : CoordInputs L X) (c : Nat)
    (f : MbarFam) : ∀ r ∈ X.objects (mbarLoc L c f), r.fault = none := by
  cases f with
  | lastStoreDone => exact lastStore_fault hp hX hFw hR hI hB c
  | qTma => exact qTma_fault hp hX hFw hR hI hB c
  | qUtccp => exact qUtccp_fault hp hX hFw hR hI hB c
  | dequantReady s => exact dequantReady_fault hp hX hFw hR hI hB hN c s
  | rawReady s => exact rawReady_fault hp hX hFw hR hI hB hRaw c s
  | rawFree s => exact rawFree_fault hp hX hFw hR hI hB hRaw c s
  | coordReady s => exact coordReady_fault hp hX hFw hR hI hB hCo c s
  | coordFree s => exact coordFree_fault hp hX hFw hR hI hB hCo c s
  | qkDone s => exact qkDone_fault hp hX hFw hR hI hB c s
  | soReady s => exact soReady_fault hp hX hFw hR hI hB c s
  | svDone s => exact svDone_fault hp hX hFw hR hI hB hN c s

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
