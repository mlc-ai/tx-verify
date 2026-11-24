-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.MmaPoll

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Mma
open PTX PTX.Flow PTX.Proof Epilogue

noncomputable section

variable {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m) {g : Nat} {t : TState}
    {F : List (Nat × Value)} (hFresh : ∀ pair ∈ F, pair.1 ≠ 9634 ∧ pair.1 ≠ 9635 ∧ pair.1 ≠ 2537)
    (ht : At t 2141 ((2535, b32 l.sharedBase) :: (2536, b32 0) :: F))
include hp hFresh ht

/-- Before assembling QK0, every MMA lane observes Q stage 0 and the first K ring slot. -/
theorem firstQKWaitsInPrefix {events : List Event} {ending : Option TState}
    (hr : Run kernel Assumptions.all l g t events ending)
    (hLater : ending = none ∨ ∃ later ∈ events, 2145 < later.pc) :
    let q : Bool → Event := fun ok =>
      ⟨2141, .wait ⟨.shared, g / l.block, l.sharedBase⟩ 0 ok true .cta⟩
    let k : Bool → Event := fun ok =>
      ⟨2145, .wait ⟨.shared, g / l.block, l.sharedBase + 32⟩ 0 ok true .cta⟩
    ∃ nq nk u rest,
      events = List.replicate nq (q false) ++ (q true :: List.replicate nk (k false)) ++
        (k true :: rest) ∧
      At u 2148 ((2537, b32 (l.sharedBase + 32)) ::
        (2535, b32 l.sharedBase) :: (2536, b32 0) :: F) ∧
      Run kernel Assumptions.all l g u rest ending := by
  dsimp only
  let G := (2535, b32 l.sharedBase) :: (2536, b32 0) :: F
  have hShared := hp.shared.2.1
  have hAlign := hp.shared.1
  have hBase : l.sharedBase < 2 ^ 32 := by omega
  have hKV : l.sharedBase + 32 < 2 ^ 32 := by omega
  have hQFresh : ∀ pair ∈ G, pair.1 ≠ (waitSite 0).result := by
    simp only [G, waitSite, List.mem_cons]
    rintro pair (rfl | rfl | hm)
    · exact of_decide_eq_true rfl
    · exact of_decide_eq_true rfl
    · exact (hFresh pair hm).1
  obtain ⟨nq, v, mid, hEvents, hv, hMid⟩ :=
    waitTraceInPrefix (phase := 0) 0 hBase (by omega) (by decide) hQFresh
      (by simp [G, waitSite]) (by simp [G, waitSite]) ht hr
    (hLater.imp_right fun ⟨e, he, hSite⟩ => ⟨e, he, by change 2141 < e.pc; omega⟩)
  have hLaterMid : ending = none ∨ ∃ later ∈ mid, 2145 < later.pc := by
    refine hLater.imp_right ?_
    rintro ⟨e, he, hPc⟩
    rw [hEvents] at he
    have hKeep : e ∈ mid := by
      rcases List.mem_append.mp he with hFalse | hTail
      · have hEq := (List.mem_replicate.mp hFalse).2
        rw [hEq] at hPc
        have : 2145 < 2141 := hPc
        omega
      · rcases List.mem_cons.mp hTail with hEq | hSaved
        · rw [hEq] at hPc
          have : 2145 < 2141 := hPc
          omega
        · exact hSaved
    exact ⟨e, hKeep, hPc⟩
  have hMore : mid ≠ [] := by
    intro hNil
    rcases hLaterMid with hEnding | ⟨_, hMem, _⟩
    · rw [hNil, hEnding] at hMid
      cases hMid
    · rw [hNil] at hMem
      cases hMem
  have hKC : Seg kernel [] l g 1 2144 [(2535, b32 l.sharedBase)] 2145
      [(2537, b32 (l.sharedBase + 32))] := by
    intro s hs
    seg_fp hs using norm_bits
  have hV : At v 2144 [(2535, b32 l.sharedBase)] := hv.mono ⟨hv.2.2.2.2.1, trivial⟩
  obtain ⟨w, hLocal, hw'⟩ := hKC v hV
  have hSafe : ∀ pair ∈ G, pair.1 ≠ 2537 := by
    simp only [G, List.mem_cons]
    rintro pair (rfl | rfl | hm)
    · exact of_decide_eq_true rfl
    · exact of_decide_eq_true rfl
    · exact (hFresh pair hm).2.2
  have hCode : ((kernel.code.drop 2144).take 1).all
      (fun ins => (G.map Prod.fst).all (fun r => !(writesRegs ins.op).contains r)) = true := by
    have hSlice : (kernel.code.drop 2144).take 1 = [⟨none, .int {
        op := .add, ty := .int .s 32, sat := false, dsts := [some 2537],
        srcs := [.reg 2535, .imm 32] }⟩] := by
      set_option maxRecDepth 100000 in
      kernel_rfl
    rw [hSlice]
    apply List.all_eq_true.mpr
    intro ins hi
    obtain rfl : ins = _ := List.mem_singleton.mp hi
    apply List.all_eq_true.mpr
    intro r hm
    obtain ⟨pair, hp, rfl⟩ := List.mem_map.mp hm
    simpa [writesRegs] using hSafe pair hp
  have hHeld : Holds w.regs G := by
    apply holdsSchedulerFrame (regs := G.map Prod.fst) hv.2.2.2.2
    · intro r hr
      exact schedulerLocalFrame (lo := 2144) (len := 1) hCode rfl hLocal
        (by rw [hV.1]) (by rw [hV.1]) hr
    · intro pair hm
      exact List.mem_map_of_mem hm
  have hw : At w 2145 ((2537, b32 (l.sharedBase + 32)) :: G) :=
    ⟨hw'.1, hw'.2.1, hw'.2.2.1, hw'.2.2.2.1, hw'.2.2.2.2.1, hHeld⟩
  have hRun := localRun (by decide) (by decide) hv.1 rfl hLocal
  have hKFresh : ∀ pair ∈ ((2537, b32 (l.sharedBase + 32)) :: G),
      pair.1 ≠ (waitSite 1).result := by
    simp only [G, waitSite, List.mem_cons]
    rintro pair (rfl | rfl | rfl | hm)
    · exact of_decide_eq_true rfl
    · exact of_decide_eq_true rfl
    · exact of_decide_eq_true rfl
    · exact (hFresh pair hm).2.1
  obtain ⟨nk, u, rest, hRest, hu, hSuffix⟩ :=
    waitTraceInPrefix (phase := 0) 1 hKV (by omega) (by decide) hKFresh
      (by simp [waitSite]) (by simp [G, waitSite]) hw
      (hMid.after_local_nonempty (run_rtg hRun) hMore) hLaterMid
  refine ⟨nq, nk, u, rest, ?_, hu, hSuffix⟩
  rw [hEvents, hRest]
  simp [waitSite, List.append_assoc]

end
end PTX.Kernels.TmlFa4Fwd.Mma
