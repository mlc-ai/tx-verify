-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.MmaWaitCursor
public import Kernels.TmlFa4Fwd.Proof.MmaTripEntry
public import Kernels.TmlFa4Fwd.Proof.MmaPoll
public import Kernels.TmlFa4Fwd.Proof.EpilogueWarpAlignment
public import Kernels.TmlFa4Fwd.Flow.Code.Part032

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Mma
open PTX PTX.Flow PTX.Proof

noncomputable section

private theorem signedWord {n : Nat} (h : n < 2 ^ 31) :
    toSigned 32 (BitVec.ofNat 64 n) = (n : Int) := by
  simp only [toSigned, toNat_ofNat_lt (show n < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show n < 2 ^ 32 by omega), ite_eq_left h]

/-- The selected batch's cuQ pointer is computed with the decoded signed wide multiply. -/
theorem selectedTripPointer {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    (g : Nat) {batch tile : Nat} (hb : batch < p.batch) :
    Seg kernel Assumptions.all l g 3 2109
      [(7203, b32 batch), (7502, b64 p.cuQBase), (7503, b64 p.usedKBase),
        (7202, b32 (256 * (tile + 1))), (2535, b32 l.sharedBase)]
      2112 (tripReadEntry p l batch tile) := by
  have hRange := hp.ranges ⟨p.cuQBase, 4 * (p.batch + 1)⟩ (by simp [Params.inputRegions])
  change p.cuQBase + 4 * (p.batch + 1) ≤ 2 ^ 64 at hRange
  have hb31 : batch < 2 ^ 31 := by have := hp.shape.2.1; omega
  have hb32 : batch < 2 ^ 32 := by omega
  have hBase : p.cuQBase < 2 ^ 64 := by omega
  have hOff : 4 * batch < 2 ^ 64 := by omega
  have ha : p.cuQBase + 4 * batch < 2 ^ 64 := by omega
  have hFour : toSigned 32 (truncBits 32 (BitVec.ofInt 64 4)) = 4 := rfl
  have hWide : (batch : Int) * 4 = ((4 * batch : Nat) : Int) := by
    push_cast
    omega
  have hSeg : Seg kernel [] l g 3 2109
      [(7203, b32 batch), (7502, b64 p.cuQBase), (7503, b64 p.usedKBase),
        (7202, b32 (256 * (tile + 1))), (2535, b32 l.sharedBase)]
      2112 (tripReadEntry p l batch tile) := by
    intro t ht
    unfold tripReadEntry
    seg_fp ht using
      simp only [b64, kind_s_beq_s, ↓reduceIte, Nat.reduceMul, truncBits_ofNat hb32 (by decide),
        signedWord hb31, hFour, hWide, BitVec.ofInt_natCast,
        truncBits_ofNat hOff (by decide), truncBits_ofNat hBase (by decide),
        ← BitVec.ofNat_add, truncBits_ofNat ha (by decide)]
  intro t ht
  obtain ⟨u, hu, hU⟩ := hSeg t ht
  exact ⟨u, localRun (by decide) (by decide) ht.1 (by
    set_option maxRecDepth 100000 in kernel_rfl) hu, hU⟩

/-- The actual selected-request reads, trip count, and initial Q0/K0 waits reach the first
descriptor assembly. The returned trace position includes all failed wait attempts. -/
theorem firstQKFromSelectedInPrefix {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g pos batch tile : Nat} (hb : batch < p.batch) (htile : 256 * tile < p.qLength batch)
    {t : TState} {ending : Option TState} (ht : At t 2109
      [(7203, b32 batch), (7502, b64 p.cuQBase), (7503, b64 p.usedKBase),
        (7202, b32 (256 * (tile + 1))), (2535, b32 l.sharedBase)])
    (hCuQ : ∀ lane ≤ 1, ∀ k < 4, ∀ w a bs, X.MemWrites w a bs →
      ¬ a.Covers ((globalLoc (p.cuQBase + 4 * (batch + lane))).at k))
    (hUsedK : ∀ k < 4, ∀ w a bs, X.MemWrites w a bs →
      ¬ a.Covers ((globalLoc (p.usedKBase + 4 * batch)).at k))
    (hr : Run kernel Assumptions.all l g t ((X.tr g).drop pos) ending)
    (hDemand : Loader.PrefixDemand X g pos 2145 ending) :
    0 < trips p batch tile ∧
      ∃ nq nk u, X.get (g, pos + 3 + nq) =
        some ⟨2141, .wait ⟨.shared, g / l.block, l.sharedBase⟩ 0 true true .cta⟩ ∧
        X.get (g, pos + 3 + nq + 1 + nk) =
          some ⟨2145, .wait ⟨.shared, g / l.block, l.sharedBase + 32⟩ 0 true true .cta⟩ ∧
        At u 2148 [(2537, b32 (l.sharedBase + 32)), (2535, b32 l.sharedBase), (2536, b32 0),
          (1189, b32 (trips p batch tile))] ∧
        Run kernel Assumptions.all l g u ((X.tr g).drop (pos + 3 + nq + 1 + nk + 1)) ending := by
  obtain ⟨r, hLocal, hR⟩ := selectedTripPointer hp g hb t ht
  obtain ⟨hTrip, v, hv, hV, hAfter⟩ :=
    trackToFirstQPollInPrefix hp hX hb htile hR hCuQ hUsedK
      (hr.after_local_nonempty (run_rtg hLocal) (hDemand.nonempty hr)) hDemand
  have hLater : ending = none ∨ ∃ later ∈ (X.tr g).drop (pos + 3), 2145 < later.pc := by
    refine hAfter.imp_right ?_
    rintro ⟨j, later, hBefore, hSite, hGet⟩
    refine ⟨later, ?_, hSite⟩
    apply List.mem_of_getElem? (i := j - (pos + 3))
    rwa [List.getElem?_drop, Nat.add_sub_of_le hBefore]
  let F := [(1189, b32 (trips p batch tile))]
  have hFresh : ∀ pair ∈ F, pair.1 ≠ 9634 ∧ pair.1 ≠ 9635 ∧ pair.1 ≠ 2537 := by
    intro pair hm
    rcases List.mem_singleton.mp hm with rfl
    exact of_decide_eq_true rfl
  obtain ⟨nq, nk, u, rest, hEvents, hu, hRest⟩ :=
    firstQKWaitsInPrefix hp (g := g) (F := F) hFresh hv hV hLater
  let q : Bool → Event := fun ok =>
    ⟨2141, .wait ⟨.shared, g / l.block, l.sharedBase⟩ 0 ok true .cta⟩
  let k : Bool → Event := fun ok =>
    ⟨2145, .wait ⟨.shared, g / l.block, l.sharedBase + 32⟩ 0 ok true .cta⟩
  change (X.tr g).drop (pos + 3) =
    List.replicate nq (q false) ++ (q true :: List.replicate nk (k false)) ++ (k true :: rest)
    at hEvents
  refine ⟨hTrip, nq, nk, u, ?_, ?_, hu, ?_⟩
  · change (X.tr g)[pos + 3 + nq]? = some (q true)
    rw [← List.getElem?_drop, hEvents, List.append_assoc,
      List.getElem?_append_right (by simp)]
    simp
  · change (X.tr g)[pos + 3 + nq + 1 + nk]? = some (k true)
    rw [show pos + 3 + nq + 1 + nk = pos + 3 + (nq + 1 + nk) by omega, ← List.getElem?_drop,
      hEvents, List.getElem?_append_right (by simp [Nat.add_assoc, Nat.add_comm 1])]
    simp [Nat.add_assoc, Nat.add_comm 1]
  · have hDrop : (X.tr g).drop (pos + 3 + nq + 1 + nk + 1) = rest := by
      rw [show pos + 3 + nq + 1 + nk + 1 = pos + 3 + (nq + 1 + nk + 1) by omega,
        ← List.drop_drop, hEvents]
      have hLen : (List.replicate nq (q false) ++ (q true :: List.replicate nk (k false))).length =
          nq + 1 + nk := by simp [Nat.add_assoc, Nat.add_comm 1]
      rw [← hLen, ← List.drop_drop, List.drop_append_length]
      rfl
    exact hDrop.symm ▸ hRest

/-- Recover initial Q0/K0 polling on a terminated MMA trace. -/
theorem firstQKFromSelected {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g pos batch tile : Nat} (hb : batch < p.batch) (htile : 256 * tile < p.qLength batch)
    {t : TState} (ht : At t 2109
      [(7203, b32 batch), (7502, b64 p.cuQBase), (7503, b64 p.usedKBase),
        (7202, b32 (256 * (tile + 1))), (2535, b32 l.sharedBase)])
    (hCuQ : ∀ lane ≤ 1, ∀ k < 4, ∀ w a bs, X.MemWrites w a bs →
      ¬ a.Covers ((globalLoc (p.cuQBase + 4 * (batch + lane))).at k))
    (hUsedK : ∀ k < 4, ∀ w a bs, X.MemWrites w a bs →
      ¬ a.Covers ((globalLoc (p.usedKBase + 4 * batch)).at k))
    (hr : Run kernel Assumptions.all l g t ((X.tr g).drop pos) none) :
    0 < trips p batch tile ∧
      ∃ nq nk u, X.get (g, pos + 3 + nq) =
        some ⟨2141, .wait ⟨.shared, g / l.block, l.sharedBase⟩ 0 true true .cta⟩ ∧
        X.get (g, pos + 3 + nq + 1 + nk) =
          some ⟨2145, .wait ⟨.shared, g / l.block, l.sharedBase + 32⟩ 0 true true .cta⟩ ∧
        At u 2148 [(2537, b32 (l.sharedBase + 32)), (2535, b32 l.sharedBase), (2536, b32 0),
          (1189, b32 (trips p batch tile))] ∧
        Run kernel Assumptions.all l g u ((X.tr g).drop (pos + 3 + nq + 1 + nk + 1)) none :=
  firstQKFromSelectedInPrefix hp hX hb htile ht hCuQ hUsedK hr (.inl rfl)

end
end PTX.Kernels.TmlFa4Fwd.Mma
