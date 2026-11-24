-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Result.GemmKvValues
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0ProbabilityBytes

@[expose] public section

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Result

open PTX.Proof MmaDataTrace

noncomputable section

/-- The softmax lane that writes a given head and sparse-slot pair. -/
def probabilityLane (L : Launch) (cta : Nat) (row : Fin 128) (slot : Fin 64) : Nat :=
  cta * L.block + 64 * (slot.val / 32) + row.val % 64

/-- Recover the storing lane's head and row half from a probability tile coordinate. -/
theorem probabilityLane_coords {P : Params} {L : Launch} {mem0 : Mem0} (hpre : Pre P L mem0)
    (cta : Nat) (row : Fin 128) (slot : Fin 64) :
    let lane := probabilityLane L cta row slot
    ctaOf L lane = cta ∧ Wg0.head L lane = row.val % 64 ∧
      Wg0.half L lane = slot.val / 32 := by
  let lane := probabilityLane L cta row slot
  have ht : tidOf L lane = 64 * (slot.val / 32) + row.val % 64 := by
    rw [tidOf_eq hpre]
    dsimp only [probabilityLane, lane]
    rw [hpre.block]
    omega
  refine ⟨?_, ?_, ?_⟩
  · dsimp [ctaOf, probabilityLane]
    rw [hpre.block]
    omega
  · rw [Wg0.head, ht]
    omega
  · rw [Wg0.half, warpOf, ht]
    omega

/-- The Wg0 store is a write of the exact BF16 byte consumed by a PV operand. -/
theorem probability_write_byte {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    (hpre : Pre P L mem0) {g j : Nat} {d : Wg0.D} {e : Event} {u : TState}
    {site : Fin 4} (hd : d.site = .pStore site) (he : X.get (g, j) = some e)
    (hf : (Wg0.code P L g).toMachine.Fired (some d) e (some u))
    (half byte : Fin 2) :
    let slot := 32 * Wg0.half L g + 2 * (4 * site.val + d.sub) + half.val
    let loc : Loc := ⟨.shared, ctaOf L g, pLinearByte L (Wg0.head L g) slot byte.val⟩
    ∃ a bs, X.MemWrites (.thread (g, j)) a bs ∧
      wbyte a bs loc = some (.float .bf16 (d.pw (Wg0.head L g) slot), byte.val) := by
  obtain ⟨a, hkind, hloc, _, hsub⟩ := Wg0.fired_pStore_event hpre hd hf
  let sub : Fin 4 := ⟨d.sub, hsub⟩
  let bytes := (Wg0.pPacked L g d (4 * site.val + d.sub)).toBytes
  obtain ⟨address, hsite, haddr⟩ := pStore_mmaByte (g := g) (block := d.block)
    (Wg0.head_eq L g) site sub half byte
  have haddr' : a.loc = address := by
    rw [hd] at hloc
    exact Option.some.inj (hloc.symm.trans hsite)
  refine ⟨a, bytes, ?_, ?_⟩
  · cases e
    exact .inl ⟨_, he.trans (congrArg some (congrArg (Event.mk _) hkind))⟩
  · rw [← haddr, ← haddr']
    change bytes[a.loc.addr + (2 * half.val + byte.val) - a.loc.addr]? = _
    rw [Nat.add_sub_cancel_left]
    exact pPacked_mmaByte L g d site sub half byte

/-- Actual PV A reads recover the probabilities written by their owning softmax lanes. -/
theorem pvA_from_probability {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    {g block : Nat} {i : EvId} {issue : Fin 8} {ops : AsyncCopy.MmaOperands}
    (hi : X.MmaIssue i (Wg1Mma.pvDest issue) (pvOperands L g block issue) (pvAccum block issue)
      [0, 0, 0, 0]) (ho : X.async.mmaOperands i = some ops) (row : Fin 128) (weight : Nat → ℝ)
    (hwrite : ∀ k : Fin 16, ∀ b : Fin 2,
      let slot : Fin 64 := ⟨pvSlot issue k, by unfold pvSlot; omega⟩
      let lane := probabilityLane L (ctaOf L g) row slot
      let site : Fin 4 := ⟨slot.val % 32 / 8, by omega⟩
      ∃ j d e u, d.site = Wg0.Site.pStore site ∧ d.sub = (slot.val / 2) % 4 ∧ d.block = block ∧
        X.get (lane, j) = some e ∧ (Wg0.code P L lane).toMachine.Fired (some d) e (some u) ∧
        d.pw (row.val % 64) slot.val = weight slot.val ∧
        X.rf (.async i (.mmaRead false (2 * (row.val * 16 + k.val) + b.val))) 0 =
          some (.thread (lane, j))) :
    Bf16Operand ops.a row.val (fun k => weight (16 * (issue.val / 2) + k)) := by
  intro k hk b hb
  let k' : Fin 16 := ⟨k, hk⟩
  let b' : Fin 2 := ⟨b, hb⟩
  let slot : Fin 64 := ⟨pvSlot issue k', by unfold pvSlot; omega⟩
  let lane := probabilityLane L (ctaOf L g) row slot
  let site : Fin 4 := ⟨slot.val % 32 / 8, by omega⟩
  let bit : Fin 2 := ⟨slot.val % 2, Nat.mod_lt _ (by decide)⟩
  obtain ⟨j, d, e, u, hd, hsub, _, he, hf, hw, hrf⟩ := hwrite k' b'
  obtain ⟨hcta, hhead, hhalf⟩ := probabilityLane_coords hpre (ctaOf L g) row slot
  obtain ⟨a, bs, hmem, hval⟩ := probability_write_byte hpre hd he hf bit b'
  have heq : 32 * Wg0.half L lane + 2 * (4 * site.val + d.sub) + bit.val = slot.val := by
    rw [hhalf, hsub]
    change 32 * (slot.val / 32) +
      2 * (4 * (slot.val % 32 / 8) + slot.val / 2 % 4) + slot.val % 2 = slot.val
    omega
  dsimp only at hval
  rw [heq, hhead, hcta, hw] at hval
  have hl := pvProbabilityByte L g block issue row k' b'
  exact operand_byte_from_writer hX hi ho (isB := false) hl hmem hval hrf

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Result
