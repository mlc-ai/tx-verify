-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Protocol.Values.EpiStore
import Kernels.InklingRelDecode.Proof.Lib.EpiLse
import Kernels.InklingRelDecode.Proof.Lib.EvLane
import Lemmas.Flow.StoreAdvance
import Lemmas.Flow.StoreSrc
import Lemmas.Flow.StoreGlobal
import Kernels.InklingRelDecode.Flow.Code.Part041

@[expose] public section

/-! # The word the epilogue stores for the log normalizer

The normalizer of register 524 (`scale * log2e * m + log2 l`, from `lg2` at pc 2562 and `fma` at
pc 2563) stays in its register to the `selp` at pc 2680, which picks it or the `-inf` pattern by the
predicate 178 (the sum is zero); the store at pc 2682 writes that word. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.Values
open PTX PTX.Flow PTX.Proof PTX.Kernels.InklingRelDecode.Proof.Lib

noncomputable section
variable {L : Launch} {g : Nat} {X : Execution}

/-- The word of the LSE store: the `-inf` pattern for a zero sum, else the normalizer. -/
def lseV (l sc mr : ℝ) : Value :=
  if l = 0 then .bits 32 (truncBits 32 (BitVec.ofInt 64 (-8388608)))
  else .float .f32 (sc * mr + Real.logb 2 l)

private def s524 : List (Nat × Nat) := [(2564, 2846)]
private def s178 : List (Nat × Nat) := [(2600, 2846)]

private theorem a_fwd : fwdOk s524 [524] = true := by decide +kernel
private theorem a_ev : evKeep s524 [524] = true := by decide +kernel
private theorem a_enter : enterOk s524 2564 = true := by decide +kernel
private theorem a_pred : predOk 2564 [2563] = true := by decide +kernel
private theorem a_zero : inS s524 0 = false := by decide +kernel
private theorem a_out : evOut s524 = true := by decide +kernel
private theorem b_fwd : fwdOk s178 [178] = true := by decide +kernel
private theorem b_ev : evKeep s178 [178] = true := by decide +kernel
private theorem b_enter : enterOk s178 2600 = true := by decide +kernel
private theorem b_pred : predOk 2600 [2599] = true := by decide +kernel
private theorem b_zero : inS s178 0 = false := by decide +kernel
private theorem b_out : evOut s178 = true := by decide +kernel
private theorem p63_pred : predOk 2563 [2562] = true := by decide +kernel
private theorem p63_land : evLand 2563 = true := by decide +kernel
private theorem p82_pred : predOk 2682 [2681] = true := by decide +kernel
private theorem p82_land : evLandS 2682 [2681] = true := by decide +kernel
private theorem p81_pred : predOk 2681 [2680] = true := by decide +kernel
private theorem p81_land : evLandS 2681 [2680] = true := by decide +kernel

/-- **The normalizer stays in register 524** from the `fma` to the end of the window. -/
theorem norm_kept {l sc mr : ℝ} (hl : 0 < l)
    (entry : ∀ t, Iface.LaneState L X g t → t.pc = 2562 → t.regs 1915 = some (.float .f32 l))
    (entry2 : ∀ t, Iface.LaneState L X g t → t.pc = 2562 →
      t.regs 1914 = some (.float .f32 mr) ∧ t.regs 498 = some (.float .f32 sc)) :
    ∀ t, Iface.LaneState L X g t → 2564 ≤ t.pc → t.pc ≤ 2846 →
      t.regs 524 = some (.float .f32 (sc * mr + Real.logb 2 l)) := by
  intro t ht h1 h2
  refine win_ind (S := s524) (R := [524]) (lo := 2564) (preds := [2563])
    (P := fun t => t.regs 524 = some (.float .f32 (sc * mr + Real.logb 2 l)))
    a_fwd a_ev a_enter a_pred a_zero a_out (fun t t' h hp => by rw [h 524 (by simp)]; exact hp)
    (fun c w hc ht' hcp hw => ?_) t ht (by simp [inS, s524]; omega)
  have hc63 : c.pc = 2563 := by simpa using hcp
  obtain ⟨c0, hc0, hc0p, hT0⟩ := tau_before p63_pred p63_land (by omega) hc hc63
  have hc02 : c0.pc = 2562 := by simpa using hc0p
  obtain ⟨-, h59, hk⟩ := lg2_tau hc02 hl (entry c0 hc0 hc02) hT0
  obtain ⟨e14, e98⟩ := entry2 c0 hc0 hc02
  obtain ⟨-, h524, -⟩ := fma_tau hc63 (by rw [hk 498 (by omega), e98])
    (by rw [hk 1914 (by omega), e14]) h59 ht'
  exact h524

/-- **The predicate 178 stays** from the zero pairs to the end of the window. -/
theorem zero_kept {l : ℝ} {b : Bool}
    (entry : ∀ t, Iface.LaneState L X g t → t.pc = 2562 → t.regs 1915 = some (.float .f32 l))
    (wait : EpiWait L X g b) :
    ∀ t, Iface.LaneState L X g t → 2600 ≤ t.pc → t.pc ≤ 2846 →
      t.regs 178 = some (.pred (decide (l = 0))) := by
  intro t ht h1 h2
  refine win_ind (S := s178) (R := [178]) (lo := 2600) (preds := [2599])
    (P := fun t => t.regs 178 = some (.pred (decide (l = 0))))
    b_fwd b_ev b_enter b_pred b_zero b_out (fun t t' h hp => by rw [h 178 (by simp)]; exact hp)
    (fun c w hc ht' hcp hw => ?_) t ht (by simp [inS, s178]; omega)
  obtain ⟨-, h178, -⟩ := zero_pairs entry wait w (lane_tail hc ht') hw
  exact h178

/-- **The predicate 178 stays** (any row sum value) from the zero pairs to the end of the window. -/
theorem zero_kept_any {v : Value} {b : Bool}
    (entry : ∀ t, Iface.LaneState L X g t → t.pc = 2562 → t.regs 1915 = some v)
    (wait : EpiWait L X g b) :
    ∀ t, Iface.LaneState L X g t → 2600 ≤ t.pc → t.pc ≤ 2846 →
      t.regs 178 = some (.pred (okPred (setpE (.unord .eq) false v
        (.bits 32 (BitVec.ofNat 64 0))))) := by
  intro t ht h1 h2
  refine win_ind (S := s178) (R := [178]) (lo := 2600) (preds := [2599])
    (P := fun t => t.regs 178 = some (.pred (okPred (setpE (.unord .eq) false v
      (.bits 32 (BitVec.ofNat 64 0))))))
    b_fwd b_ev b_enter b_pred b_zero b_out (fun t t' h hp => by rw [h 178 (by simp)]; exact hp)
    (fun c w hc ht' hcp hw => ?_) t ht (by simp [inS, s178]; omega)
  obtain ⟨-, h178, -⟩ := zero_pairs_any entry wait w (lane_tail hc ht') hw
  exact h178

private theorem em2681 : 2681 ∉ Assumptions.emuSites := by decide +kernel

private theorem em2680 : 2680 ∉ Assumptions.emuSites := by decide +kernel

/-- The registers of the selection at pc 2680. -/
private theorem sel_regs {l sc mr : ℝ} {b : Bool} (hl : 0 ≤ l)
    (entry : ∀ t, Iface.LaneState L X g t → t.pc = 2562 → t.regs 1915 = some (.float .f32 l))
    (entry2 : ∀ t, Iface.LaneState L X g t → t.pc = 2562 → 0 < l →
      t.regs 1914 = some (.float .f32 mr) ∧ t.regs 498 = some (.float .f32 sc))
    (wait : EpiWait L X g b) {c : TState} (hc : Iface.LaneState L X g c) (hpc : c.pc = 2680) :
    c.regs 178 = some (.pred (decide (l = 0))) ∧
      (l ≠ 0 → c.regs 524 = some (.float .f32 (sc * mr + Real.logb 2 l))) := by
  refine ⟨zero_kept entry wait c hc (by omega) (by omega), fun hne => ?_⟩
  have hpos : 0 < l := lt_of_le_of_ne hl (Ne.symm hne)
  exact norm_kept hpos entry (fun t ht h => entry2 t ht h hpos) c hc (by omega) (by omega)

/-- **The LSE store writes the bytes of its word.** -/
theorem lse_core {m : Mem0} {p : Bool} {V : Value}
    (hX : Consistent L kernel Assumptions.all m X) (hVb : V.bytes = 4)
    (selr : ∀ c, Iface.LaneState L X g c → c.pc = 2680 →
      c.regs 178 = some (.pred p) ∧ (p = false → c.regs 524 = some V))
    {k : Nat} {a : Acc} {bs : List Byte} (he : X.get (g, k) = some ⟨2682, .wr a bs⟩) :
    bs = (if p then Value.bits 32 (truncBits 32 (BitVec.ofInt 64 (-8388608))) else V).toBytes := by
  obtain ⟨s, u, hs, hes⟩ := lane_of_event hX he (by simp [Ends])
  obtain ⟨ins, hci, -, hf⟩ := EventFrame.estep_event_source hes
  have hspc := EventFrame.estep_source_pc hes
  have hpc : s.pc = 2682 := by simpa using hspc.symm
  obtain ⟨c1, hc1, hp1, hT1⟩ := back_one p82_pred p82_land (by omega) hs hpc
  have hc1p : c1.pc = 2681 := by simpa using hp1
  rcases hT1 with hT1 | ⟨e1, hes1⟩
  swap
  · exfalso
    obtain ⟨ins1, hci1, hnl1, -⟩ := EventFrame.estep_event_source hes1
    rw [hc1p, Flow.code_2681] at hci1
    obtain rfl := (Option.some.inj hci1).symm
    exact absurd hnl1 (by decide)
  obtain ⟨ins1, hci1, -, hk1⟩ := win_cases hT1
  rw [hc1p, Flow.code_2681] at hci1
  obtain rfl := (Option.some.inj hci1).symm
  have hreg1 : s.regs 1831 = c1.regs 1831 := by
    rcases hk1 with ⟨hg, -⟩ | ⟨-, -, hreg⟩
    · simp at hg
    · exact hreg 1831 (by simp [writesRegs]) (fun h => absurd (by simpa [hc1p] using h) em2681)
  obtain ⟨c2, hc2, hp2, hT2⟩ := back_one p81_pred p81_land (by omega) hc1 hc1p
  have hc2p : c2.pc = 2680 := by simpa using hp2
  rcases hT2 with hT2 | ⟨e2, hes2⟩
  swap
  · exfalso
    obtain ⟨ins2, hci2, hnl2, -⟩ := EventFrame.estep_event_source hes2
    rw [hc2p, Flow.code_2680] at hci2
    obtain rfl := (Option.some.inj hci2).symm
    exact absurd hnl2 (by decide)
  obtain ⟨h178, h524⟩ := selr c2 hc2 hc2p
  obtain ⟨-, -, hT, hF⟩ := selp_tau hc2p h178 (fun hp => ⟨V, h524 hp, hVb⟩) hT2
  have hv : s.regs 1831 = some (if p then Value.bits 32 (truncBits 32 (BitVec.ofInt 64 (-8388608)))
      else V) := by
    rw [hreg1]
    cases p
    · obtain ⟨v, hv, hw⟩ := hF rfl
      have hv' := h524 rfl
      rw [hv] at hv'
      rw [hw, Option.some.inj hv']
      rfl
    · rw [hT rfl]
      rfl
  have hbytes : (if p then Value.bits 32 (truncBits 32 (BitVec.ofInt 64 (-8388608))) else V).bytes
      = 4 := by
    cases p <;> simp [hVb, Value.bytes]
  obtain ⟨mm, hmm, hgs⟩ : ∃ mm, ins.op = .mem mm ∧ GlobalStore mm 2379 1831 := by
    rw [hpc, Flow.code_2682] at hci
    obtain rfl := (Option.some.inj hci).symm
    exact ⟨_, rfl, by decide⟩
  rw [hmm] at hf
  obtain ⟨hr, hsp, hb, hkd, hsem, hw, -, hsrc⟩ := hgs
  obtain ⟨hsub, -, -⟩ := fires_st_adv hr (sp := .global) (by simpa using hsp) hb hkd hsem hsrc hf
  obtain ⟨acc, hacc⟩ := fires_st_srcBytes hr (by simpa using hsp) hb hkd hsem hsrc
    (by rw [hw]; exact hbytes) hsub hv hf (fun f h => by cases h)
  exact (Kind.wr.inj hacc).2


/-- **The LSE store writes the bytes of its word.** -/
theorem lse_store {m : Mem0} {l sc mr : ℝ} {b : Bool}
    (hX : Consistent L kernel Assumptions.all m X) (hl : 0 ≤ l)
    (entry : ∀ t, Iface.LaneState L X g t → t.pc = 2562 → t.regs 1915 = some (.float .f32 l))
    (entry2 : ∀ t, Iface.LaneState L X g t → t.pc = 2562 → 0 < l →
      t.regs 1914 = some (.float .f32 mr) ∧ t.regs 498 = some (.float .f32 sc))
    (wait : EpiWait L X g b) {k : Nat} {a : Acc} {bs : List Byte}
    (he : X.get (g, k) = some ⟨2682, .wr a bs⟩) : bs = (lseV l sc mr).toBytes := by
  have := lse_core (V := .float .f32 (sc * mr + Real.logb 2 l)) (p := decide (l = 0)) hX
    (by simp [Value.bytes, FloatFmt.bytes]) (fun c hc hpc => by
      obtain ⟨h178, h524⟩ := sel_regs hl entry entry2 wait hc hpc
      exact ⟨h178, fun hp => h524 (by simpa using hp)⟩) he
  rw [this]
  by_cases hz : l = 0 <;> simp [lseV, hz]

/-- **The LSE store of the empty launch writes the `-inf` pattern.** -/
theorem lse_store_zero {m : Mem0} {v : Value} {b : Bool}
    (hX : Consistent L kernel Assumptions.all m X)
    (entry : ∀ t, Iface.LaneState L X g t → t.pc = 2562 → t.regs 1915 = some v)
    (wait : EpiWait L X g b)
    (hz : okPred (setpE (.unord .eq) false v (.bits 32 (BitVec.ofNat 64 0))) = true)
    {k : Nat} {a : Acc} {bs : List Byte} (he : X.get (g, k) = some ⟨2682, .wr a bs⟩) :
    bs = (Value.bits 32 (truncBits 32 (BitVec.ofInt 64 (-8388608)))).toBytes := by
  have := lse_core (V := b32 0) (p := true) hX rfl (fun c hc hpc => by
    refine ⟨?_, fun h => absurd h (by simp)⟩
    rw [zero_kept_any entry wait c hc (by omega) (by omega), hz]) he
  simpa using this

end
end PTX.Kernels.InklingRelDecode.Proof.Protocol.Values
