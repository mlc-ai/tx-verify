-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingSoftmaxWriteRegs
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingRegisterRegion
import Lemmas.Flow.NotTcSt
import Lemmas.Flow.NotBulk
import Lemmas.Flow.ElemAccess
import Lemmas.Flow.EventCont
import Lemmas.Flow.OpPcsFast

@[expose] public section

/-! # Tensor Memory store destinations are independent of rescale data -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking

open PTX PTX.Flow PTX.Proof PTX.EventFrame

variable {L : Launch} {g : Nat}

private def addrReg (tile : Fin 4) : Nat := 1263 + 129 * tile.val
private def addrMove (tile : Fin 4) : Nat := 715 + 101 * tile.val
private def addrRegion (tile : Fin 4) (pc : Nat) : Bool :=
  decide (addrMove tile < pc ∧ pc ≤ (Wg0.Site.rescaleStore tile).pc)

set_option maxRecDepth 100000 in
private theorem addr_audit (tile : Fin 4) :
    registerRegionChecked (addrReg tile) (addrRegion tile) [addrMove tile] = true := by
  fin_cases tile <;> decide +kernel

private theorem addr_mov_is_local (tile : Fin 4) :
    [addrMove tile].all (fun pc => ((kernel.code[pc]?).map (·.op.isLocal)).getD true) = true := by
  fin_cases tile <;> decide +kernel

private theorem addr_lit {t u : TState} (tile : Fin 4)
    (hPc : t.pc = addrMove tile) (hTau : Tau kernel Assumptions.all L g t u) :
    u.regs (addrReg tile) = some (b32 (64 * tile.val)) := by
  have hAt : AtVector t (addrMove tile) [] t.sub t.acc :=
    ⟨hPc, rfl, rfl, tau_fault_free hTau, trivial⟩
  obtain ⟨v, hRun, hv⟩ : ∃ v, run kernel Assumptions.all L g 1 t = some v ∧
      AtVector v (addrMove tile + 1) [(addrReg tile, b32 (64 * tile.val))] t.sub t.acc := by
    fin_cases tile <;> seg_fp hAt using norm_bits [addrReg, addrMove, b32]
  exact (one_step_matches hTau hRun) ▸ hv.2.2.2.2.1

set_option maxRecDepth 100000 in
private theorem store_sites :
    OpPcsFast kernel.code tcStOp [814, 915, 1016, 1117] = true := by decide +kernel

private theorem store_site_tile {pc : Nat} (hp : pc ∈ [814, 915, 1016, 1117]) :
    ∃ tile : Fin 4, pc = (Wg0.Site.rescaleStore tile).pc := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩
  · exact ⟨2, rfl⟩
  · exact ⟨3, rfl⟩

/-- The instruction source of a Tensor Memory store identifies its destination-register site. -/
theorem actual_tmem_store_site {mem0 : Mem0} {X : Execution}
    {i dst : Nat} {e : Event} {words : List Value} {shape : TcShape}
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (he : X.get (g, i) = some e) (hk : e.kind = .tc (.st dst words shape)) :
    ∃ tile : Fin 4, e.pc = (Wg0.Site.rescaleStore tile).pc := by
  rcases get_source hX he with ⟨f, hf⟩ | ⟨t, ins, o, _, hc, hf⟩
  · rw [hf] at hk
    cases hk
  · exact store_site_tile (OpPcsFast.mem store_sites hc (fires_tcSt_op hf hk))

/-- An actual Tensor Memory rescale store names only the corresponding output slice. -/
theorem tmem_store_from_mask {t : TState} {events : List Event} {o : Option TState}
    {e : Event} {dst : Nat} {words : List Value} {shape : TcShape}
    (tile : Fin 4) (ht : t.pc = 264) (hRun : Run kernel Assumptions.all L g t events o)
    (he : e ∈ events) (hp : e.pc = (Wg0.Site.rescaleStore tile).pc)
    (hk : e.kind = .tc (.st dst words shape)) :
    dst = 64 * tile.val ∧ shape = .s32x32b ∧ words.length = 64 := by
  let valid (u : TState) : Prop := addrRegion tile u.pc = true →
    u.regs (addrReg tile) = some (b32 (64 * tile.val))
  have hStart : valid t := by
    intro h
    rw [ht] at h
    have hNo : addrRegion tile 264 = false := by fin_cases tile <;> decide
    rw [hNo] at h
    cases h
  obtain ⟨u, next, hValid, hSource⟩ := actual_event_invariant (valid := valid)
    (fun hOld hTau => register_region_tau (property := (· = some (b32 (64 * tile.val))))
      (addr_audit tile) hOld (fun hUpdate _ => addr_lit tile (List.mem_singleton.mp hUpdate) hTau)
      hTau)
    (fun hOld hEvent => register_region_event (property := (· = some (b32 (64 * tile.val))))
      (addr_audit tile) (register_updates_local (addr_mov_is_local tile)) hOld hEvent)
    hStart hRun he
  have hPc : u.pc = (Wg0.Site.rescaleStore tile).pc := (estep_source_pc hSource).symm.trans hp
  have hIn : addrRegion tile u.pc = true := by rw [hPc]; fin_cases tile <;> decide
  have hReg := hValid hIn
  cases next with
  | none =>
    obtain ⟨_, _, hFire⟩ := hSource
    have hEnd := fires_none_ends hFire
    simp [Ends, hk] at hEnd
  | some v =>
    obtain ⟨ins, hc, _, hFire⟩ := estep_event_source hSource
    rw [hPc] at hc
    have hBound : 64 * tile.val < 2 ^ 32 := by have := tile.isLt; omega
    have finish {ss : List Opnd} (hs : ins.op = .tcSt (addrReg tile) ss .s32x32b)
        (hLen : ss.length = 64) :
        dst = 64 * tile.val ∧ shape = .s32x32b ∧ words.length = 64 := by
      rw [hs] at hFire
      obtain ⟨⟨vs, hEvent⟩, _⟩ := fires_tcSt hReg hBound hFire
      obtain ⟨ha, _, hc⟩ := TcKind.st.inj (Kind.tc.inj (hk.symm.trans (congrArg Event.kind hEvent)))
      exact ⟨ha, hc, (fires_tcSt_len (by simp) hFire hk).trans hLen⟩
    fin_cases tile
    · obtain rfl := Option.some.inj (Flow.code_814.symm.trans hc)
      exact finish rfl rfl
    · obtain rfl := Option.some.inj (Flow.code_915.symm.trans hc)
      exact finish rfl rfl
    · obtain rfl := Option.some.inj (Flow.code_1016.symm.trans hc)
      exact finish rfl rfl
    · obtain rfl := Option.some.inj (Flow.code_1117.symm.trans hc)
      exact finish rfl rfl

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking
