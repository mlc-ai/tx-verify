-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.MmaPvIssue
public import Lemmas.Flow.Join

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Mma
open PTX PTX.Flow PTX.Proof

def pvAdvancePc (block : Fin 4) (fragment : Fin 7) : Nat :=
  pvPc block ⟨fragment.val + 1, by have := fragment.isLt; omega⟩

def pvAdvanceLowSrc (block : Fin 4) (fragment : Fin 7) : Nat :=
  (pvSite block).b - if fragment.val < 5 then 3 else 2

def pvAdvanceLowOffset (fragment : Fin 7) : Nat :=
  if fragment.val < 5 then 128 * (fragment.val + 1) else 128

private theorem reassembleCode (block : Fin 4) (fragment : Fin 7) :
    let site := pvSite block
    let pc := pvAdvancePc block fragment
    kernel.code[pc - 2]? = some ⟨none, .int {
      op := .add, ty := .int .u 32, sat := false, dsts := [some (site.b - 2)],
      srcs := [.reg (pvAdvanceLowSrc block fragment), .imm (pvAdvanceLowOffset fragment : Int)] }⟩ ∧
    kernel.code[pc - 1]? = some ⟨none, .move {
      kind := .pack, ty := .int .b 64, dsts := [some site.b],
      srcs := [.reg (site.b - 2), .reg (site.b - 1)] }⟩ := by
  fin_cases block <;> fin_cases fragment
  · exact ⟨Flow.code_2320, Flow.code_2321⟩
  · exact ⟨Flow.code_2323, Flow.code_2324⟩
  · exact ⟨Flow.code_2326, Flow.code_2327⟩
  · exact ⟨Flow.code_2329, Flow.code_2330⟩
  · exact ⟨Flow.code_2332, Flow.code_2333⟩
  · exact ⟨Flow.code_2338, Flow.code_2339⟩
  · exact ⟨Flow.code_2341, Flow.code_2342⟩
  · exact ⟨Flow.code_2435, Flow.code_2436⟩
  · exact ⟨Flow.code_2438, Flow.code_2439⟩
  · exact ⟨Flow.code_2441, Flow.code_2442⟩
  · exact ⟨Flow.code_2444, Flow.code_2445⟩
  · exact ⟨Flow.code_2447, Flow.code_2448⟩
  · exact ⟨Flow.code_2453, Flow.code_2454⟩
  · exact ⟨Flow.code_2456, Flow.code_2457⟩
  · exact ⟨Flow.code_2571, Flow.code_2572⟩
  · exact ⟨Flow.code_2574, Flow.code_2575⟩
  · exact ⟨Flow.code_2577, Flow.code_2578⟩
  · exact ⟨Flow.code_2580, Flow.code_2581⟩
  · exact ⟨Flow.code_2583, Flow.code_2584⟩
  · exact ⟨Flow.code_2589, Flow.code_2590⟩
  · exact ⟨Flow.code_2592, Flow.code_2593⟩
  · exact ⟨Flow.code_2611, Flow.code_2612⟩
  · exact ⟨Flow.code_2614, Flow.code_2615⟩
  · exact ⟨Flow.code_2617, Flow.code_2618⟩
  · exact ⟨Flow.code_2620, Flow.code_2621⟩
  · exact ⟨Flow.code_2623, Flow.code_2624⟩
  · exact ⟨Flow.code_2629, Flow.code_2630⟩
  · exact ⟨Flow.code_2632, Flow.code_2633⟩

private theorem reassembleRange (block : Fin 4) (fragment : Fin 7) :
    1904 ≤ pvAdvancePc block fragment - 2 ∧ pvAdvancePc block fragment - 2 + 2 ≤ 2768 := by
  fin_cases block <;> fin_cases fragment <;> decide

/-- Reassemble the next V descriptor while retaining the live issue and poll operands. -/
theorem pvNextDescriptorFramed (l : Launch) (g : Nat) (block : Fin 4) (fragment : Fin 7)
    {lo : Nat} {F : List (Nat × Value)} (hLo : lo + pvAdvanceLowOffset fragment < 2 ^ 32)
    (hFrame : ∀ pair ∈ F, pair.1 ≠ (pvSite block).b - 2 ∧ pair.1 ≠ (pvSite block).b) :
    let s := pvSite block
    let offs := pvAdvanceLowOffset fragment
    Seg kernel Assumptions.all l g 2 (pvAdvancePc block fragment - 2)
      ((pvAdvanceLowSrc block fragment, b32 lo) :: (s.b - 1, b32 0x40004040) :: F)
      (pvAdvancePc block fragment)
      ((s.b - 2, b32 (lo + offs)) ::
        (s.b, b64 (lo + offs + 2 ^ 32 * 0x40004040)) :: F) := by
  dsimp only
  let s := pvSite block
  let off := pvAdvanceLowOffset fragment
  intro t ht
  let u := next (setReg t (s.b - 2) (b32 (lo + off)))
  let v := next (setReg u s.b (b64 (lo + off + 2 ^ 32 * 0x40004040)))
  have hRange := reassembleRange block fragment
  have hLowReg : t.regs (pvAdvanceLowSrc block fragment) = some (b32 lo) := ht.2.2.2.2.1
  have hHighReg : t.regs (s.b - 1) = some (b32 0x40004040) := ht.2.2.2.2.2.1
  have hLoReg : u.regs (s.b - 2) = some (b32 (lo + off)) := Function.update_self ..
  have hNe : s.b - 1 ≠ s.b - 2 := by fin_cases block <;> decide
  have hNe' : s.b - 2 ≠ s.b := by fin_cases block <;> decide
  have hH : u.regs (s.b - 1) = some (b32 0x40004040) := by
    change Function.update t.regs (s.b - 2) (some (b32 (lo + off))) (s.b - 1) = _
    rw [Function.update_of_ne hNe, hHighReg]
  have hR1 : run kernel [] l g 1 t = some u := by
    apply run_local (reassembleCode block fragment).1 rfl ht
    rw [execLocalA_nil, execLocal_int rfl]
    change execInt l g t ⟨.add, .int .u 32, false, [some (s.b - 2)],
      [.reg (pvAdvanceLowSrc block fragment), .imm (off : Int)]⟩ = _
    have h0 : lo < 2 ^ 32 := by change lo + off < 2 ^ 32 at hLo; omega
    have h1 : off < 2 ^ 32 := by change lo + off < 2 ^ 32 at hLo; omega
    have h2 : lo + off < 2 ^ 32 := hLo
    simp only [execInt, DType.width, readValue, readBits, readReg, hLowReg, b32,
      bind, Except.bind, pure, Except.pure, truncBits_ofNat h0 (by decide),
      BitVec.ofInt_natCast, truncBits_ofNat h1 (by decide), ← BitVec.ofNat_add,
      truncBits_ofNat h2 (by decide), u]
  have hu : At u (pvAdvancePc block fragment - 2 + 1) [] := by
    refine ⟨congrArg (· + 1) ht.1, ht.2.1, ht.2.2.1, ht.2.2.2.1, trivial⟩
  have hPc : pvAdvancePc block fragment - 2 + 1 = pvAdvancePc block fragment - 1 := by omega
  rw [hPc] at hu
  have hR2 : run kernel [] l g 1 u = some v := by
    apply run_local (reassembleCode block fragment).2 rfl hu
    rw [execLocalA_nil, execLocal_move rfl]
    have hJoin : joinValue (b32 (lo + off)) (b32 0x40004040) =
        b64 (lo + off + 2 ^ 32 * 0x40004040) := by
      unfold b32 b64
      rw [Nat.mul_comm (2 ^ 32) 0x40004040]
      exact join_bits32 rfl rfl hLo (by decide)
    change execMove l g u (.move ⟨.pack, .int .b 64, [some s.b],
      [.reg (s.b - 2), .reg (s.b - 1)]⟩) = _
    simp only [execMove, readValue, readReg, hLoReg, hH, hJoin, v,
      bind, Except.bind, pure, Except.pure]
    simp [b32, Value.bytes, DType.width]
  have huHeld : Holds u.regs F := holds_update ht.2.2.2.2.2.2
    (fun pair hm => (hFrame pair hm).1)
  have huFrame : At u (pvAdvancePc block fragment - 1) ((s.b - 2, b32 (lo + off)) :: F) :=
    hu.mono ⟨hLoReg, huHeld⟩
  have hv' := huFrame.set (r := s.b) (v := b64 (lo + off + 2 ^ 32 * 0x40004040)) (by
    intro pair hm
    rcases List.mem_cons.mp hm with rfl | hm
    · exact hNe'
    · exact (hFrame pair hm).2)
  have hv : At v (pvAdvancePc block fragment)
      ((s.b - 2, b32 (lo + off)) :: (s.b, b64 (lo + off + 2 ^ 32 * 0x40004040)) :: F) := by
    have hp : pvAdvancePc block fragment - 1 + 1 = pvAdvancePc block fragment := by omega
    rw [hp] at hv'
    exact hv'.mono ⟨hv'.2.2.2.2.2.1, hv'.2.2.2.2.1, hv'.2.2.2.2.2.2⟩
  have hStraight : ((kernel.code.drop (pvAdvancePc block fragment - 2)).take 1).all
      (fun i => Epilogue.schedulerFallsThrough i.op) = true := by
    set_option maxRecDepth 100000 in
    fin_cases block <;> fin_cases fragment <;> kernel_rfl
  exact ⟨v, localRun hRange.1 hRange.2 ht.1 hStraight (run_comp hR1 hR2), hv⟩

end PTX.Kernels.TmlFa4Fwd.Mma
