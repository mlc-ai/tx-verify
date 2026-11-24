-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Spec
public import Lemmas.Flow.ElectMask

@[expose] public section

/-! # Every election of the kernel uses the full mask

Each of the kernel's `elect.sync` instructions names the immediate `-1` as its member mask
(`electMaskOk`, decided on the decoded code). An election event of any thread's trace is fired by
an `elect.sync` of the code at its position and carries the value of its mask operand
(`elect_mask`), so its mask is the 32-bit all-ones mask, whatever machine follows the thread. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Flow

noncomputable section

/-- Every `elect.sync` of the code has the immediate `-1` as its mask operand. -/
def electMaskOk (code : List Instr) : Bool :=
  code.all fun ins =>
    match ins.op with
    | .warp ⟨.elect, _, _, _, some (.imm v)⟩ => v == -1
    | .warp ⟨.elect, _, _, _, _⟩ => false
    | _ => true

theorem kernel_electMaskOk : electMaskOk kernel.code = true := by
  decide +kernel

/-- **Every election event of a consistent execution has the full mask** (`4294967295`). -/
theorem elect_full {L : Launch} {A : List Assumption} {mem0 : Mem0} {X : Execution}
    (hX : Consistent L kernel A mem0 X) {e : EvId} {pc mask inst l : Nat}
    (he : X.Elect e pc mask inst l) : mask = 4294967295 := by
  obtain ⟨g, j⟩ := e
  have hget : (X.tr g)[j]? = some ⟨pc, .elect mask inst l⟩ := he
  have hg : g < L.threads := by
    by_contra h
    rw [hX.outside g (by omega)] at hget
    simp at hget
  have hmem : (⟨pc, .elect mask inst l⟩ : Event) ∈ X.tr g := List.mem_of_getElem? hget
  obtain ⟨ins, ty, d, p, mk, hc, hop, t, bits, hb, hbm⟩ :=
    elect_mask (hX.thr g hg) hmem (e := ⟨pc, .elect mask inst l⟩) rfl
  have hins : ins ∈ kernel.code := List.mem_of_getElem? hc
  have hall := List.all_eq_true.mp kernel_electMaskOk ins hins
  rw [hop] at hall
  cases mk <;> simp at hall
  rename_i v
  have hv : v = -1 := by simpa using hall
  subst hv
  simp only [readBits, truncBits, pure, Except.pure] at hb
  cases hb
  rw [← hbm]
  rfl

end
end PTX.Kernels.FlashAttn4Fwd.Proof
