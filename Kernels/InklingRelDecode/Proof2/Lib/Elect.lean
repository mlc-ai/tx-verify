-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Flow.Code
public import Lemmas.Flow.ElectMask
public import Lemmas.Flow.ElectLead

@[expose] public section

/-! # Every election of the kernel has the full mask

Moved from the first tree's `Interface/RsElect.lean` (names and namespace unchanged): every
`elect.sync` of the code has the mask `-1` (`electMaskOk`, decided), so every election event
carries the full mask (`elect_full`, `electMask_full`), and a thread with an election returning
its own lane led every election of its trace (`electLead_of_elected`). -/

namespace PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {L : Launch} {mem0 : Mem0} {g : Nat} {X : Execution}

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
theorem elect_full {A : List Assumption} (hX : Consistent L kernel A mem0 X) {e : EvId}
    {pc mask inst l : Nat} (he : X.Elect e pc mask inst l) : mask = 4294967295 := by
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

/-- Every election of a consistent execution's thread uses the full mask. -/
theorem electMask_full {A : List Assumption} (hX : Consistent L kernel A mem0 X) (g : Nat) :
    ElectMask 4294967295 (X.tr g) := by
  intro e he mask inst ld hk
  obtain ⟨n, hn, rfl⟩ := List.getElem_of_mem he
  have hx : (X.tr g)[n] = ⟨(X.tr g)[n].pc, .elect mask inst ld⟩ := by rw [← hk]
  exact elect_full hX (e := (g, n)) (pc := (X.tr g)[n].pc) (inst := inst) (l := ld)
    (show (X.tr g)[n]? = _ by rw [List.getElem?_eq_getElem hn, ← hx])

/-- **A thread with an election returning its lane led every election.** -/
theorem electLead_of_elected {A : List Assumption} (hX : Consistent L kernel A mem0 X)
    (hel : Elected (X.tr g) (laneOf L g)) : ElectLead L g (X.tr g) := by
  rcases electLead_or_nonLead hX.elect (electMask_full hX g) with h | h
  · exact h
  · exfalso
    obtain ⟨e, he, mask, inst, hk⟩ := hel
    exact h e he mask inst (laneOf L g) hk rfl

end
end PTX.Kernels.InklingRelDecode.Proof.Interface
