-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.MmaValueDescriptorWord
public import Kernels.TmlFa4Fwd.Proof.MmaPvEntry

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Mma
open PTX PTX.Flow PTX.Proof PTX.EventFrame

private theorem madeOperandsB {l : Launch} {cta : Nat} {d : TcMma.Descriptor}
    {a b : TcShared.Descriptor} {s : TcMma.OperandSpec}
    (hs : TcMma.makeOperands l cta d a b = some s) : s.b = b := by
  unfold TcMma.makeOperands at hs
  obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp hs
  obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
  exact congrArg TcMma.OperandSpec.b (Option.some.inj h).symm

private def valueBTemplate (b : TcShared.Descriptor) : Tmpl → Prop
  | .tc (.mma _ op _ _) _ => op.b = b
  | .ub _ => True
  | _ => False

private theorem ofExec_valueB {b : TcShared.Descriptor} {r : Exec Tmpl}
    (h : AllOk (valueBTemplate b) r) : valueBTemplate b (ofExec r) := by
  cases r
  · trivial
  · exact h

private theorem fires_valueB {pc : Nat} {b : TcShared.Descriptor} {tmpl : Tmpl}
    {e : Event} {u : TState} (hf : Fires pc tmpl e (some u)) (h : valueBTemplate b tmpl) :
    ∃ dst op accum mask, e = ⟨pc, .tc (.mma dst op accum mask)⟩ ∧ op.b = b := by
  cases tmpl <;> simp only [valueBTemplate] at h
  case tc k _ =>
    cases k <;> try contradiction
    exact ⟨_, _, _, _, hf.1, h⟩
  case ub => cases hf.2

private theorem execBindOk {α β : Type} (a : α) (f : α → Exec β) :
    (Except.ok a : Exec α) >>= f = f a := rfl

private theorem templateB {l : Launch} {g d ta reg : Nat} {aoff : Int} {t : TState}
    {id en : Opnd} {mask : List Opnd} {word : Nat} {b : TcShared.Descriptor}
    (hr : readBits l g t 64 (.reg reg) = .ok (BitVec.ofNat 64 word))
    (hNat : (BitVec.ofNat 64 word).toNat = word)
    (hDecode : TcShared.decode word = some b) :
    valueBTemplate b (eventTmpl Assumptions.all l g t
      (.tcMma (.dense .one false .f16 d (.tmem ta aoff) (.reg reg) id mask en))) := by
  simp only [eventTmpl, tcTmpl_tcMma_tmem (.inr (.inl rfl)), mmaTmemTmpl]
  apply ofExec_valueB
  simp only [hr, execBindOk, hNat, hDecode]
  repeat' first | (apply allOk_bind; intro) | (apply allOk_ite) | exact True.intro | split
  all_goals
    rename_i hAssembly
    have hB := madeOperandsB hAssembly
    exact hB

variable {p : Params} {l : Launch}

private theorem valuePackIdentities {m : Mem0} (hp : Pre p l m) (use : Nat) :
    sharedDescriptorWord (kvStart l use) 16384 =
        valueDescriptorLow l use + 2 ^ 32 * 0x40004040 ∧
      joinValue (b32 (valueDescriptorLow l use))
          (.bits 32 (truncBits 32 (BitVec.ofInt 64 1073758272))) =
        b64 (valueDescriptorLow l use + 2 ^ 32 * 0x40004040) := by
  refine ⟨rfl, ?_⟩
  have hLo : valueDescriptorLow l use < 2 ^ 32 := by
    have := hp.shared.2.1
    have hSlot : kvSlot use < 3 := Nat.mod_lt _ (by decide)
    unfold valueDescriptorLow kvStart
    omega
  unfold b32 b64
  rw [Nat.mul_comm (2 ^ 32) 0x40004040]
  exact join_bits32 rfl rfl hLo (by decide)

/-- After the actual broadcast result is known, the three descriptor instructions
pack its low word and the fixed swizzle/stride word for the first PV fragment. -/
theorem valueFirstPackedWord {m : Mem0} (hp : Pre p l m) (g : Nat) (block : Fin 4) (use : Nat) :
    let site := pvSite block
    Seg kernel [] l g 3 (pvPc block 0 - 4)
      [((pvSrcRegs block).2.2, b32 (valueDescriptorLow l use))]
      (pvPc block 0 - 1)
      [(site.b, b64 (sharedDescriptorWord (kvStart l use) 16384)),
        (site.b - 3, b32 (valueDescriptorLow l use)), (site.b - 1, b32 0x40004040)] := by
  dsimp only
  obtain ⟨hWord, hJoin⟩ := valuePackIdentities hp use
  fin_cases block <;> intro t ht <;>
    simp only [hWord] <;> seg_fp ht using first | exact hJoin | rfl

/-- The initial PV pack preserves the live warp and election predicate. -/
theorem valueFirstPackedWordFramed {m : Mem0} (hp : Pre p l m) (g : Nat) (block : Fin 4) (use : Nat)
    (lead : Bool) :
    let site := pvSite block
    Seg kernel [] l g 3 (pvPc block 0 - 4)
      [((pvSrcRegs block).2.2, b32 (valueDescriptorLow l use)),
        (1062, b32 12), ((pvSite block).guard, .pred lead)]
      (pvPc block 0 - 1)
      [(site.b, b64 (sharedDescriptorWord (kvStart l use) 16384)),
        (site.b - 3, b32 (valueDescriptorLow l use)), (site.b - 1, b32 0x40004040),
        (1062, b32 12), (site.guard, .pred lead)] := by
  dsimp only
  obtain ⟨hWord, hJoin⟩ := valuePackIdentities hp use
  fin_cases block <;> intro t ht <;>
    simp only [hWord] <;> seg_fp ht using first | exact hJoin | rfl

/-- A returning PV template at its decoded site issues the B descriptor in its lane register. -/
theorem pvReturningIssueBOfRegister {m : Mem0} (hp : Pre p l m) (block : Fin 4) (step : Fin 8)
    (use : Nat) {g : Nat} {t u : TState} {e : Event} (hPc : t.pc = pvPc block step)
    (hReg : t.regs (pvSite block).b =
      some (b64 (sharedDescriptorWord (kvStart l use + pvFragment step) 16384)))
    (he : EStep kernel Assumptions.all l g t e (some u)) :
    ∃ d op accum mask, e = ⟨pvPc block step, .tc (.mma d op accum mask)⟩ ∧
      op.b = sharedDescriptor (kvStart l use + pvFragment step) 16384 := by
  let start := kvStart l use + pvFragment step
  let word := sharedDescriptorWord start 16384
  have hs : start < 2 ^ 18 ∧ start % 16 = 0 := by
    have := hp.shared.2.1
    have := hp.shared.1
    have hSlot : kvSlot use < 3 := Nat.mod_lt _ (by decide)
    have := step.isLt
    dsimp only [start, kvStart, pvFragment]
    exact ⟨by omega, by omega⟩
  have hWord : word < 2 ^ 64 := sharedDescriptorWord_lt hs.1 hs.2 (.inr rfl)
  have hDecode := sharedDescriptor_decode hs.1 hs.2 (.inr (rfl : 16384 = 16384))
  have hNat : (BitVec.ofNat 64 word).toNat = word := by
    exact (BitVec.toNat_ofNat ..).trans (Nat.mod_eq_of_lt hWord)
  have hT := templateB (d := (pvSite block).dst) (ta := (pvSite block).a)
    (aoff := 8 * (step.val : Int)) (id := .reg (pvSite block).id)
    (mask := List.replicate 4 (.imm 0)) (en := pvEnable block step)
    (readBits_b64 (L := l) (g := g) hReg hWord)
    hNat hDecode
  obtain ⟨ins, hi, _, hFire⟩ := estep_event_source he
  have hCode := pvCode block step
  dsimp only at hCode
  rw [hPc, hCode] at hi
  obtain rfl := Option.some.inj hi.symm
  rw [hPc] at hFire
  exact fires_valueB hFire hT

/-- A real PV issue uses the physical V descriptor encoded by that lane's B register. -/
theorem pvIssueBOfRegister {m : Mem0} (hp : Pre p l m) (block : Fin 4) (step : Fin 8) (use : Nat)
    {g d : Nat} {t : TState} {op : TcMma.OperandSpec} {accum : Bool} {mask : List Nat} {u : TState}
    (hReg : t.regs (pvSite block).b =
      some (b64 (sharedDescriptorWord (kvStart l use + pvFragment step) 16384)))
    (he : EStep kernel Assumptions.all l g t ⟨pvPc block step, .tc (.mma d op accum mask)⟩ (some u))
    :
    op.b = sharedDescriptor (kvStart l use + pvFragment step) 16384 := by
  obtain ⟨_, _, _, _, hEv, hB⟩ := pvReturningIssueBOfRegister hp block step use
    (estep_source_pc he).symm hReg he
  cases hEv
  exact hB

end PTX.Kernels.TmlFa4Fwd.Mma
