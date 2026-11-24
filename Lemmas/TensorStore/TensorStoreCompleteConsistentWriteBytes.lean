-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Async.AsyncExecution
public import Lemmas.Clc.ClcEffects

@[expose] public section

/-! Actual asynchronous writes define every byte of their declared footprint. A whole write of an
operation with a register source has the destination's size because its issuing instruction built
the bytes from the value operands (`hform` states the memory-source form). -/
namespace PTX
open AsyncCopy
noncomputable section

 theorem Consistent.async_write_bytes {L : Launch} {K : Kernel} {A : List Assumption}
    {mem0 : Mem0} {X : Execution} (hX : Consistent L K A mem0 X)
    {i : EvId} {p : Part} {a : Acc} {bytes : List Byte}
    (hw : X.MemWrites (.async i p) a bytes)
    (hform : ∀ s, issuedBy X i = some s → s.data = none ∧ s.writes = .whole ∧
      s.src.size = s.dst.size) : bytes.length=a.size := by
  cases p <;> try exact hw.elim
  case writeCopy =>
    have hw0 := hw
    obtain ⟨s, hcop, -, hdst, -⟩ := hw
    obtain ⟨s', hcop', -, hlen⟩ := hX.copy_write_read hw0 hform
    have huniq : s' = s := Execution.Copy.unique hcop' hcop
    subst huniq
    rw [hdst] at hlen
    exact hlen
  case writeStore x y k =>
    obtain ⟨o,address,b,_,_,_,_,hsize,rfl,_⟩ := hw
    simpa only [List.length_singleton] using hsize.symm
  case writeLoad x y k =>
    obtain ⟨o,address,b,_,_,_,_,hsize,rfl,_⟩ := hw
    simpa only [List.length_singleton] using hsize.symm
  case writeElem j =>
    obtain ⟨s, hcop, hsel, hbytes⟩ := hw
    obtain ⟨pc, hi⟩ := hcop
    have hn : nonempty (X.async.copies i) := ⟨.write (.elem j), by simp [present, hbytes]⟩
    obtain ⟨spec, hs, hok⟩ := hX.tma.1 i hn
    simp only [issuedBy, hi, Option.some.injEq] at hs
    subst hs
    have hbs : bytes.length = s.elemWidth := (hok.2.2.2.2.1 j bytes hbytes).2.1
    have hasz : a.size = s.elemWidth := by
      obtain ⟨k, -, hk⟩ := List.mem_map.mp (List.mem_of_getElem? hsel)
      rw [← hk]
    rw [hasz, hbs]
  case writeCta c =>
    obtain ⟨s,targets,_,_,_,response,_,rfl,rfl⟩ := hw
    simp [Value.toBytes,Value.bytes]

 theorem Consistent.async_write_byte_defined {L : Launch} {K : Kernel} {A : List Assumption}
    {mem0 : Mem0} {X : Execution} (hX : Consistent L K A mem0 X)
    {i : EvId} {p : Part} {a : Acc} {bytes : List Byte} {loc : Loc}
    (hw : X.MemWrites (.async i p) a bytes)
    (hform : ∀ s, issuedBy X i = some s → s.data = none ∧ s.writes = .whole ∧
      s.src.size = s.dst.size)
    (hcover : a.Covers loc) : ∃value,wbyte a bytes loc=some value := by
  have hlen := hX.async_write_bytes hw hform
  have hr : loc.addr-a.loc.addr<bytes.length := by
    unfold Acc.Covers Loc.InRange at hcover
    omega
  exact ⟨bytes[loc.addr-a.loc.addr],List.getElem?_eq_getElem hr⟩

end
end PTX
