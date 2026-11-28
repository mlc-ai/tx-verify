-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Protocol.Shared.TileWriters
import Kernels.InklingRelDecode.Proof.Common.Export.PairPhase
import Kernels.InklingRelDecode.Proof.Protocol.Shared.RoleVersions
import Kernels.InklingRelDecode.Proof.Dispatch.Export.RoleAddress

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.Shared
open PTX PTX.Flow PTX.Proof

/-- At either dispatch, each worker reads the corresponding byte of the
most recently published role word. The phase is observable in its own trace. -/
theorem role_bytes {Q L m X g k a bs} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (he : X.get (g,k)=some ⟨2340,.rd a bs⟩) :
    let n := ((X.tr g).take k).countP (Execution.isBarId 1)
    bs=[(b32 (if n=1 then 16777730 else 50529027)).toBytes[g%L.block/32-4]?] := by
  dsimp only
  obtain ⟨low,high,_,addr⟩ := Dispatch.Export.role_address hp hX he
  have miss : ¬TensorByte X a.loc := by
    apply outside_tiles hp hX <;> rw [addr] <;> dsimp <;> omega
  have single {v : Option Byte} (h : bs.length=1 ∧ bs[0]?=some v) : bs=[v] := by
    obtain ⟨len,hd⟩ := h
    cases bs with
    | nil => simp at len
    | cons x xs =>
      simp at len hd
      simp [len,hd]
  obtain first|⟨second,_⟩ := read_round hp hX he (.inl rfl)
  · rw [ite_eq_left first]
    exact single (first_role_byte hp hX he first miss)
  · rw [ite_eq_right (by omega)]
    exact single (exit_role_byte hp hX he second miss)

/-- Before scratch reuse, worker count loads return the launch's two counts. -/
theorem pair_bytes {Q L m X g k p a bs} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (he : X.get (g,k)=some ⟨p,.rd a bs⟩)
    (site : p=2345 ∨ p=2423) (first : ((X.tr g).take k).countP (Execution.isBarId 1)=1) :
    ∃ j : Fin 2, (p=2423 → j=1) ∧ a.loc=⟨.shared,g/L.block,L.sharedBase+212992+4*j.val⟩ ∧
      bs=(b32 (if j=0 then Iface.preloadCount Q L (g/L.block)
        else Lib.blocksOf Q L (g/L.block))).toBytes.map some := by
  apply worker_pair hp hX he site first
  intro o bound
  apply outside_tiles hp hX <;> dsimp <;> omega

/-- Every worker count read consumes the publication at 571. Its address
selects the component even though the two components share an instruction PC. -/
theorem published_counts {Q L m X g k p a bs} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (he : X.get (g,k)=some ⟨p,.rd a bs⟩)
    (site : p=2345 ∨ p=2423) :
    ∃ j : Fin 2, (p=2423 → j=1) ∧ a.loc=⟨.shared,g/L.block,L.sharedBase+212992+4*j.val⟩ ∧
      bs=(b32 (if j=0 then Iface.preloadCount Q L (g/L.block)
        else Lib.blocksOf Q L (g/L.block))).toBytes.map some := by
  apply pair_bytes hp hX he site
  exact Export.pair_phase hp hX (fun h => role_bytes hp hX h) he site

end PTX.Kernels.InklingRelDecode.Proof.Protocol.Shared
