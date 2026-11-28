-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Protocol.Tmem.WriteStore
public import Kernels.InklingRelDecode.Proof.Iface.BaseRead
import Kernels.InklingRelDecode.Proof.Protocol.Tmem.DataStatic
import Kernels.InklingRelDecode.Proof.Common.Export.TcOperand
import Kernels.InklingRelDecode.Proof.Lib.TcDataEvent

/-! # The rescale store of a thread

An event of pc 2328 that is not undefined behaviour is a `tcgen05.st` (`st_kind_2328`), and the
cell its word `jj` writes is the cell of its thread's half-split access (`st_cell`). -/

namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.Values
open PTX PTX.Flow PTX.TcMma Tmem

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **An event of pc 2328 without undefined behaviour is a `tcgen05.st`.** -/
public theorem st_kind_2328 (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (base : Iface.BaseRead L X) {g j : Nat} {k : Kind}
    (he : X.get (g, j) = some ⟨2328, k⟩) (nu : ∀ f, k ≠ .ub f) :
    ∃ a vals sh, k = .tc (.st a vals sh) := by
  have hd := Lib.tcdata_event hX he nu
  have hd' : isTcData ⟨2328, k⟩ = true := by
    rw [hd]
    simp [Lib.dataPcs]
  obtain ⟨kk, rfl⟩ : ∃ kk, k = .tc kk := by
    cases k <;> first | exact ⟨_, rfl⟩ | simp [isTcData] at hd'
  have tc : isTcColl ⟨2328, .tc kk⟩ = true := by
    cases kk <;> simp [isTcData, isTcColl] at hd' ⊢
  obtain ⟨i, w, -, -, -, sta⟩ := Export.st_round hp hX hf base he tc (.inr rfl)
  cases kk <;> simp [tcStatic, Lib.opStatic] at sta ⊢

/-- **The cell the rescale store of a thread writes**: the thread's lane, its half's column. -/
public theorem st_cell (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (base : Iface.BaseRead L X) {g j a : Nat} {sh : TcShape} {vals : List Value}
    (he : X.get (g, j) = some ⟨2328, .tc (.st a vals sh)⟩) (jj : Nat) :
    tcDataCell L g sh a jj = ⟨g / L.block, g % L.block / 32 % 4 * 32 + laneOf L g % 16,
      256 + (if laneOf L g < 16 then 0 else 64) + jj⟩ := by
  obtain ⟨i, kk, -, hs⟩ := st_static hp hX hf base he
  rcases hs with ⟨-, ha, hsh, -⟩ | ⟨h, -⟩
  · rw [ha, hsh]
    exact cell_split L g 256 64 kk jj (by omega)
  · exact absurd h (by decide)

end PTX.Kernels.InklingRelDecode.Proof.Protocol.Values
