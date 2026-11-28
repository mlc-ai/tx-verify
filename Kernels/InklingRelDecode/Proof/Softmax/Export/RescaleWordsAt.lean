-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Common.Follow
public import Lemmas.Flow.OutKinds
public import Kernels.InklingRelDecode.Proof.Lib.RoundWords
import Kernels.InklingRelDecode.Proof.Softmax.Export.AlphaOperand
import Kernels.InklingRelDecode.Proof.Softmax.Data.RoundNum
import Kernels.InklingRelDecode.Proof.Common.SoftSite
import Kernels.InklingRelDecode.Proof.Common.LaunchLane

/-! # The words of the rescale store are numbers

The store of pc 2328 writes the rescale factor times the words of the accumulator load
(`rescale_store`). The factor is a number (`alphaWord_has`, from the words of the rounds), so the
words are numbers when the loaded words are. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Export
open PTX PTX.Proof PTX.Flow Control Data

variable {Q : Params} {L : Launch} {g : Nat}

/-- **Every word of the rescale store is a single-precision number**, when the words of the
accumulator loads before it are and the words of the rounds are numbers or `-inf`. -/
public theorem rescale_event {m : Mem0} {X : Execution} {k a : Nat} {vals : List Value}
    {sh : TcShape} (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hR : g % L.block < 128 → ∀ p ∈ roundWords X g k, SK.ni.Has p.1 ∧ SK.ni.Has p.2)
    (hov : ∀ j < k, ∀ a' ov sh', X.get (g, j) = some ⟨2260, .tc (.ld a' ov sh')⟩ →
      ∀ x ∈ ov, ∃ r : ℝ, x = .float .f32 r)
    (get : X.get (g, k) = some ⟨2328, .tc (.st a vals sh)⟩) :
    ∀ v ∈ vals, ∃ r : ℝ, v = .float .f32 r := by
  have clean : ∀ f, (Event.mk 2328 (.tc (.st a vals sh))).kind ≠ .ub f := fun _ => nofun
  obtain ⟨w, ent, d, n, hsc, -⟩ := at_site hp hX get clean (by show 574 < 2328; omega)
    (by show 2328 < 2331; omega)
  have lane : g % L.block < 128 := data_warp hp hX (List.getElem?_eq_some_iff.mp get).1.le hsc
  obtain ⟨hl, j, hj, a', ov, sh', hg, hlen, hv⟩ := rescale_store hp hX get
  obtain ⟨-, x, hx⟩ := alphaWord_has hp (hR lane)
  intro v hvm
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hvm
  have e := hv i (hl ▸ hi)
  rw [List.getElem?_eq_getElem hi] at e
  have hmem : ov.getD i (b32 0) ∈ ov := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
    exact List.getElem_mem _
  obtain ⟨r, hr⟩ := hov j hj a' ov sh' hg _ hmem
  rw [hr, mulE_reads hx (readEReal_float r) (mulEReal_coe x r), erealValue_coe] at e
  exact ⟨x * r, by simpa [okVal] using Option.some.inj e⟩

end PTX.Kernels.InklingRelDecode.Proof.Softmax.Export
