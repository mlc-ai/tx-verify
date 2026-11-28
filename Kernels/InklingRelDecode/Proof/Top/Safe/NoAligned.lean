-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Common.Follow
public import Kernels.InklingRelDecode.Proof.Iface.BaseRead
import Kernels.InklingRelDecode.Proof.Lib.StaticCode
import Kernels.InklingRelDecode.Proof.Top.Safe.NoAlignedReg
import Kernels.InklingRelDecode.Proof.Protocol.Shared.ReadValues
import Kernels.InklingRelDecode.Proof.Protocol.Bar.AlignedExit
import Kernels.InklingRelDecode.Proof.Protocol.Bar.AlignedLanes
import Kernels.InklingRelDecode.Proof.Protocol.Tc.Operand
import Kernels.InklingRelDecode.Proof.Protocol.Tc.Exit

@[expose] public section

/-! # ERR-ALIGNED

The kernel has no cluster barrier and no warp matrix instruction (`Lib.noClusterEvent`,
`Lib.noMatrixEvent`), so those two classes are empty. The `tcgen05` collectives are
`Protocol.Tc.not_divergent` and `Protocol.Tc.not_exited`. The `setmaxnreg` class is
`Safe.alignedReg`. The barrier class is `Protocol.Bar.not_divergent` and
`Protocol.Bar.not_exited`. Race freedom, which `Top/Safety.lean` takes from `Safe.noRace`, is
used by the collectives and the barriers; the Tensor Memory object's recorded base is `baseRead`. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Top
open PTX

variable {Q : Params} {L : Launch} {m : Mem0}

theorem Safe.noAligned (hp : Pre Q L m) {X : Execution} (base : Iface.BaseRead L X)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (safe : ¬ Race L X) : ¬ AlignedMismatch L kernel X := by
  rintro ⟨c, hc⟩
  have words : RoleBytes L X := fun he => Protocol.Shared.role_bytes hp hX he
  have none_event (ev : Event) (he : ∃ i, X.get i = some ev) (hm : isCluster ev = true ∨
      isMatrix ev = true) : False := by
    obtain ⟨i, he⟩ := he
    obtain ⟨pc, k⟩ := ev
    rcases hm with hm | hm
    · obtain ⟨op, rfl⟩ := isCluster_kind hm
      exact Lib.noClusterEvent hX he
    · have := Lib.noMatrixEvent hX he
      rw [hm] at this
      cases this
  cases c with
  | tc =>
    rcases hc with hc | hc
    · exact Protocol.Tc.not_divergent hp hX hf safe base hc
    · exact Protocol.Tc.not_exited hp hX hf safe hc
  | bar =>
    rcases hc with hc | hc
    · exact Protocol.Bar.not_divergent hp hX hf words safe hc
    · exact Protocol.Bar.not_exited hp hX hf words hc
  | setMaxReg =>
    rcases hc with hc | hc
    · exact (Safe.alignedReg hp words hX hf).1 hc
    · exact (Safe.alignedReg hp words hX hf).2 hc
  | cluster =>
    rcases hc with ⟨e, f, pe, pf, ke, kf, -, he, -, hme, -⟩ | ⟨e, f, ev, -, he, hme, -⟩
    · exact none_event ⟨pe, ke⟩ ⟨e, he⟩ (.inl hme)
    · exact none_event ev ⟨e, he⟩ (.inl hme)
  | matrix =>
    rcases hc with ⟨e, f, pe, pf, ke, kf, -, he, -, hme, -⟩ | ⟨e, f, ev, -, he, hme, -⟩
    · exact none_event ⟨pe, ke⟩ ⟨e, he⟩ (.inr hme)
    · exact none_event ev ⟨e, he⟩ (.inr hme)

end PTX.Kernels.InklingRelDecode.Proof.Top
