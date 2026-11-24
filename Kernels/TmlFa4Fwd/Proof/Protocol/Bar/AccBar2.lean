-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Top.JR
public import Core.Assembly.Execution
public import Core.Data.Types
public import Core.Data.Value
public import Kernels.TmlFa4Fwd.Assumptions
public import Kernels.TmlFa4Fwd.Proof.Common.Roles
public import Kernels.TmlFa4Fwd.Proof.Correction.Machine
public import Kernels.TmlFa4Fwd.Proof.Correction.Shape
public import Kernels.TmlFa4Fwd.Proof.Epilogue.Machine
public import Kernels.TmlFa4Fwd.Proof.Epilogue.Shape
public import Kernels.TmlFa4Fwd.Proof.Loader.Machine
public import Kernels.TmlFa4Fwd.Proof.Loader.Shape
public import Kernels.TmlFa4Fwd.Proof.SmWarp.Export.Follow
public import Kernels.TmlFa4Fwd.Proof.Softmax.Machine
public import Kernels.TmlFa4Fwd.Proof.Softmax.Shape
public import Kernels.TmlFa4Fwd.Proof.Startup.Machine
public import Kernels.TmlFa4Fwd.Proof.Startup.Shape
public import Kernels.TmlFa4Fwd.Proof.Protocol.Bar.Bar2Corr
public import Kernels.TmlFa4Fwd.Proof.Protocol.Bar.Bar2Soft
public import Kernels.TmlFa4Fwd.Spec
public import Lemmas.CtaBarrier.CtaBarrierIdSourceCount
import Kernels.TmlFa4Fwd.Proof.Protocol.Bar.Count
import Kernels.TmlFa4Fwd.Proof.Top.JRStub
import Kernels.TmlFa4Fwd.Proof.Protocol.Mbar.Init
import Kernels.TmlFa4Fwd.Proof.Mma.Export.Entry

@[expose] public section

/-! # Every Tensor Memory access follows a barrier-2 event of its lane

An MMA, `tcgen05.ld` or `tcgen05.st` event (`IsAcc`) is fired from a state of the MMA warp's code
at an issue site, or from a softmax or correction state at a Tensor Memory site (`soft_acc`,
`corr_acc`; the other shape tables have none). The MMA warp's code states other than `bar1`
follow the lane's `bar.sync 2, 416` (`mma_bar1_before`); the softmax and correction lanes have
made one barrier-2 event at those sites (`soft_tc_bar2`, `corr_tc_bar2`). So every access has a
barrier-2 event of its lane before it (`acc_bar2`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- A Tensor Memory access kind: an MMA, a load or a store. -/
def IsAcc : Kind → Prop
  | .tc (.mma ..) => True
  | .tc (.ld ..) => True
  | .tc (.st ..) => True
  | _ => False

theorem epi_noacc {d : Epilogue.D} {pc : Nat} {k : Kind} (hk : IsAcc k)
    (hev : Epilogue.Ev p L g d ⟨pc, k⟩) : False := by
  unfold Epilogue.Ev at hev
  split at hev <;> rcases k with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ |
    _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ <;>
    simp_all [Epilogue.isStore, IsAcc]

set_option maxHeartbeats 4000000 in
theorem ld_noacc {w : Nat} {d : Loader.D} {pc : Nat} {k : Kind} (hk : IsAcc k)
    (hev : Loader.Ev p L g w d ⟨pc, k⟩) : False := by
  obtain ⟨s, rest⟩ := d
  cases s <;> simp only [Loader.Ev] at hev
  all_goals first | exact (epi_noacc hk hev).elim | skip
  all_goals (try split at hev)
  all_goals shape_destruct hev
  all_goals (try subst_vars)
  all_goals simp_all [IsAcc]

theorem start_noacc {s : Startup.D} {n : Cls → Nat} (hJ : JR p L g (.inl s, n)) {pc : Nat}
    {k : Kind} (hk : IsAcc k) (hev : Startup.Ev L g s ⟨pc, k⟩) : False := by
  obtain ⟨site, x1, x2, x3⟩ := s
  cases site
  case bar => simp only [Startup.Ev, Kind.bar.injEq] at hev; subst hev; exact hk
  case enter r => exact absurd rfl (jr_start_site hJ r)
  case sh j =>
    fin_cases j <;> simp only [Startup.Ev] at hev <;> obtain ⟨_, _, hk'⟩ := hev <;> subst hk' <;>
      exact hk
  all_goals simp only [Startup.Ev] at hev
  all_goals first
    | (subst hev; exact hk)
    | (rcases hev with ⟨_, _, -, hk'⟩ | ⟨_, hk'⟩ <;> subst hk' <;> exact hk)
    | (rcases hev with ⟨_, _, hk'⟩ | ⟨_, hk'⟩ <;> subst hk' <;> exact hk)

set_option maxHeartbeats 8000000 in
/-- A softmax access is fired at a Tensor Memory site. -/
theorem soft_acc {d : Softmax.D} {pc : Nat} {k : Kind} (hk : IsAcc k)
    (hev : Softmax.Ev p L g d ⟨pc, k⟩) : d.site.isTc = true := by
  obtain ⟨s, v, kk, acc⟩ := d
  cases s
  all_goals first | rfl | skip
  all_goals exfalso
  all_goals simp only [Softmax.Ev] at hev
  all_goals first | exact (epi_noacc hk hev).elim | skip
  all_goals (try split at hev)
  all_goals shape_destruct hev
  all_goals (try subst_vars)
  all_goals simp_all [IsAcc, Softmax.rdOrUb, Softmax.tcLdOrUb]

set_option maxHeartbeats 8000000 in
/-- A correction access is fired at a Tensor Memory site. -/
theorem corr_acc {d : Correction.D} {pc : Nat} {k : Kind} (hk : IsAcc k)
    (hev : Correction.Ev p L g d ⟨pc, k⟩) : d.site.isTc = true := by
  obtain ⟨s, v, kk⟩ := d
  cases s
  all_goals first | rfl | skip
  all_goals exfalso
  all_goals simp only [Correction.Ev] at hev
  all_goals first | exact (epi_noacc hk hev).elim | skip
  all_goals (try split at hev)
  all_goals shape_destruct hev
  all_goals (try subst_vars)
  all_goals simp_all [IsAcc, Correction.rdOrUb]

/-- A barrier-2 event before position `f` counts. -/
theorem bar2_pos {h j f pc : Nat} {cnt : Option Nat} {mode : BarMode} (hjf : j < f)
    (hj : X.get (h, j) = some ⟨pc, .bar 2 cnt mode⟩) :
    1 ≤ ((X.tr h).take f).countP (Execution.isBarId 2) := by
  have hmem : (⟨pc, .bar 2 cnt mode⟩ : Event) ∈ (X.tr h).take f := by
    have hj' : (X.tr h)[j]? = some ⟨pc, .bar 2 cnt mode⟩ := hj
    rw [← List.getElem?_take_of_lt hjf] at hj'
    exact List.mem_of_getElem? hj'
  exact List.countP_pos_iff (p := Execution.isBarId 2) |>.mpr ⟨_, hmem, rfl⟩

set_option maxHeartbeats 8000000 in
/-- **Every Tensor Memory access follows a barrier-2 event of its lane.** -/
theorem acc_bar2 (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) {f pc : Nat} {k : Kind}
    (hk : IsAcc k) (he : X.get (g, f) = some ⟨pc, k⟩) :
    1 ≤ ((X.tr g).take f).countP (Execution.isBarId 2) := by
  have hub : ∀ fl, (⟨pc, k⟩ : Event).kind ≠ .ub fl := by
    rintro fl rfl; exact hk
  obtain ⟨⟨σ1, n⟩, hσ, hJ, hi, hev⟩ :=
    ev_at hp hX (table_shape_of hp hFw) (table_followed hp hX hFw) he hub
  rcases σ1 with s | ⟨i, d⟩
  · exact (start_noacc hJ hk hev).elim
  cases i with
  | epilogue => exact (epi_noacc hk hev).elim
  | loader b => exact (ld_noacc hk hev).elim
  | stub r =>
    exact (jr_stub hJ).elim
  | softmax =>
    have := soft_tc_bar2 hp hX hFw he hσ (soft_acc hk hev.1)
    omega
  | correction =>
    have := corr_tc_bar2 hp hX hFw he hσ
      (corr_acc hk (hev.1.data_or_vote.resolve_right (by rintro ⟨_,_,rfl⟩; exact hk)))
    omega
  | mma =>
    rcases d with s | ⟨⟨⟩, d⟩
    · exfalso
      rcases hev with ⟨_, _, _, hk'⟩ | ⟨_, _, _, hk'⟩ | ⟨_, _, hk'⟩ | ⟨_, hk'⟩ <;>
        simp only at hk' <;> subst hk' <;> exact hk
    · have hs : d.site ≠ .bar1 := by
        intro hs
        obtain ⟨s0, v0⟩ := d
        simp only at hs
        subst hs
        simp only [TEv, Mma.Ev] at hev
        subst hev
        exact hk
      obtain ⟨j, hj, pc', hget⟩ := mma_bar1_before hp hX he hσ hs
      exact bar2_pos hj hget

end
end PTX.Kernels.TmlFa4Fwd.Proof
