-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Lib.Export
public import Kernels.TmlFa4Fwd.Proof.Mma.Export.TmemCount
import Kernels.TmlFa4Fwd.Proof.Common.Sound
import Kernels.TmlFa4Fwd.Proof.Mma.Open
import Kernels.TmlFa4Fwd.Proof.Mma.Export.SafePre
import Kernels.TmlFa4Fwd.Proof.Protocol.Mbar.Init
import Kernels.TmlFa4Fwd.Proof.Protocol.Tmem.Ops
import Kernels.TmlFa4Fwd.Proof.Protocol.Tmem.Word
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The warp-collective `tcgen05` instructions of the MMA warp

They are its three resource operations (`tc_sched`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- The MMA warp's `k`-th resource operation. -/
def resSched (L : Launch) (g : Nat) : Nat → Nat × TcKind
  | 0 => (1909, .resource .one (some ⟨.shared, g / L.block, L.sharedBase + 312⟩) (.alloc 512))
  | 1 => (2763, .resource .one none .relinquish)
  | _ => (2766, .resource .one none (.dealloc 0 512))

set_option maxHeartbeats 4000000 in
/-- The role of the MMA warp has no Tensor Memory load, store or wait. -/
private theorem role_tc {d : Mma.D} {e : Event} (hev : Mma.Ev p L g d e) :
    isTcColl e = Tmem.Pair.isTmemOp e := by
  obtain ⟨site, v⟩ := d
  obtain ⟨pc, kind⟩ := e
  cases site <;> simp only [Mma.Ev] at hev
  case word | down | up | total | vote | pre | tiles =>
    all_goals
      unfold Epilogue.Ev at hev
      split at hev <;> cases kind <;> simp_all [Mma.Site.toE, isTcColl, Tmem.Pair.isTmemOp]
  all_goals shape_destruct hev
  all_goals subst_vars
  all_goals rfl

section
variable (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow p L X)
include hp hX hFw

/-- **The MMA warp's collective `tcgen05` events are its resource operations.** -/
theorem mma_tcColl (hw : Prologue.warpIndex L g = 12) {k : Nat} {e : Event}
    (he : X.get (g, k) = some e) : isTcColl e = Tmem.Pair.isTmemOp e := by
  by_cases hub : ∃ f, e.kind = .ub f
  · obtain ⟨f, hf⟩ := hub
    obtain ⟨pc, kd⟩ := e
    simp only at hf
    subst hf
    rfl
  push Not at hub
  rcases Mma.open_ev hp hX hFw hw he hub with ⟨s, n, -, -, hJ, hi, hev⟩ | ⟨s, n, -, -, -, hev⟩ |
    ⟨d, n, -, -, -, -, hev⟩
  · rw [start_notc hev hi.2, start_nores hev hi.2]
  · obtain ⟨pc, kd⟩ := e
    rcases hev with ⟨_, _, _, hk⟩ | ⟨_, _, _, hk⟩ | ⟨_, _, hk⟩ | ⟨_, hk⟩ <;>
      (simp only at hk; subst hk; rfl)
  · exact role_tc hev

/-- The collective `tcgen05` events of a prefix of a lane of the MMA warp. -/
theorem mma_tcCount (hw : Prologue.warpIndex L g = 12) (k : Nat) :
    ((X.tr g).take k).countP isTcColl = Tmem.Pair.tmemOps ((X.tr g).take k) := by
  refine List.countP_congr fun e he => ?_
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem (List.mem_of_mem_take he)
  rw [mma_tcColl hp hX hFw hw (k := j) (List.getElem?_eq_getElem hj)]

/-- **A lane of the MMA warp makes its `k`-th collective `tcgen05` event as scheduled.** -/
theorem tc_sched (hw : Prologue.warpIndex L g = 12) {k pc : Nat} {tk : TcKind}
    (he : X.get (g, k) = some ⟨pc, .tc tk⟩) (hm : isTcColl ⟨pc, .tc tk⟩ = true) :
    ((X.tr g).take k).countP isTcColl < 3 ∧
      (pc, tk) = resSched L g (((X.tr g).take k).countP isTcColl) := by
  have hg := Frame.lt_of_get hX he
  rw [mma_tcColl hp hX hFw hw he] at hm
  obtain ⟨grp, dst, act, hk⟩ := isTmemOp_eq hm
  simp only [Kind.tc.injEq] at hk
  subst hk
  rw [mma_tcCount hp hX hFw hw]
  have hF := tmem1Facts hp hX hFw
  obtain ⟨-, -, hsh⟩ := hF.event hg he
  refine ⟨Tmem.Pair.lt_of_tmemShape hsh, ?_⟩
  obtain ⟨σ, hσ, hJ, hi, hev⟩ := ev_at hp hX (table_shape_of hp hFw) (table_followed hp hX hFw) he
    (by intro f hf; cases hf)
  obtain ⟨d, n, rfl⟩ := tev_res hJ hi hev rfl
  have hpc : pc = _ := Frame.event_pcU (fun g hg => thread_sound hp hg) hX he hσ
      (fun f h => by cases h)
  have hc := mma_count hp hX hg hw k (List.getElem?_eq_some_iff.mp he).1 _ hσ
  obtain ⟨t, ins, o, hat, hinv, hcd, hf⟩ :=
    Frame.fired_siteU (fun g hg => thread_sound hp hg) hX he hσ (fun f h => by cases h)
  rw [hc]
  rcases d with s0 | ⟨⟨⟩, d⟩
  · have hk3 := Mma.pre_kind hp hat hcd hf
    cases s0 with
    | set => obtain ⟨_, h⟩ := hk3.1 rfl; cases h
    | wr => obtain ⟨_, h⟩ := hk3.2.2 rfl; cases h
    | enter => exact absurd hinv.2 (by simp [Mma.Start.exit])
    | alloc =>
      have h := hk3.2.1 rfl
      simp only [Kind.tc.injEq] at h
      rw [h, hpc]
      rfl
  · have hrd := Mma.ev_res (Mma.mfired hp hX he hσ).1 rfl
    have hkd := Mma.rd_kind hp hat hcd hf (by intro f hf; cases hf)
    obtain ⟨site, v⟩ := d
    cases site <;> simp only [Mma.isRD, reduceCtorEq] at hrd
    · have h := hkd.1 ⟨_, rfl⟩
      simp only [Kind.tc.injEq] at h
      rw [h, hpc]
      rfl
    · obtain ⟨a, h⟩ := hkd.2 ⟨_, rfl⟩
      simp only [Kind.tc.injEq] at h
      rw [h] at he
      obtain rfl := hF.dealloc hg he
      rw [h, hpc]
      rfl

end

end
end PTX.Kernels.TmlFa4Fwd.Proof
