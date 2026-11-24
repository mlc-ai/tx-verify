-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.IpInitStage
public import Kernels.InklingRelDecode.Proof.Thread.EvDProSync

@[expose] public section

/-!
# The prologue's elections and initializations

The prologue's twelve `mbarrier.init` sites `in0 … in11` follow twelve `elect.sync` sites
`el0 … el11` (`ProA.elSite j`, `ProA.inSite j`), and a thread runs `in j` exactly when it is in
warp 0 and the election returned its own lane:

* `v_p40_iff`: `%p40` (the warp index is 0) is `tid < 32`;
* `el_step`: from the site `el j`, the event is an election and the successor is `in j` iff the
  election returned the thread's lane and the thread is in warp 0 (`tid < 32`);
* `in_pred`: the only site before `in j` is `el j`.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.IpInit
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {L : Launch} {g : Nat}

/-- `%p40`, the guard of the initializations, is the thread being in warp 0. -/
theorem v_p40_iff (hb : L.block = 256) (dt : ProA.Dat) :
    ProA.v_p40 L g dt = true ↔ g % L.block < 32 := by
  have h1 : g % L.block < 256 := by rw [hb]; exact Nat.mod_lt _ (by omega)
  unfold ProA.v_p40 ProA.v_r3 ProA.pEqB32
  simp only [truncBits, PTX.compare, BitVec.toNat_ofNat, ProA.tidOf]
  simp
  omega

/-- **The step from an election site**: an election event, and the thread's next site is the
initialization iff the election returned its own lane and it is in warp 0. -/
theorem el_step (hb : L.block = 256) {j : Nat} (hj : j < 12) {dt : ProA.Dat} {e : Event}
    {d' : ProA.D} (h : ProA.next L g ⟨ProA.elSite j, dt⟩ e = some (some d')) :
    ∃ mk inst ld, e.kind = .elect mk inst ld ∧
      (d'.site = ProA.inSite j ↔ (laneOf L g = ld ∧ g % L.block < 32)) := by
  interval_cases j <;>
  · simp only [ProA.elSite, ProA.elSites, ProA.inSite, ProA.inSites, List.getD_cons_zero,
      List.getD_cons_succ, ProA.next] at h ⊢
    split at h
    · rename_i mk inst ld hk
      refine ⟨mk, inst, ld, hk, ?_⟩
      split at h
      · rename_i hc
        simp only [Option.some.injEq] at h
        subst h
        simp only [Bool.and_eq_true, v_p40_iff hb, beq_iff_eq] at hc
        exact ⟨fun _ => ⟨hc.2, hc.1⟩, fun _ => rfl⟩
      · rename_i hc
        simp only [Option.some.injEq] at h
        subst h
        simp only [Bool.and_eq_true, v_p40_iff hb, beq_iff_eq] at hc
        constructor
        · intro h2
          cases h2
        · rintro ⟨h1, h2⟩
          exact absurd ⟨h2, h1⟩ hc
    · simp at h

/-- **The only site before the initialization `in j` is the election `el j`.** -/
theorem in_pred {d d' : ProA.D} {e : Event} (h : ProA.next L g d e = some (some d')) :
    ∀ j < 12, d'.site = ProA.inSite j → d.site = ProA.elSite j := by
  obtain ⟨s, dt⟩ := d
  cases s <;> simp only [ProA.next] at h <;> (repeat' split at h) <;>
    first
    | (simp at h; done)
    | (simp only [Option.some.injEq] at h; subst h; (try simp only [ProA.qSite])
       (repeat' split) <;> decide)

end
end PTX.Kernels.InklingRelDecode.Proof.IpInit
