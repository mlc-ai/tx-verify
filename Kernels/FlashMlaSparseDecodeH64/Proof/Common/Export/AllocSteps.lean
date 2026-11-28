-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.Regions
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Launch
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MbarRows.Startup
public import Lemmas.Kernel.Progress.Rank
public import Lemmas.Kernel.Progress.NextEv
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Where
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.AllocAt
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.FollowStep
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.RegTime
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.Tmem
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.Tmem

@[expose] public section

/-! # The time table after the allocation

The time table's facts a lane blocked at a performed but unpublished allocation needs:

* `alloc_pc`: an allocation request is the startup's (warpgroup 0's resource operation is the
  deallocation, `wg0_deallocOps`);
* `alloc_next_wr`: lane 0's event after its allocation is the store of the word at pc 91;
* `alloc_earlier`: when two lanes' last events are their allocations, lane 0 (at the store,
  time 93) is earlier than any other lane (at the read-back, time 94). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow MbarRow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

section
variable (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow P L X)
include hp hX hFw

/-- **An allocation request is the startup's.** -/
theorem alloc_pc {k pc n : Nat} {grp : CtaGroup} {dst : Option Loc} (hg : g < L.threads)
    (ha : X.get (g, k) = some ⟨pc, .tc (.resource grp dst (.alloc n))⟩) : StartupAt pc := by
  rcases (tmem_res (tmem_rows hp hX hFw) hg ha rfl).2 with ⟨h, -⟩ | ⟨h, -⟩
  · exact h
  · obtain ⟨-, h2, -⟩ := wg0_deallocOps hp hX hFw ha h rfl
    cases h2

/-- **Lane 0's event after its allocation is the store of the word**, at the allocation's pc. -/
theorem alloc_next_wr (hnu : ¬ HasUb X) {k pc n : Nat} {grp : CtaGroup} {dst : Option Loc}
    {f : Event} (ha : X.get (g, k) = some ⟨pc, .tc (.resource grp dst (.alloc n))⟩)
    (hpc : StartupAt pc) (hl : PTX.laneOf L g = 0) (hf : X.get (g, k + 1) = some f) :
    pc = 91 ∧ ∃ bytes,
      f = ⟨91, .wr { loc := wsLoc L (g / L.block) Region.tmemWord.lo, size := 4 } bytes⟩ := by
  obtain ⟨h91, x1, x2, n', hσ⟩ := alloc_state hp hX hFw ha hpc
  simp only [hl, ↓reduceIte] at hσ
  obtain ⟨σ, hσ', hJ, hi, hev, hpc'⟩ := ev_at hp hX hFw hf (noUb_kind hnu hf)
  rw [hσ] at hσ'
  cases hσ'
  have hf91 : f.pc = 91 := by rw [hpc']; rfl
  obtain ⟨d, n, hd, -, -, hE, -, -⟩ := startup_state hJ hi hev hpc' (by rw [hf91]; decide)
  simp only [Prod.mk.injEq, Sum.inl.injEq] at hd
  obtain ⟨rfl, rfl⟩ := hd
  obtain ⟨col, -, hk⟩ := hE
  obtain ⟨fpc, fk⟩ := f
  simp only at hf91 hk
  subst hf91 hk
  exact ⟨h91, _, rfl⟩

/-- **Lane 0 after its allocation is earlier than another lane after its own.** -/
theorem alloc_earlier {h kh kg pch pcg nh ng : Nat} {grp grp' : CtaGroup}
    {dst dst' : Option Loc}
    (hah : X.get (h, kh) = some ⟨pch, .tc (.resource grp dst (.alloc nh))⟩) (hph : StartupAt pch)
    (hlh : (X.tr h).length = kh + 1) (hl0 : PTX.laneOf L h = 0)
    (hag : X.get (g, kg) = some ⟨pcg, .tc (.resource grp' dst' (.alloc ng))⟩)
    (hpg : StartupAt pcg) (hlg : (X.tr g).length = kg + 1) (hl : PTX.laneOf L g ≠ 0) :
    Sched.threadTime (timed P L) X h < Sched.threadTime (timed P L) X g := by
  obtain ⟨-, x1, x2, n1, h1⟩ := alloc_state hp hX hFw hah hph
  obtain ⟨-, y1, y2, n2, h2⟩ := alloc_state hp hX hFw hag hpg
  rw [← hlh] at h1
  rw [← hlg] at h2
  rw [timed_eq, Sched.threadTime_of h1, Sched.threadTime_of h2]
  simp [hl0, hl, time, Startup.time, Startup.Site.pc]

end

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
