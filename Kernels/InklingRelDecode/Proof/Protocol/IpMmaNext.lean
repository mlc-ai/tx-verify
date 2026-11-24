-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.IpMmaTrace
public import Kernels.InklingRelDecode.Proof.Protocol.IpLifeCommit

@[expose] public section

/-!
# A commit of the commit-order sites is followed by another commit of its thread

`Life.NextCommit L X` (`IpLifeCommit.lean`): a commit at pc 2546 (`kv_empty`) or 2548 (`o_done`)
of thread `g` is followed, once every thread of its CTA has exited, by another commit event of `g`.

The two sites are `pvCommit1` and `pvCommit2` of the MMA role. The thread is the lane that led the
PV election (`mma_lead`). The role is left only through `setMaxRegInc`, after the election
`finElect`, and the thread leads that election as well (`ElectOk`: one leader for the warp and the
mask, whatever the instances), so it runs `finCommit` before it leaves the role. The thread's last
event is its exit, outside the role.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.IpMma
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX.Kernels.InklingRelDecode.Proof.Life

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **A commit at pc 2546 or 2548 is at `pvCommit1` or `pvCommit2`.** -/
theorem commit_site {g : Nat} {d : Mma.D} {pc : Nat} {sp : TcCommit.Spec}
    (hsh : EvW.MmShape L g d ⟨pc, .tc (.commit sp)⟩) (h : pc = 2546 ∨ pc = 2548) :
    d.site = .pvCommit1 ∨ d.site = .pvCommit2 := by
  unfold EvW.MmShape at hsh
  cases hs : d.site <;> simp only [hs] at hsh <;>
    first
    | (simp at hsh; done)
    | (unfold EvW.QkIssue at hsh
       obtain ⟨_, _, _, _, _, _, hev⟩ := hsh
       simp at hev)
    | (unfold EvW.PvIssue at hsh
       obtain ⟨_, _, _, _, hev⟩ := hsh
       simp at hev)
    | (simp only [Event.mk.injEq] at hsh
       obtain ⟨h1, -⟩ := hsh
       simp [Mma.Site.pc, Flow.tcCommit_0, Flow.tcCommit_3] at h1
       omega)
    | simp

/-- **`NextCommit`.** -/
theorem nextCommit (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) : NextCommit L X := by
  intro g k pc sp he hsites hexit
  have hS := hf.sound
  have hg : g < L.threads := Frame.lt_of_get hX he
  have hk : k < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  obtain ⟨d, P, hσ, hsh⟩ := mma_event_state hpre hX hS hf.tracked hg he (.inr ⟨sp, rfl⟩)
  have hpc : pc = 2546 ∨ pc = 2548 := by
    simpa [Assumptions.commitOrderSites] using hsites
  have hsite := commit_site hsh hpc
  -- the thread's exit
  obtain ⟨pcx, hlast⟩ := hexit g hg rfl
  have hlen : 0 < (X.tr g).length := by omega
  have hkx : (X.tr g).length - 1 < (X.tr g).length := by omega
  have hxget : X.get (g, (X.tr g).length - 1) = some ⟨pcx, .exit⟩ := by
    show (X.tr g)[(X.tr g).length - 1]? = _
    rw [← List.getLast?_eq_getElem?]
    exact hlast
  have hcls := (cls_inv k _ hk.le hσ)
  obtain ⟨x, hxσ⟩ : ∃ x, St Q L X g ((X.tr g).length - 1) = some (some (.w (.exit x))) := by
    rcases exit_event_state hX hS hf.tracked hxget with ⟨dd, hs1, -⟩ | ⟨x, hs1, -⟩
    · exfalso
      have := (cls_inv _ _ (by omega) hs1).mp trivial
      have h2 := hcls.mpr this
      exact h2
    · exact ⟨x, hs1⟩
  -- the thread led the PV election
  have hisPv : isPv d.site = true := by
    rcases hsite with h | h <;> simp [h, isPv]
  obtain ⟨m0, hm0, pc0, inst0, ld0, hel0, hl0⟩ := mma_lead hpre hX hS hg (isX := isPv)
    (el := .pvElect) (Or.inr rfl) rfl (fun h hs => next_pv h hs) k d P hk hσ hisPv
  have hkk : k < (X.tr g).length - 1 := by
    rcases Nat.lt_or_ge k ((X.tr g).length - 1) with h | h
    · exact h
    · have : k = (X.tr g).length - 1 := by omega
      rw [this, hxσ] at hσ
      cases hσ
  have halive : Alive d.site := by
    rcases hsite with h | h <;> simp [h, Alive]
  obtain ⟨k', hk', -, d', P', pc', sp', -, hσ', hs', hget⟩ :=
    fin_commit hpre hX hS hg hkx hxσ (fun _ _ h => by cases h) ⟨m0, pc0, inst0, ld0, hel0, hl0⟩
      _ k d P rfl hkk hσ halive
  refine ⟨k', ?_, sp', pc', hget⟩
  rcases Nat.lt_or_ge k k' with h | h
  · exact h
  · have : k' = k := by omega
    subst this
    rw [hσ] at hσ'
    cases hσ'
    rcases hsite with h | h <;> rw [h] at hs' <;> cases hs'

end
end PTX.Kernels.InklingRelDecode.Proof.IpMma
