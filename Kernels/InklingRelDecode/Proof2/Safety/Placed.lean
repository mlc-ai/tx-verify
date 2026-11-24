-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof2.Safety.LdRng
public import Kernels.InklingRelDecode.Proof2.Lib.MmaFoot
public import Lemmas.Flow.NotTcMma

@[expose] public section

/-! # Shared placement on the role table

`sharedPlaced`: every shared byte an access of a consistent execution touches is in a region of a
launched CTA (`Safety.SharedPlaced`). A thread's read or write: `rd_placed`, `wr_placed`. An MMA's
operand read: the event is the MMA warp's (`mma_ev_state`, its shape `EvW.MmShape`), whose
operands are in the rings and the query tile (`Safety.mma_foot`). A tensor copy's write: the copy
is the prologue's (into the rings) or the loader's, whose destination box is in the ring slot
`i % 3` by its counter bounds (`ld_rng`, `ld_shape`, `copy_ring`). The kernel has no other
asynchronous operation with a shared footprint, no atomic and no non-coherent load. -/

namespace PTX.Kernels.InklingRelDecode.Proof2
open PTX PTX.Proof PTX.Flow PTX.Frame
open PTX.Kernels.InklingRelDecode.Proof.Safety (InRegions SharedPlaced)

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- The positions of the MMA warp's MMA and commit instructions. -/
def mmaPcs : List Nat :=
  [Proof.Mma.Site.qkCommit.pc, Proof.Mma.Site.pvCommit1.pc, Proof.Mma.Site.pvCommit2.pc,
    Proof.Mma.Site.finCommit.pc] ++
    (List.finRange 8).map (fun j => (Proof.Mma.Site.qk j).pc) ++
    (List.finRange 8).map (fun j => (Proof.Mma.Site.pv j).pc)

/-- Instructions that issue an MMA or a commit. -/
def mmaLikeOp (op : Op) : Bool := tcMmaOp op || commitOp op

/-- **The MMAs and commits of the program are the MMA warp's.** -/
theorem kernel_mma_pcs : OpPcsFast kernel.code mmaLikeOp mmaPcs = true := by
  decide +kernel

local macro "site_none" : tactic =>
  `(tactic| (intro s h; revert h; cases s <;> (try (rename_i j; revert j)) <;> decide +kernel))

theorem startup_mma : ∀ s : Startup.Site, s.pc ∈ mmaPcs → False := by
  intro s h; revert h
  cases s with
  | enter r => cases r <;> decide
  | _ => decide

theorem proA_mma (s : ProA.Site) (h : s.pc ∈ mmaPcs) : False := by
  cases s with
  | ld k | el k | init k | arr k | psh k | ldq k | st9 k =>
    revert h; revert k; decide
  | pb b j | lb b j | pel b j | ptc b j | stq b j =>
    revert h; revert j; revert b; decide
  | _ => revert h; decide

theorem sm_mma : ∀ s : Proof.Sm.Site, s.pc ∈ mmaPcs → False := by site_none
theorem epi_mma : ∀ s : Proof.Epi.Site, s.pc ∈ mmaPcs → False := by site_none
theorem worker_mma : ∀ s : Proof.Worker.Site, s.pc ∈ mmaPcs → False := by site_none
theorem idle_mma : ∀ s : Proof.Worker.Idle.Site, s.pc ∈ mmaPcs → False := by site_none
theorem loader_mma : ∀ s : Proof.Loader.Site, s.pc ∈ mmaPcs → False := by site_none
theorem exitsite_mma : ∀ s : Proof.WComp.ExitSite, s.pc ∈ mmaPcs → False := by site_none

/-- **An MMA event is fired from a state of the MMA warp**, with the warp's shape. -/
theorem mma_ev_state (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    {g k pc c : Nat} {spec : TcMma.OperandSpec} {acc : Bool} {mask : List Nat}
    (he : X.get (g, k) = some ⟨pc, .tc (.mma c spec acc mask)⟩) :
    ∃ tm d P n, Frame.stateAt (thread Q L) X g k =
        some (some (.inr ⟨.inl (.worker tm), .mma d P⟩, n)) ∧
      Proof.EvW.MmShape L g d ⟨pc, .tc (.mma c spec acc mask)⟩ := by
  have hg := Frame.lt_of_get hX he
  obtain ⟨σ, t, ins, o, hσ, hJ, hat, hi, hc, hf⟩ := ev_state hp hX he (fun f h => by cases h)
  cases o with
  | none => exact absurd (fires_none_ends hf) (by simp [Ends])
  | some u =>
    have hev := frag_ev hp hg hJ hat hi hc hf
    have hop : mmaLikeOp ins.op = true := by simp [mmaLikeOp, fires_tcMma_op hf rfl]
    have hpc := OpPcsFast.mem kernel_mma_pcs hc hop
    obtain ⟨x, n⟩ := σ
    rcases x with st | ⟨_ | r, d⟩
    · exact (startup_mma st.site hpc).elim
    · rename_i i
      cases i with
      | dp tm bw =>
        rcases d with d | ⟨_ | _, τ⟩
        · exact (proA_mma d.site hpc).elim
        · cases τ with
          | sm d => exact (sm_mma d.site hpc).elim
          | epi d => exact (epi_mma d.site hpc).elim
        · exact hJ.elim
      | worker w =>
        cases d with
        | mma d P => exact ⟨w, d, P, n, hσ, hev⟩
        | worker w => exact (worker_mma w.site hpc).elim
        | idle d => exact (idle_mma d.site hpc).elim
        | loader d P => exact (loader_mma d.site hpc).elim
        | exit x => exact (exitsite_mma x.site hpc).elim
    · exact hJ.elim

/-- **Every tensor copy is a KV copy of its CTA into the rings.** -/
theorem copy_ring (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    {g k pc a : Nat} {s : TensorCopy.Spec}
    (he : X.get (g, k) = some ⟨pc, .tensorIssue a s⟩) :
    ∃ col row dst bar, s = Proof.EvW.kvCopySpec Q (g / L.block) col row dst bar ∧
      L.sharedBase ≤ dst ∧ dst + 8192 ≤ L.sharedBase + 196608 := by
  have hg := Frame.lt_of_get hX he
  have hsr := hp.sharedRange
  unfold sharedBytes at hsr
  obtain ⟨σ, t, ins, o, hσ, hJ, hat, hi, hc, hf⟩ := ev_state hp hX he (fun f h => by cases h)
  cases o with
  | none => exact absurd (fires_none_ends hf) (by simp [Ends])
  | some u =>
    have hop : tensorOp ins.op = true := by
      cases hq : tensorOp ins.op
      · exact absurd rfl (fires_notTensor (eventTmpl_notTensor hq) hf a s)
      · rfl
    have hpc := OpPcsFast.mem kernel_copy_pcs hc hop
    obtain ⟨x, n⟩ := σ
    rcases x with st | ⟨_ | r, d⟩
    · exact (startup_copy st.site hpc).elim
    · rename_i i
      cases i with
      | dp tm bw =>
        rcases d with d | ⟨_ | _, τ⟩
        · obtain ⟨b, j, hs⟩ := proA_copy d.site hpc
          have hx : d.site ≠ .exit := by rw [hs]; simp
          have hF := ProA.fired_old (P := Startup.inh L g Q tm) hx hat hi.1 hc hf
          obtain ⟨-, -, hP, -⟩ := (hJ : ProRef Q L g tm bw d n)
          have hmap : d.dt.pro.rest 1949 = .ptr 64 true (.param (param "1")) 0 := by
            rw [hP.pro]; rfl
          have hi12 : 4 * b.val + j.val < 12 := by omega
          have he' := Proof.ProA.ptc_event_map hp (i := 4 * b.val + j.val) hi12 hmap hF
            (by simp only [ProA.D.old, hs, ptc_old])
          simp only [Event.mk.injEq, Kind.tensorIssue.injEq] at he'
          obtain ⟨-, -, rfl⟩ := he'
          refine ⟨_, _, _, _, rfl, ?_⟩
          have hsb : Proof.ProA.SbRoom L := by unfold Proof.ProA.SbRoom; omega
          rw [show (ProA.D.old d).dt = d.dt from rfl, Proof.ProA.copyDst_form L g d.dt hsb hi12]
          have h1 := Proof.ProA.half_lt d.dt ((4 * b.val + j.val) / 4)
          have h2 : (4 * b.val + j.val) / 4 < 3 := by omega
          have h3 : (4 * b.val + j.val) % 2 < 2 := Nat.mod_lt _ (by omega)
          have h4 : (4 * b.val + j.val) % 4 / 2 < 2 := by omega
          constructor
          · omega
          · have : 16384 * Proof.ProA.half d.dt ((4 * b.val + j.val) / 4) +
                32768 * ((4 * b.val + j.val) / 4) + 98304 * ((4 * b.val + j.val) % 2) +
                8192 * ((4 * b.val + j.val) % 4 / 2) + 8192 ≤ 196608 := by omega
            omega
        · cases τ with
          | sm d => exact (sm_copy d.site hpc).elim
          | epi d => exact (epi_copy d.site hpc).elim
        · exact hJ.elim
      | worker w =>
        cases d with
        | loader d P =>
          have h' := ld_shape hp hX he (by simp [Ends]) hσ
          unfold Proof.EvW.LdShape at h'
          split at h'
          all_goals first
            | (obtain ⟨bx, hb, h'⟩ := h'
               simp only [Event.mk.injEq, Kind.tensorIssue.injEq] at h'
               obtain ⟨-, -, rfl⟩ := h'
               refine ⟨_, _, _, _, rfl, ?_⟩
               rename_i hsite
               have hb' : bx.2.1 < 2 ∧ bx.2.2 < 2 := by
                 rw [hsite] at hb
                 simp only [Proof.EvW.ldBox, Option.some.injEq] at hb
                 subst hb
                 decide
               have hm : d.i % 3 < 3 := Nat.mod_lt _ (by omega)
               simp only [Proof.EvW.ldDst]
               split_ifs <;> omega)
            | (exfalso; revert h'; simp)
        | worker w => exact (worker_copy w.site hpc).elim
        | idle d => exact (idle_copy d.site hpc).elim
        | mma d P => exact (mma_copy d.site hpc).elim
        | exit x => exact (exitsite_copy x.site hpc).elim
    · exact hJ.elim

/-- The source location of a tensor load byte is a global byte. -/
theorem sourceLoc_global {outer : Nat} {d : TensorDescriptor.Descriptor outer}
    {o : Fin (outer + 1) → Int} {r : Option (Fin 4 → Int)} {x y k : Nat} {l : Loc}
    (h : TensorTransfer.sourceLoc d o r x y k = some l) : l.space = .global := by
  unfold TensorTransfer.sourceLoc at h
  simp only [bind, Option.bind_eq_some_iff, Option.some.injEq] at h
  obtain ⟨-, -, -, -, rfl⟩ := h
  rfl

theorem inRegions_ring {l : Loc} (hs : l.space = .shared) (hlo : L.sharedBase ≤ l.addr)
    (hhi : l.addr < L.sharedBase + 196608) : InRegions L l := by
  by_cases h : l.addr < L.sharedBase + 4
  · exact .inl ⟨hs, hlo, h⟩
  · exact .inr (.inl ⟨hs, by omega, hhi⟩)

/-- **Shared placement of every access of a consistent execution.** -/
theorem sharedPlaced (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X) :
    SharedPlaced L X := by
  intro e a l hmt hc hsp
  have hsa : a.loc.space = .shared := hc.1.symm.trans hsp
  have hcta : ∀ {g : Nat}, g < L.threads → l.cta = g / L.block → l.cta < L.grid := by
    intro g hg h
    rw [h]
    exact NamedBar.cta_lt hg
  rcases hmt with ⟨w, hI⟩ | ⟨i, bs, rfl, pc, hn⟩
  · rcases e with i | ⟨i, p⟩
    · -- a thread's access
      rcases hI with ⟨bs, ⟨pc, he⟩, -⟩ | ⟨bs, ⟨pc, he⟩, -⟩ | ⟨old, new, pc, he⟩
      · obtain ⟨g, k⟩ := i
        exact (rd_placed hp hX he hsa hc).2
      · obtain ⟨g, k⟩ := i
        exact (wr_placed hp hX he hsa hc).2
      · exact absurd he (no_rmw hX)
    · -- a stage of an asynchronous operation
      obtain ⟨-, hfp⟩ := hI
      cases p with
      | mmaRead isB index =>
        obtain ⟨hsz, hmf⟩ := hfp
        rcases hmf with ⟨d, s, acc, mask, ⟨pc, he⟩, hb⟩ | ⟨c, k, cta, hcp, -⟩
        · have hg := Frame.lt_of_get hX he
          obtain ⟨tm, dd, P, n, -, hsh⟩ := mma_ev_state hp hX he
          obtain ⟨hB, hA⟩ := Proof.Safety.mma_foot hp hsh
          obtain ⟨-, hc2, hlo, hhi⟩ := hc
          cases isB
          · obtain ⟨h1, h2, h3, h4⟩ := hA _ _ hb
            refine ⟨hcta hg (hc2.trans h2), ?_⟩
            exact .inr (.inr (.inl ⟨hsp, by omega, by omega⟩))
          · obtain ⟨h1, h2, h3, h4⟩ := hB _ _ hb
            refine ⟨hcta hg (hc2.trans h2), ?_⟩
            exact inRegions_ring hsp (by omega) (by omega)
        · exact absurd hcp (no_cp hX _ _)
      | readLoad x y k =>
        obtain ⟨s, addr, -, hloc, -⟩ := hfp
        have h := sourceLoc_global hloc
        rw [h] at hsa
        exact absurd hsa (by simp)
      | readCopy =>
        rcases hfp with ⟨s, ⟨pc, he⟩, -⟩ | ⟨pc, he⟩
        · exact absurd he (no_copy hX)
        · exact absurd he (no_bulkPrefetch hX)
      | readStore x y k =>
        obtain ⟨s, addr, ⟨pc, he⟩, -⟩ := hfp
        exact absurd he (no_tensorStore hX)
      | readPrefetch x y k =>
        obtain ⟨s, addr, ⟨pc, he⟩, -⟩ := hfp
        exact absurd he (no_tensorPrefetch hX)
      | writeLoad x y k =>
        obtain ⟨s, addr, ⟨pc, hget⟩, hloc, hsz⟩ := hfp
        have hg := Frame.lt_of_get hX hget
        obtain ⟨col, row, dst, bar, hs, hr1, hr2⟩ := copy_ring hp hX hget
        rw [hs] at hloc
        obtain ⟨h1, h2, h3, h4⟩ := Proof.Ring.Foot.copy_foot Q (i.1 / L.block) col row dst bar hloc
        obtain ⟨-, hc2, hlo, hhi⟩ := hc
        refine ⟨hcta hg (hc2.trans h2), ?_⟩
        exact inRegions_ring hsp (by omega) (by omega)
      | writeStore x y k =>
        obtain ⟨s, addr, ⟨pc, he⟩, -⟩ := hfp
        exact absurd he (no_tensorStore hX)
      | writeCta c =>
        obtain ⟨s, targets, ⟨pc, he⟩, -⟩ := hfp
        exact absurd he (no_clc hX)
      | writeCopy =>
        obtain ⟨s, ⟨pc, he⟩, -⟩ := hfp
        exact absurd he (no_copy hX)
      | writeElem j =>
        obtain ⟨s, ⟨pc, he⟩, -⟩ := hfp
        exact absurd he (no_copy hX)
      | oldStore x y k =>
        obtain ⟨s, r, ⟨pc, he⟩, -⟩ := hfp
        exact absurd he (no_tensorStore hX)
      | oldElem j =>
        obtain ⟨s, r, ⟨pc, he⟩, -⟩ := hfp
        exact absurd he (no_copy hX)
      | readCta c => exact hfp.elim
      | readElem j => exact hfp.elim
      | writePrefetch x y k => exact hfp.elim
      | oldCopy => exact hfp.elim
      | oldLoad x y k => exact hfp.elim
      | oldCta c => exact hfp.elim
      | oldPrefetch x y k => exact hfp.elim
      | notifyCopy => exact hfp.elim
      | notifyLoad => exact hfp.elim
      | notifyCta c => exact hfp.elim
      | readsDone => exact hfp.elim
      | fullDone => exact hfp.elim
      | resolve => exact hfp.elim
      | tcNotify r => exact hfp.elim
      | mmaDone => exact hfp.elim
      | arriveOn => exact hfp.elim
  · exact absurd hn (no_nc hX)

end
end PTX.Kernels.InklingRelDecode.Proof2
