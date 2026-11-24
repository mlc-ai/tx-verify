-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof2.Safety.Foot
public import Kernels.InklingRelDecode.Proof2.Lib.KvFoot
public import Kernels.InklingRelDecode.Proof2.Lib.NoEvents

@[expose] public section

/-! # The asynchronous writes on the role table

`copy_spec`: every tensor copy is a KV copy (`EvW.kvCopySpec`) of its thread's CTA, with its
destination box inside the rings (the prologue's, `copyDst_form`) or, for the loader's at a
counter the role table does not bound yet, within 65536 bytes below the rings or wrapped to the
top of the 32-bit space (`EvW.ldDstW_range`). `async_write_loc`: so every asynchronous write
(the kernel's are the tensor copies' tile bytes; it has no bulk copy, no tensor store and no
cancellation response) is a shared byte of the issuing CTA below `sharedBase + 196608` or above
`2 ^ 32 - 65536`: it covers none of the pair, the scratch words, the mbarriers or the role word. -/

namespace PTX.Kernels.InklingRelDecode.Proof2
open PTX PTX.Proof PTX.Flow PTX.Frame

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **Every tensor copy is a KV copy of its CTA into the rings, or near them.** -/
theorem copy_spec (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    {g k pc a : Nat} {s : TensorCopy.Spec}
    (he : X.get (g, k) = some ⟨pc, .tensorIssue a s⟩) :
    ∃ col row dst bar, s = Proof.EvW.kvCopySpec Q (g / L.block) col row dst bar ∧
      ((L.sharedBase ≤ dst + 65536 ∧ dst + 8192 ≤ L.sharedBase + 196608) ∨
        2 ^ 32 - 65536 ≤ dst) := by
  have hg := Frame.lt_of_get hX he
  have hsr := hp.sharedRange
  unfold sharedBytes at hsr
  obtain ⟨σ, t, ins, o, -, hJ, hat, hi, hc, hf⟩ := ev_state hp hX he (fun f h => by cases h)
  cases o with
  | none => exact absurd (fires_none_ends hf) (by simp [Ends])
  | some u =>
    have hev := frag_ev hp hg hJ hat hi hc hf
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
          refine ⟨_, _, _, _, rfl, .inl ?_⟩
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
          have h' : Proof.EvW.LdShapeW Q L g d ⟨pc, .tensorIssue a s⟩ := hev
          unfold Proof.EvW.LdShapeW at h'
          split at h'
          all_goals first
            | (obtain ⟨bx, hb, h'⟩ := h'
               simp only [Event.mk.injEq, Kind.tensorIssue.injEq] at h'
               obtain ⟨-, -, rfl⟩ := h'
               exact ⟨_, _, _, _, rfl, Proof.EvW.ldDstW_range hsr hb⟩)
            | (exfalso; revert h'; simp)
        | worker w => exact (worker_copy w.site hpc).elim
        | idle d => exact (idle_copy d.site hpc).elim
        | mma d P => exact (mma_copy d.site hpc).elim
        | exit x => exact (exitsite_copy x.site hpc).elim
    · exact hJ.elim

/-- **Every asynchronous write is a shared byte of the issuing CTA in or near the rings.** -/
theorem async_write_loc (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    {i : EvId} {p : AsyncCopy.Part} {a : Acc} {bs : List Byte}
    (hw : X.MemWrites (.async i p) a bs) {l : Loc} (hl : a.Covers l) :
    l.space = .shared ∧ l.cta = i.1 / L.block ∧
      ((L.sharedBase ≤ l.addr + 65536 ∧ l.addr < L.sharedBase + 196608) ∨
        2 ^ 32 - 65536 ≤ l.addr) := by
  rcases p with sl | sl | sl | t | _ | _ | _ | r | ⟨isB, index⟩ | _ | _
  all_goals try exact hw.elim
  rcases sl with _ | ⟨x, y, k⟩ | ⟨x, y, k⟩ | c | ⟨x, y, k⟩ | j
  · obtain ⟨s, ⟨pc, he⟩, -⟩ := hw
    exact absurd he (no_copy hX)
  · obtain ⟨o, addr, b, -, ⟨pc, he⟩, hloc, -, hsz, -⟩ := hw
    obtain ⟨col, row, dst, bar, hs, hr⟩ := copy_spec hp hX he
    rw [hs] at hloc
    obtain ⟨h1, h2, h3, h4⟩ := Proof.Ring.Foot.copy_foot Q (i.1 / L.block) col row dst bar hloc
    obtain ⟨hs1, hc, hlo, hhi⟩ := hl
    rw [hsz] at hhi
    refine ⟨hs1.trans h1, hc.trans h2, ?_⟩
    rcases hr with hr | hr
    · exact .inl ⟨by omega, by omega⟩
    · exact .inr (by omega)
  · obtain ⟨o, addr, b, -, ⟨pc, he⟩, -⟩ := hw
    exact absurd he (no_tensorStore hX)
  · obtain ⟨s, targets, ⟨pc, he⟩, -⟩ := hw
    exact absurd he (no_clc hX)
  · exact hw.elim
  · obtain ⟨s, ⟨pc, he⟩, -⟩ := hw
    exact absurd he (no_copy hX)

end
end PTX.Kernels.InklingRelDecode.Proof2
