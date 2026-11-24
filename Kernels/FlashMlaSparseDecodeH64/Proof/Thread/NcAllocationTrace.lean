-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.NcInputTrace
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.WriteExclusions
import Lemmas.Flow.NotBulk
import Lemmas.Flow.NotNc
import Lemmas.Flow.OpPcsFast
import Lemmas.Flow.WriteSpace

public section

/-! # Non-coherent reads name the canonical global address space -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.NcInputTrace

open PTX PTX.Flow

private def directNc : Op → Bool
  | .mem m => match m.addr.base with
    | .reg _ _ => decide (m.rule = some .threadAccess ∧ m.locSpace? = some .global ∧
        m.kind = .load ∧ m.sem = .weak ∧ m.nc = true)
    | _ => false
  | _ => false

set_option maxRecDepth 100000 in
private theorem direct_sites :
    ∀ j : Fin ncLoads.length, ((kernel.code[ncLoads[j.val]]?).map
      (fun ins => directNc ins.op)).getD false = true := by
  decide +kernel

private theorem direct_shape {tag : Nat} {ins : Instr}
    (hTag : tag ∈ ncLoads) (hc : kernel.code[tag]? = some ins) :
    ∃ m : MemAccess, ins.op = .mem m ∧ m.rule = some .threadAccess ∧
      m.locSpace? = some .global ∧ m.kind = .load ∧ m.sem = .weak ∧ m.nc = true ∧
      ∃ base width, m.addr.base = .reg base width := by
  obtain ⟨j, hj, heq⟩ := List.mem_iff_getElem.mp hTag
  have check := direct_sites ⟨j, hj⟩
  change ((kernel.code[ncLoads[j]]?).map _).getD false = true at check
  rw [heq, hc] at check
  change directNc ins.op = true at check
  cases hop : ins.op with
  | mem m =>
    cases hb : m.addr.base <;> simp only [directNc, hop, hb, Bool.false_eq_true] at check
    case reg base width =>
      obtain ⟨hr, hm, hk, hw, hn⟩ := of_decide_eq_true check
      exact ⟨m, rfl, hr, hm, hk, hw, hn, base, width, hb⟩
  | _ => all_goals simp [directNc, hop] at check

set_option maxRecDepth 100000 in
private theorem nc_op_sites_cover : OpPcsFast kernel.code isNcLoad ncLoads = true := by
  decide +kernel

/-- An ordinary read cannot be fired by one of the kernel's non-coherent loads. -/
theorem ordinary_read_op_not_nc {L : Launch} {g tag : Nat} {t : TState} {ins : Instr}
    {a : Acc} {bs : List (Option Byte)} {o : Option TState}
    (hc : kernel.code[tag]? = some ins)
    (hf : Fires tag (eventTmpl Assumptions.all L g t ins.op) ⟨tag, .rd a bs⟩ o) :
    isNcLoad ins.op = false := by
  cases hn : isNcLoad ins.op
  · rfl
  · obtain ⟨m, hm, hr, hsp, hk, hs, hnc, base, width, hb⟩ :=
      direct_shape (OpPcsFast.mem nc_op_sites_cover hc hn) hc
    rw [hm, eventTmpl, memTmpl_direct_weakLoad hr hsp hb hk hs, loadTmpl, hnc] at hf
    split at hf
    · cases hf.1
    · simp only [↓reduceIte, true_and] at hf
      split at hf
      · obtain ⟨_, _, h, _⟩ := hf
        cases h
      · cases hf.1

private theorem load_global_cta {A : List Assumption} {L : Launch} {g : Nat}
    {t : TState} {m : MemAccess} {base width : Nat} {e : Event} {o : Option TState}
    {a : Acc} {bs : List (Option Byte)}
    (hr : m.rule = some .threadAccess) (hm : m.locSpace? = some .global)
    (hb : m.addr.base = .reg base width) (hk : m.kind = .load) (hw : m.sem = .weak)
    (hf : Fires e.pc (eventTmpl A L g t (.mem m)) e o)
    (he : e.kind = .nc a bs) : a.loc.cta = 0 := by
  rw [eventTmpl, memTmpl_direct_weakLoad hr hm hb hk hw, loadTmpl] at hf
  cases hAddr : effAddr L g t .global base m.addr.off with
  | error f =>
    simp only [hAddr, bind, Except.bind] at hf
    have h := congrArg Event.kind hf.1
    rw [he] at h
    cases h
  | ok loc =>
    simp only [hAddr, bind, Except.bind] at hf
    split at hf
    · have h := congrArg Event.kind hf.1
      rw [he] at h
      cases h
    · rename_i fp hFoot
      have hCta : loc.cta = 0 := by
        simp only [effAddr, bind, Except.bind, pure, Except.pure] at hAddr
        split at hAddr <;> cases hAddr
        rfl
      split at hf
      · split at hf
        · obtain ⟨_, _, h, _⟩ := hf
          have hfp := (Kind.nc.inj (he.symm.trans (congrArg Event.kind h))).1
          rw [hfp]
          exact (elemAcc_local hFoot).2.trans hCta
        · have h := congrArg Event.kind hf.1
          rw [he] at h
          cases h
      · obtain ⟨_, _, h, _⟩ := hf
        have he' := congrArg Event.kind h
        rw [he] at he'
        cases he'

/-- Every actual non-coherent load has its declared footprint and canonical global CTA. -/
theorem allocation_footprint {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    {g i : Nat} {a : Acc} {bs : List (Option Byte)}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (ht : Frame.Tracked (Machine.code P L) X)
    (hRead : X.NcReads (g, i) a bs) : NcInputFootprint P a ∧ a.loc.cta = 0 := by
  obtain ⟨tag, he⟩ := hRead
  rcases PTX.Flow.get_source hX he with ⟨_, h⟩ | ⟨t, ins, o, hTag, hCode, hFire⟩
  · cases h
  have hn : ncLoads.contains tag = true := by
    by_contra habs
    have hNotMem : tag ∉ ncLoads := fun h => habs (List.contains_iff_mem.mpr h)
    have hAllow : Assumptions.all.any (·.ncLoads t.pc) = false := by
      simp [Assumptions.all, Assumptions.idealArith, Assumptions.approx, Assumptions.mulBf16x2,
        Assumptions.cvtBf16x2, Assumptions.cvtUe8m0,
        Assumptions.lg2Exact, Assumptions.ncReadOnly, Assumptions.paramPointers,
        Assumptions.storeDrain, Assumptions.sharedBits, Assumptions.commitOrder,
        Assumption.commitOrderAt, Assumption.idealReal,
        Assumption.approxExact, Assumption.ncReadOnly, hTag, hNotMem]
    exact fires_not_nc hAllow hFire rfl
  refine ⟨footprint hpre hX hs ht he hn rfl, ?_⟩
  obtain ⟨m, hop, hr, hm, hk, hw, _, base, width, hb⟩ :=
    direct_shape (List.contains_iff_mem.mp hn) hCode
  rw [hop] at hFire
  exact load_global_cta hr hm hb hk hw hFire rfl

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.NcInputTrace
