-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.WriteExclusions
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0Epilogue
import Lemmas.Flow.OpPcsFast
import Lemmas.Flow.WriteSpace

public section

/-! # Ordinary shared writes stay in the issuing CTA -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.RoleSharedWrites

open PTX PTX.Flow

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

private def localWriteOp : Op → Bool
  | .mem m => match m.rule, m.locSpace?, m.addr.base with
    | some .threadAccess, some _, .reg .. => decide (m.kind = .store ∧ m.sem = .weak)
    | _, _, _ => false
  | .tcAlloc .. => true
  | _ => false

private def stageSites : List Nat :=
  (List.finRange 4).flatMap fun j => (List.finRange 8).map fun k => (Wg0.Site.oStage j k).pc

set_option maxRecDepth 100000 in
private theorem write_sites :
    OpPcsFast kernel.code (fun op => writeOp op && !localWriteOp op) stageSites = true := by
  decide +kernel

private theorem stage_site {s : Wg0.Site} (h : s.pc ∈ stageSites) :
    ∃ j k, s = .oStage j k := by
  cases s with
  | oStage j k => exact ⟨j, k, rfl⟩
  | _ =>
    all_goals
      exfalso
      revert h
      first | decide | (rename_i a; revert a; decide) | (rename_i a b; revert a b; decide)

private theorem stage_role {g : Nat} {d : Machine.ThreadD}
    (h : (Machine.code P L g).pc d ∈ stageSites) :
    ∃ w j k, d = .wg0 w ∧ w.site = .oStage j k := by
  cases d with
  | wg0 s =>
    obtain ⟨j, k, hk⟩ := stage_site h
    exact ⟨s, j, k, rfl, hk⟩
  | head => exact absurd h (by change 1843 ∉ stageSites; decide)
  | done => exact absurd h (by change 3611 ∉ stageSites; decide)
  | prologue s =>
    change s.pc ∈ stageSites at h
    exfalso
    cases s <;> revert h <;> first | decide | (rename_i a; revert a; decide)
  | idle s =>
    change s.pc ∈ stageSites at h
    exfalso
    cases s <;> revert h <;> decide
  | mma d =>
    change d.site.pc ∈ stageSites at h
    exfalso
    generalize d.site = s at h
    clear d
    cases s <;> revert h <;> first | decide | (rename_i a; revert a; decide)
  | tma d =>
    change d.site.pc ∈ stageSites at h
    exfalso
    generalize d.site = s at h
    clear d
    cases s <;> revert h <;>
      first | decide | (rename_i a; revert a; decide) | (rename_i a b; revert a b; decide)
  | index d =>
    change d.site.pc ∈ stageSites at h
    exfalso
    generalize d.site = s at h
    clear d
    cases s <;> revert h <;> first | decide | (rename_i a; revert a; decide) |
      (rename_i a b; revert a b; decide) | (rename_i a b c; revert a b c; decide)
  | wg2 d =>
    change d.site.pc ∈ stageSites at h
    exfalso
    generalize d.site = s at h
    clear d
    cases s <;> revert h <;> first | decide | (rename_i a b; revert a b; decide)

private theorem from_store {L : Launch} {g base w : Nat} {off : Int}
    {t u : TState} {srcs : List Opnd} {sp : Space} {a : Acc} {bs : List Byte}
    (hs : a.loc.space = .shared)
    (h : storeTmpl L g t sp w base off srcs = .write a bs u) :
    a.loc.cta = ctaOf L g := by
  unfold storeTmpl at h
  split at h
  · cases h
  · rename_i a' hacc
    cases hloc : effAddr L g t sp base off with
    | error f => simp [hloc, bind, Except.bind] at hacc
    | ok loc =>
      simp only [hloc, bind, Except.bind] at hacc
      repeat' (first | split at h | (cases h; done))
      simp only [Tmpl.write.injEq] at h
      obtain ⟨rfl, -, -⟩ := h
      have hElem := elemAcc_local hacc
      have hSpace := effAddr_space hloc
      have hShared : sp = .shared := hSpace.symm.trans (hElem.1.symm.trans hs)
      rw [hShared] at hloc
      exact hElem.2.trans (sharedEffAddr_local hloc).2

private theorem from_alloc {L : Launch} {g base : Nat} {off : Int} {count : Opnd}
    {group : CtaGroup} {t u : TState} {loc : Loc}
    (h : tcTmpl L g t (.tcAlloc group base off count) = .tcAllocStore loc u) :
    loc.cta = ctaOf L g := by
  simp only [tcTmpl, bind, Except.bind, pure, Except.pure, throw, throwThe,
    MonadExceptOf.throw] at h
  repeat' (first | split at h | (simp [ofExec] at h; done))
  simp only [ofExec, Tmpl.tcAllocStore.injEq] at h
  obtain ⟨rfl, -⟩ := h
  exact (sharedEffAddr_local (by assumption)).2

private theorem from_local {A : List Assumption} {L : Launch} {g pc tag : Nat}
    {t : TState} {op : Op} {a : Acc} {bs : List Byte} {o : Option TState}
    (hl : localWriteOp op = true)
    (hf : Fires pc (eventTmpl A L g t op) ⟨tag, .wr a bs⟩ o)
    (hs : a.loc.space = .shared) :
    a.loc.cta = ctaOf L g := by
  cases op <;> simp only [localWriteOp, Bool.false_eq_true] at hl
  case mem m =>
    split at hl
    · rename_i sp base width hr hm hb
      obtain ⟨hk, hsem⟩ := of_decide_eq_true hl
      rw [eventTmpl, memTmpl_direct_weakStore hr hm hb hk hsem] at hf
      rcases fires_write_tmpl hf with ⟨u, hv⟩ | ⟨u, hv, -⟩
      · exact from_store hs hv
      · have hm := storeTmpl_isMem (L := L) (g := g) (t := t) (sp := sp)
          (w := m.elem.width) (base := base) (off := m.addr.off) (srcs := m.srcs)
        rw [hv] at hm
        exact hm.elim
    · cases hl
  case tcAlloc group base off count =>
    rcases fires_write_tmpl hf with ⟨u, hv⟩ | ⟨u, hv, -⟩
    · simp only [eventTmpl, tcTmpl, bind, Except.bind, pure, Except.pure, throw, throwThe,
        MonadExceptOf.throw] at hv
      repeat' (first | split at hv | simp [ofExec] at hv)
    · exact from_alloc hv

/-- An ordinary shared write at an identified thread state belongs to the issuing CTA. -/
theorem shared_cta_of_state (hpre : Pre P L mem0) (hs : GlobalWrites.SoundThreads P L)
    (hX : Consistent L kernel Assumptions.all mem0 X) {i : EvId} {tag : Nat}
    {a : Acc} {bs : List Byte} {d : Machine.ThreadD}
    (he : X.get i = some ⟨tag, .wr a bs⟩)
    (hd : Frame.stateAt (Machine.code P L) X i.1 i.2 = some (some d))
    (hshared : a.loc.space = .shared) :
    a.loc.cta = ctaOf L i.1 := by
  obtain ⟨t, ins, o, ha, hi, hc, hf⟩ := Frame.fired_site hs hX he hd
  by_cases hlocal : localWriteOp ins.op = true
  · exact from_local hlocal hf hshared
  have hw := fires_write_op hf rfl
  have hSite := OpPcsFast.mem write_sites hc (by simp [hw, hlocal])
  obtain ⟨d, j, k, rfl, hStage⟩ := stage_role hSite
  have hg := Frame.lt_of_get hX he
  have hc' : kernel.code[(Wg0.Site.oStage j k).pc]? = some ins := by
    rw [← hStage]
    exact hc
  obtain rfl := Option.some.inj (hc'.symm.trans (Wg0.stage_code j k))
  rw [Wg0.event_oStage hpre hg ha hi hStage] at hf
  have hLoc : a = {
      loc := Wg0.shLoc L i.1 (Wg0.stageWrite L i.1 j.val k.val t.sub)
      size := 4, elem := t.sub } :=
    (Kind.wr.inj (congrArg Event.kind hf.1)).1
  rw [hLoc]
  rfl

/-- Every ordinary shared write in a tracked execution belongs to the issuing CTA. -/
theorem shared_cta (hpre : Pre P L mem0) (hs : GlobalWrites.SoundThreads P L)
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (ht : Frame.Tracked (Machine.code P L) X)
    {i : EvId} {a : Acc} {bs : List Byte}
    (hw : X.Writes i a bs) (hshared : a.loc.space = .shared) :
    a.loc.cta = ctaOf L i.1 := by
  obtain ⟨_, he⟩ := hw
  obtain ⟨_, hd⟩ := Frame.event_state hs hX ht he (by simp)
  exact shared_cta_of_state hpre hs hX he hd hshared

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.RoleSharedWrites
