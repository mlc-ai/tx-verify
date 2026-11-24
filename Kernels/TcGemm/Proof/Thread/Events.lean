-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TcGemm.Proof.Interface
public import Kernels.TcGemm.Proof.Thread.Machine

@[expose] public section

/-! # `tc_gemm`: the template and the event of each site

At a concrete state of a followed abstract state, the instruction of its site makes the site's
template (`site_tmpl`), so an event it fires is the site's event (`event_of_tmpl`,
`site_event`). -/

namespace PTX.Kernels.TcGemm.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {L : Launch} {A B D : Nat} {a b : Nat → Nat → Int} {mem0 : Mem0} {g : Nat}

/-- **The template of each site.** -/
theorem site_tmpl (hpre : Pre L A B D a b mem0) (hg : g < L.threads) {d : ThreadD} {t : TState}
    {ins : Instr} (h : (code L A B D g).AtD d t) (hi : Inv g d)
    (hc : kernel.code[d.site.pc]? = some ins) :
    SiteTmpl L A B D g d (eventTmpl [] L g t ins.op) := by
  obtain ⟨s, c, vals⟩ := d
  cases s with
  | alloc =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tmemAlloc_0)
    exact ⟨_, tmpl_alloc hpre hg (hi.warp (.inl rfl)) (tc_reg h.2.2.2.2) h.2.1⟩
  | allocSt =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tmemAlloc_0)
    exact ⟨_, tmpl_allocSt hpre hg (tc_reg h.2.2.2.2) h.2.1⟩
  | init0 =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarInit_0)
    exact ⟨_, tmpl_init0 hpre hg (tc_reg h.2.2.2.2)⟩
  | init1 =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarInit_1)
    exact ⟨_, tmpl_init1 hpre hg (tc_reg h.2.2.2.2)⟩
  | fence =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_fenceProxy_0)
    exact ⟨_, tmpl_fenceProxy⟩
  | arrive =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarArrive_0)
    exact ⟨_, tmpl_arrive hpre hg (tc_reg h.2.2.2.2)⟩
  | bulkA =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_bulkCopy_0)
    exact ⟨_, tmpl_bulkA hpre hg (tc_reg h.2.2.2.2) (tc_reg h.2.2.2.2) (tc_reg h.2.2.2.2)⟩
  | bulkB =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_bulkCopy_1)
    exact ⟨_, tmpl_bulkB hpre hg (tc_reg h.2.2.2.2) (tc_reg h.2.2.2.2) (tc_reg h.2.2.2.2)⟩
  | bar0 z =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_bar_0)
    exact ⟨_, tmpl_bar⟩
  | load z =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_load_0)
    have h11 : t.regs 11 = some (b32 (L.sharedBase + 4368)) := by
      rw [reg_at h.2.2.2.2 (show 11 ∈ liveAt (.load z) by cases z <;> table_decide)]; tc_values
    exact ⟨_, tmpl_load hpre hg h11 h.2.1⟩
  | wait0 =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarWait_0)
    exact ⟨_, tmpl_wait0 hpre hg (tc_reg h.2.2.2.2)⟩
  | mma =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mma_0)
    obtain rfl := hi.zero rfl
    have h4 : t.regs 4 = some (.pred false) := by
      rw [reg_at h.2.2.2.2 (by table_decide)]; tc_values; rfl
    exact ⟨_, tmpl_mma hpre hg hi.col (tc_reg h.2.2.2.2) (tc_reg h.2.2.2.2) (tc_reg h.2.2.2.2)
      (tc_reg h.2.2.2.2) (tc_reg h.2.2.2.2) h4⟩
  | commit =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tcCommit_0)
    exact ⟨_, tmpl_commit hpre hg (tc_reg h.2.2.2.2)⟩
  | wait1 =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarWait_1)
    exact ⟨_, tmpl_wait1 hpre hg (tc_reg h.2.2.2.2)⟩
  | fence1 =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tcFence_0)
    exact ⟨_, tmpl_fenceAfter⟩
  | ld =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tmemLoad_0)
    exact ⟨_, tmpl_ld hpre hg hi.col (tc_reg h.2.2.2.2)⟩
  | waitLd =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tmemWait_0)
    exact ⟨_, tmpl_waitLd hpre⟩
  | st j =>
    have hj := hi.st j rfl
    have hins : ins.op = if j < 4 then storeLo else storeHi := by
      by_cases hj4 : j < 4
      · simp only [Site.pc, hj4, ↓reduceIte] at hc ⊢
        rw [Option.some.inj (hc.symm.trans Flow.code_store_0)]
      · simp only [Site.pc, hj4, ↓reduceIte] at hc ⊢
        rw [Option.some.inj (hc.symm.trans Flow.code_store_1)]
    rw [hins, tmpl_st hpre hg hj h.2.1 (st_47 h.2.2.2.2) (st_regs hj h.2.2.2.2)]
    cases hv : storeValue 32 (word vals j) with
    | ok v' =>
      have hb : stBytes (word vals j) = v'.toBytes := by rw [stBytes, hv]
      exact .inl ⟨⟨v', hv⟩, _, by rw [hb]⟩
    | error f =>
      exact .inr ⟨(fun ⟨v', h⟩ => by rw [hv] at h; cases h), f, rfl⟩
  | fenceB =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tcFence_1)
    exact ⟨_, tmpl_fenceBefore⟩
  | bar1 =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_bar_1)
    exact ⟨_, tmpl_bar⟩
  | fence2 =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tcFence_2)
    exact ⟨_, tmpl_fenceAfter⟩
  | dealloc =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tmemDealloc_0)
    exact ⟨_, tmpl_dealloc hpre hi.col (tc_reg h.2.2.2.2)⟩
  | exit =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_exit_0)
    exact tmpl_exit

/-- **The event of a site's template.** -/
theorem event_of_tmpl {d : ThreadD} {m : Tmpl} {e : Event} {o : Option TState}
    (hm : SiteTmpl L A B D g d m) (hf : Fires d.site.pc m e o) : SiteEvent L A B D g d e := by
  obtain ⟨s, c, vals⟩ := d
  cases s with
  | allocSt =>
    obtain ⟨u, rfl⟩ := hm
    obtain ⟨col, hcol, he, -⟩ := hf
    exact ⟨col, hcol, he⟩
  | load z =>
    obtain ⟨k, rfl⟩ := hm
    obtain ⟨bs, hl, he, -⟩ := hf
    exact ⟨bs, hl, he⟩
  | wait0 =>
    obtain ⟨k, rfl⟩ := hm
    obtain ⟨ok, he, -⟩ := hf
    exact ⟨ok, he⟩
  | wait1 =>
    obtain ⟨k, rfl⟩ := hm
    obtain ⟨ok, he, -⟩ := hf
    exact ⟨ok, he⟩
  | ld =>
    obtain ⟨k, rfl⟩ := hm
    obtain ⟨vs, hl, he, -⟩ := hf
    exact ⟨vs, hl, he⟩
  | st j =>
    rcases hm with ⟨hb, u, rfl⟩ | ⟨hb, f, rfl⟩
    · exact .inl ⟨hb, hf.1⟩
    · exact .inr ⟨hb, f, hf.1⟩
  | exit => subst hm; exact hf.1
  | _ => obtain ⟨u, rfl⟩ := hm; exact hf.1

/-- **The event at a followed state** fired at its site is the site's event. -/
theorem site_event (hpre : Pre L A B D a b mem0) (hg : g < L.threads) {d : ThreadD} {t : TState}
    {ins : Instr} {e : Event} {o : Option TState} (h : (code L A B D g).AtD d t) (hi : Inv g d)
    (hc : kernel.code[d.site.pc]? = some ins) (hf : Fires d.site.pc (eventTmpl [] L g t ins.op) e o)
      :
    SiteEvent L A B D g d e :=
  event_of_tmpl (site_tmpl hpre hg h hi hc) hf

end
end PTX.Kernels.TcGemm.Proof
