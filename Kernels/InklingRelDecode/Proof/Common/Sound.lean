-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Common.Roles
import Kernels.InklingRelDecode.Proof.Common.WorkerSound
import Kernels.InklingRelDecode.Proof.Common.DataSound
import Lemmas.Flow.GlueU
import Lemmas.Flow.CountedU
public import Kernels.InklingRelDecode.Proof.Startup.Steps

@[expose] public section

namespace PTX.Kernels.InklingRelDecode.Proof
open PTX PTX.Proof PTX.Flow

variable {Q : Params} {L : Launch} {m : Mem0} {g : Nat}

/-- The ABI prefix reaches the first event with the startup's first facts. -/
theorem start (hp : Pre Q L m) :
    ∃ t, Relation.ReflTransGen (Tau kernel Assumptions.all L g) {} t ∧
      (Startup.code Q L g).AtD (Startup.code Q L g).init t ∧
      (Startup.code Q L g).inv (Startup.code Q L g).init := by
  have hblk := hp.block
  have hn : L.ntid = ⟨L.block, 1, 1⟩ := by rw [hp.ntid, hblk]
  obtain ⟨t, hr, ht⟩ := Startup.start0 Q L g hn (by rw [hblk]; decide) (by rw [hblk]; decide)
  have hps : explicitParams L (Startup.startParams Q) = L := by
    apply explicitParams_eq
    intro p v hm
    simp only [Startup.startParams, List.mem_cons, Prod.mk.injEq, List.not_mem_nil,
      or_false] at hm
    rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hp.paramStrideBt
    · exact hp.paramPageRows
    · exact hp.paramHeadRows
    · exact hp.paramHeadCols
    · exact hp.paramSplits
    · exact hp.paramBt
  rw [hps] at hr
  have hk : ∀ r ∈ Flow.live 11, r ∈ [3, 462, 528, 529, 530, 531, 532, 534, 1949, 2020] := by
    decide
  have hF : ∀ d : Startup.D, d.w = b32 0 → ∀ R, Holds R (Startup.preFactsAt L g Q (b32 0) 11) →
      Holds R (Startup.F Q L g 11 d) := by
    intro d hd R h
    apply holds_of_pointwise
    intro r hr
    have hv : Startup.valueOf Q L g d r = Startup.preValueOf L g Q (b32 0) r := by
      have := hk r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at this
      rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [Startup.valueOf, Startup.values, Startup.preValueOf, Startup.table,
          PTX.Flow.lookupLit, hd]
    rw [hv]
    exact holds_mem h (Flow.mem_factsFrom hr)
  by_cases hl : g % L.block < 32
  · refine ⟨t, run_rtg hr, ?_, fun _ => hl⟩
    simp only [Startup.code, Startup.init, hl, ↓reduceIte]
    obtain ⟨hpc, hsub, hacc, hf, hregs⟩ := ht
    exact ⟨hpc, hsub, hacc, hf, hF _ rfl _ hregs⟩
  · have hp3 : (3, Value.pred false) ∈ Startup.preFactsAt L g Q (b32 0) 11 :=
      Startup.tbl_mem (by decide) (by simp [Startup.preValueOf, Startup.table, hl])
    obtain ⟨t', hr', ht'⟩ := Seg.guardSkip (K := kernel) (A := Assumptions.all) (L := L) (g := g)
      Flow.code_11 hp3 (by simp) t ht
    refine ⟨t', (run_rtg hr).trans (run_rtg hr'), ?_, ?_⟩
    · simp only [Startup.code, Startup.init, hl, ↓reduceIte]
      obtain ⟨hpc, hsub, hacc, hf, hregs⟩ := ht'
      refine ⟨hpc, hsub, hacc, hf, ?_⟩
      exact holds_factsFrom_mono (hF ⟨.bar0, 0, 0, b32 0⟩ rfl _ hregs) (by decide)
    · simp [Startup.init, hl, Startup.Inv]

/-- The startup's steps at every state that is not an exit. -/
theorem startup_steps (hp : Pre Q L m) (d : Startup.D) (hx : Startup.enterOf d = none) :
    (Startup.code Q L g).StepAt d := by
  have hb : g % L.block < 256 := hp.block ▸ Nat.mod_lt g (by rw [hp.block]; decide)
  cases hs : d.site with
  | alloc => exact Startup.stepAt_alloc d hs
  | allocWr => exact Startup.stepAt_allocWr d hs
  | bar0 => exact Startup.stepAt_bar0 d hs
  | ld0 => exact Startup.stepAt_ld0 d hs
  | bar1 => exact Startup.stepAt_bar1 hb d hs
  | relinq => exact Startup.stepAt_relinq hb d hs
  | shfl => exact Startup.stepAt_shfl hp d hs
  | enter r => simp [Startup.enterOf, hs] at hx

theorem stub_at (d : Startup.D) (r : Startup.Entry) (h : Startup.enterOf d = some r) :
    (Startup.code Q L g).pc d = r.pc ∧ (Startup.code Q L g).sub d = 0 ∧
      (Startup.code Q L g).acc d = [] := by
  obtain ⟨site, tm, x, bw⟩ := d
  cases site <;> simp [Startup.enterOf] at h
  subst h
  exact ⟨rfl, rfl, rfl⟩

/-- The hand-off of a stub to its role: the role's first state holds at the stub's state. -/
theorem thread_handoff (d : Startup.D) (r : Startup.Entry) (i : Role) (t : TState)
    (hr : Startup.enterOf d = some r) (hs : sel L g r d = some i)
    (hat : (Startup.code Q L g).AtD d t) (_hinv : (Startup.code Q L g).inv d) :
    (frag Q L g i).AtD (frag Q L g i).init t ∧ (frag Q L g i).inv (frag Q L g i).init := by
    obtain ⟨hpc, hsub, hacc⟩ := stub_at (Q := Q) (L := L) (g := g) d r hr
    obtain ⟨ht, hs', ha, hf, hregs⟩ := hat
    cases r with
    | dp =>
      cases hs
      refine ⟨⟨ht.trans hpc,hs'.trans hsub,ha.trans hacc,hf,?_⟩,?_,rfl⟩
      · change Holds t.regs (Prologue.Control.facts Q L g d.w {} 27)
        change Holds t.regs (factsFrom (Flow.live d.site.pc) _) at hregs
        have heq : d.site.pc=27 := hpc
        rw [heq] at hregs
        apply holds_of_pointwise
        intro reg hl
        have full := (List.mem_filter.mp hl).1
        have old := holds_mem hregs (mem_factsFrom full)
        rw [old]
        have keys : Prologue.Control.ctlLive 27 =
            [3,462,463,464,526,527,528,532,1949,2018,2019,2020,2021,2022] := by decide +kernel
        rw [keys] at hl
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hl
        rcases hl with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
        all_goals try rfl
        · change some (.bits 32 (truncBits 32 (BitVec.ofNat 64 Q.strideQ))) =
            some (Prologue.Control.u32 Q.strideQ)
          simp [truncBits,Prologue.Control.u32,b32]
        · change some (.bits 32 (truncBits 32 (BitVec.ofNat 64 Q.strideRel))) =
            some (Prologue.Control.u32 Q.strideRel)
          simp [truncBits,Prologue.Control.u32,b32]
        all_goals
          change some (.bits 64 (truncBits 64 (BitVec.ofNat 64 _))) = some (b64 _)
          simp [truncBits,b64]
          apply BitVec.eq_of_toNat_eq
          simp
      · refine ⟨⟨rfl,rfl,rfl⟩,?_,?_⟩
        · change 41≤27 → _; omega
        · change 130≤27 → _; omega
    | worker =>
      cases hs
      refine ⟨⟨ht.trans hpc, hs'.trans hsub, ha.trans hacc, hf, ?_⟩, ⟨(fun h => by cases h), rfl⟩⟩
      apply holds_of_pointwise
      intro reg hl
      have hk : ∀ r ∈ Flow.live 2337,
          r ∈ [3, 462, 463, 464, 465, 466, 528, 529, 530, 531, 532, 534, 1949, 2020] := by
        decide
      have hpc' : d.site.pc = 2337 := hpc
      change Holds t.regs (factsFrom (Flow.live d.site.pc) _) at hregs
      rw [hpc'] at hregs
      have hreg := holds_mem hregs (mem_factsFrom hl)
      rw [hreg]
      have hm := hk reg hl
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl <;> rfl


theorem thread_sound (hp : Pre Q L m) (hg : g < L.threads) : (thread Q L g).SoundU := by
  apply Code.counted_soundU
  apply Code.glue_soundU (start hp) (fun d hx =>
    (startup_steps hp d (Code.gatedExit_none.mp hx)).toStepAtU)
  · rintro (i | r) d
    · cases i with
      | dispatch => exact worker_steps hp d
      | prologue => exact data_steps hp hg d
    · exact (Code.stop_steps (by cases r <;> decide +kernel) d).toStepAtU
  apply Code.handoff_gated
  · exact fun d r h _ => stub_at d r h
  · intro d r i t hr hs hat hinv
    exact thread_handoff d r i t hr hs hat hinv

end PTX.Kernels.InklingRelDecode.Proof
