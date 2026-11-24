-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Thread.NextKind
public import Lemmas.Kernel.Frame
public import Mathlib.Tactic.DeriveFintype

@[expose] public section

/-! # A thread fires the event of its site's kind

The instruction at each site is one its kind accepts (`site_kindOp`, decided over the sites of
each role). A thread whose run ends in a state of the machine reaches, by local steps, a
concrete state of it, whose template is the event of the instruction at its site
(`Frame.end_at`): undefined behaviour or a template of the site's kind
(`fire_fact`). The allocation instruction fires the allocation at its first sub-step (the
allocation site) and the write of its column at its second (the write site). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof
open PTX PTX.Flow

noncomputable section

deriving instance Fintype for Prologue.Site
deriving instance Fintype for Loader.Site
deriving instance Fintype for Mma.Site
deriving instance Fintype for Consumer.Site

/-- Whether the instruction at `pc` is one kind `k` accepts. -/
def siteOk (k : NextKind) (pc : Nat) : Bool :=
  (kernel.code[pc]?).any fun ins => kindOp k ins.op

theorem prologue_sites : ∀ s : Prologue.Site, siteOk (prologueKind s) s.pc = true := by
  decide +kernel

theorem loader_sites : ∀ s : Loader.Site, siteOk (loaderKind s) s.pc = true := by
  decide +kernel

theorem mma_sites : ∀ s : Mma.Site, siteOk (mmaKind s) s.pc = true := by
  decide +kernel

theorem sched_sites (s : Scheduler.Site) : siteOk (schedKind s) s.pc = true := by
  cases s <;> decide +kernel

theorem cons_sites : ∀ s : Consumer.Site, siteOk (consKind s) s.pc = true := by
  decide +kernel

/-- **The instruction at a state's site is one its kind accepts.** -/
theorem site_kindOp {L : Launch} {g : Nat} (d : ThreadD) {ins : Instr}
    (hc : kernel.code[(code L g).pc d]? = some ins) : kindOp (nextKind d) ins.op = true := by
  have h : siteOk (nextKind d) ((code L g).pc d) = true := by
    rcases d with p | (l | m | s | c)
    · exact prologue_sites p.site
    · exact loader_sites l.site
    · exact mma_sites m.site
    · exact sched_sites s.site
    · exact cons_sites c.site
  simpa [siteOk, hc] using h

/-- The allocation instruction. -/
def allocOp : Op → Bool
  | .tcAlloc .. => true
  | _ => false

theorem prologue_alloc : ∀ s : Prologue.Site, (kernel.code[s.pc]?).all
    (fun ins => !allocOp ins.op || decide (s = .alloc) || decide (s = .allocWrite)) = true := by
  decide +kernel

theorem loader_no_alloc : ∀ s : Loader.Site,
    (kernel.code[s.pc]?).all (fun ins => !allocOp ins.op) = true := by
  decide +kernel

theorem mma_no_alloc : ∀ s : Mma.Site,
    (kernel.code[s.pc]?).all (fun ins => !allocOp ins.op) = true := by
  decide +kernel

theorem sched_no_alloc (s : Scheduler.Site) :
    (kernel.code[s.pc]?).all (fun ins => !allocOp ins.op) = true := by
  cases s <;> decide +kernel

theorem cons_no_alloc : ∀ s : Consumer.Site,
    (kernel.code[s.pc]?).all (fun ins => !allocOp ins.op) = true := by
  decide +kernel

/-- **The allocation instruction is at the prologue's allocation and write sites only.** -/
theorem alloc_site {L : Launch} {g : Nat} {d : ThreadD} {ins : Instr}
    (hc : kernel.code[(code L g).pc d]? = some ins) (ha : allocOp ins.op = true) :
    ∃ p : Prologue.D, d = .inl p ∧ (p.site = .alloc ∨ p.site = .allocWrite) := by
  rcases d with p | (l | m | s | c)
  · have h := prologue_alloc p.site
    change (kernel.code[p.site.pc]?).all _ = true at h
    change kernel.code[p.site.pc]? = some ins at hc
    simp only [hc, Option.all_some, ha, Bool.not_true, Bool.false_or, Bool.or_eq_true,
      decide_eq_true_eq] at h
    exact ⟨p, rfl, h⟩
  all_goals exfalso
  · have h := loader_no_alloc l.site
    change kernel.code[l.site.pc]? = some ins at hc
    simp [hc, ha] at h
  · have h := mma_no_alloc m.site
    change kernel.code[m.site.pc]? = some ins at hc
    simp [hc, ha] at h
  · have h := sched_no_alloc s.site
    change kernel.code[s.site.pc]? = some ins at hc
    simp [hc, ha] at h
  · have h := cons_no_alloc c.site
    change kernel.code[c.site.pc]? = some ins at hc
    simp [hc, ha] at h

/-- **A thread whose run ends in a machine state fires the event of its site's kind**: after
local steps it is at a concrete state of the machine state, whose template is undefined
behaviour or of the site's kind. -/
theorem fire_fact {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}
    (hpre : Pre P L mem0) (hg : g < L.threads) {d : ThreadD} {t : TState}
    (hσ : Frame.stateAt (code L) X g (X.tr g).length = some (some d))
    (hr : Run kernel Prod L g {} (X.tr g) (some t)) :
    ∃ t1 m, Relation.ReflTransGen (Tau kernel Prod L g) t t1 ∧ (code L g).AtD d t1 ∧
      out kernel Prod L g t1 = .ev m ∧ ((∃ f, m = .ub f) ∨ KindTmpl L g (nextKind d) m) := by
  obtain ⟨t1, ins, hl, hat, -, hc, hout⟩ := Frame.end_at (fun _ => sound hpre) hg hr hσ
  refine ⟨t1, _, hl, hat, hout, ?_⟩
  rcases eventTmpl_opTmpl (A := Prod) (L := L) (g := g) (t := t1) ins.op with hub | hev
  · exact .inl hub
  refine .inr (kindTmpl_of (site_kindOp d hc) hev ?_)
  intro grp b o nc hop
  obtain ⟨p, rfl, hs⟩ := alloc_site hc (by rw [hop]; rfl)
  have hsub : t1.sub = Prologue.sub p := hat.2.1
  rw [hop]
  refine ⟨fun hk => ?_, fun hk => ?_⟩
  · have hs' : p.site = .allocWrite := by
      rcases hs with hs | hs
      · simp [nextKind, prologueKind, hs] at hk
      · exact hs
    exact eventTmpl_alloc_sub (by simp [hsub, Prologue.sub, hs'])
  · have hs' : p.site = .alloc := by
      rcases hs with hs | hs
      · exact hs
      · simp [nextKind, prologueKind, hs] at hk
    intro dst t hw
    have h := tmemTmpl_alloc (A := Prod) (L := L) (g := g) (group := grp) (base := b) (off := o)
      (nc := nc) (t := t1) (by simp [hsub, Prologue.sub, hs'])
    rw [hw] at h
    exact h

end
end PTX.Kernels.Fp16Gemm8192.Proof
