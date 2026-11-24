-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Thread.PollRead
public import Kernels.Fp16Gemm8192.Proof.Thread.Fire
public import Lemmas.Flow.Region

@[expose] public section

/-! # Where a thread accesses memory

The memory a thread reads and writes, by the site it fires from: static facts of the site machine,
from the instruction at the site and the register holding its address. A read is fired at a site
of the read kind (`read_kind`): a role's load of its CTA's response buffer (`clcLoad_read`), or the
consumer's load of the Tensor Memory base word at the start of its CTA's shared window
(`ldBase_read`). A write is fired by a consumer (its staging stores) or by the Tensor Memory
allocation, writing the base word (`write_site`, `alloc_write`): no other role's site stores. A
tensor store is fired at a consumer's TMA store site (`tensorStore_cons`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof

open PTX PTX.Proof PTX.Flow

noncomputable section

set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}

/-- The prologue stores only at the allocation (decided on the code). -/
theorem prologue_stores : ∀ s : Prologue.Site,
    (kernel.code[s.pc]?).all (fun ins => !writeOp ins.op || allocOp ins.op) = true := by
  decide +kernel

theorem loader_stores : ∀ s : Loader.Site,
    (kernel.code[s.pc]?).all (fun ins => !writeOp ins.op) = true := by
  decide +kernel

theorem mma_stores : ∀ s : Mma.Site, (kernel.code[s.pc]?).all (fun ins => !writeOp ins.op) = true :=
    by
  decide +kernel

theorem sched_stores (s : Scheduler.Site) :
    (kernel.code[s.pc]?).all (fun ins => !writeOp ins.op) = true := by
  cases s <;> decide +kernel

/-- **The stores of the kernel are the consumer's and the allocation.** -/
theorem write_site {d : ThreadD} {ins : Instr} (hc : kernel.code[(code L g).pc d]? = some ins)
    (hw : writeOp ins.op = true) : (∃ c, d = .inr (.cons c)) ∨ allocOp ins.op = true := by
  rcases d with p | (l | m | s | c)
  · have h := prologue_stores p.site
    change kernel.code[p.site.pc]? = some ins at hc
    simp only [hc, Option.all_some, hw, Bool.not_true, Bool.false_or] at h
    exact .inr h
  all_goals try exact .inl ⟨_, rfl⟩
  all_goals exfalso
  · have h := loader_stores l.site
    change kernel.code[l.site.pc]? = some ins at hc
    simp [hc, hw] at h
  · have h := mma_stores m.site
    change kernel.code[m.site.pc]? = some ins at hc
    simp [hc, hw] at h
  · have h := sched_stores s.site
    change kernel.code[s.site.pc]? = some ins at hc
    simp [hc, hw] at h

/-- The allocation's write is of the Tensor Memory base word, at the start of the thread's CTA's
shared window. -/
theorem alloc_write (hpre : Pre P L mem0) {p : Prologue.D} (hs : p.site = .alloc ∨ p.site =
    .allocWrite)
    {t : TState} {ins : Instr} {e : Event} {o : Option TState}
    (hat : (code L g).AtD (.inl p) t) (hc : kernel.code[(code L g).pc (.inl p)]? = some ins)
    (hf : Fires ((code L g).pc (.inl p)) (eventTmpl Prod L g t ins.op) e o) :
    ∀ a bs, e.kind = .wr a bs → a.loc = ⟨.shared, g / L.block, L.sharedBase⟩ ∧ a.size = 4 := by
  have hbase := hpre.sharedRange
  unfold sharedBytes at hbase
  obtain ⟨site, w⟩ := p
  have hr : t.regs 90 = some (b32 L.sharedBase) := by
    rcases hs with hs | hs <;> simp only at hs <;> subst hs <;>
      exact (holds_mem hat.2.2.2.2 (Flow.mem_factsFrom (by lit_mem))).trans
        (congrArg some (by pro_values))
  have hpc : (code L g).pc (.inl ⟨site, w⟩) = Flow.tmemAlloc_0 := by
    rcases hs with hs | hs <;> simp only at hs <;> subst hs <;> rfl
  rw [hpc] at hc hf
  code_at hc
  subst hc
  exact fires_tcAlloc_wr (effAddr_b32 hr (by omega)) hf

/-- The consumer's load of the Tensor Memory base word reads the four bytes at the start of its
CTA's shared window. -/
theorem Consumer.ldBase_read (hpre : Pre P L mem0) {c : Consumer.D} (hs : c.site = .ldBase)
    {t : TState} {ins : Instr} {e : Event} {o : Option TState}
    (hat : (code L g).AtD (.inr (.cons c)) t) (hc : kernel.code[c.site.pc]? = some ins)
    (hf : Fires c.site.pc (eventTmpl Prod L g t ins.op) e o) :
    ∀ a bs, e.kind = .rd a bs → a.loc = ⟨.shared, g / L.block, L.sharedBase⟩ ∧ a.size = 4 := by
  have hbase := hpre.sharedRange
  unfold sharedBytes at hbase
  obtain ⟨site, mm, n, m', n', cp, ap, resp, x, acc, base⟩ := c
  simp only at hs
  subst hs
  code_at hc
  subst hc
  have hr : t.regs 873 = some (b32 L.sharedBase) :=
    (holds_mem hat.2.2.2.2 (Flow.mem_factsFrom (by lit_mem))).trans
      (congrArg some (by cons_values))
  exact fires_ld_rd (effAddr_b32 hr (by omega)) hat.2.1 hf

/-- A read is fired at a site of the read kind. -/
theorem read_kind {d : ThreadD} {t : TState} {ins : Instr} {pc : Nat} {e : Event}
    {o : Option TState} (hc : kernel.code[(code L g).pc d]? = some ins)
    (hf : Fires pc (eventTmpl Prod L g t ins.op) e o) {a : Acc} {bs : List (Option Byte)}
    (hk : e.kind = .rd a bs) : nextKind d = .read := by
  obtain ⟨epc, ek⟩ := e
  simp only at hk
  subst hk
  obtain ⟨kk, hm⟩ := fires_read_tmpl hf
  rcases eventTmpl_opTmpl (A := Prod) (L := L) (g := g) (t := t) ins.op with ⟨f, hub⟩ | hev
  · rw [hub] at hm
    cases hm
  rw [hm] at hev
  have h := kindTmpl_of (site_kindOp d hc) hev
    (fun _ _ _ _ _ => ⟨fun _ => trivial, fun _ _ _ h => by cases h⟩)
  cases hn : nextKind d <;> rw [hn] at h <;> simp [KindTmpl] at h ⊢

/-- A tensor store is fired at a consumer's TMA store site. -/
theorem tensorStore_cons {d : ThreadD} {t : TState} {ins : Instr} {pc : Nat} {e : Event}
    {o : Option TState} (hc : kernel.code[(code L g).pc d]? = some ins)
    (hf : Fires pc (eventTmpl Prod L g t ins.op) e o) {a : Nat} {sp : TensorStore.Spec}
    (hk : e.kind = .tensorStore a sp) : ∃ c, d = .inr (.cons c) := by
  have hop := fires_tensorStore_op hf hk
  have hko := site_kindOp d hc
  have hn : nextKind d = .tensorStore := by
    cases h : ins.op <;> rw [h] at hop hko <;> simp only [tensorStoreOp, Bool.false_eq_true] at hop
    cases hn : nextKind d <;> rw [hn] at hko <;> simp [kindOp] at hko ⊢
  rcases d with p | (l | m | s | c)
  · cases hs : p.site <;> simp [nextKind, prologueKind, hs] at hn
  · cases hs : l.site <;> simp [nextKind, loaderKind, hs] at hn
  · cases hs : m.site <;> simp [nextKind, mmaKind, hs] at hn
  · cases hs : s.site <;> simp [nextKind, schedKind, hs] at hn
  · exact ⟨c, rfl⟩

/-- **Where a thread accesses memory**, by the state it fires from: it reads its CTA's response
buffer or the Tensor Memory base word; it writes the base word, or is a consumer; it issues tensor
stores as a consumer. -/
theorem access_fact {X : Execution} (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    {k : Nat} {e : Event} {d : ThreadD} (he : X.get (g, k) = some e)
    (hσ : Frame.stateAt (code L) X g k = some (some d)) :
    (∀ a bs, e.kind = .rd a bs →
      (a.loc = ⟨.shared, g / L.block, L.sharedBase + 144⟩ ∧ a.size = 16) ∨
        (a.loc = ⟨.shared, g / L.block, L.sharedBase⟩ ∧ a.size = 4)) ∧
    (∀ a bs, e.kind = .wr a bs → (∃ c, d = .inr (.cons c)) ∨
      (a.loc = ⟨.shared, g / L.block, L.sharedBase⟩ ∧ a.size = 4)) ∧
    (∀ a sp, e.kind = .tensorStore a sp → ∃ c, d = .inr (.cons c)) := by
  obtain ⟨t, ins, o, hat, -, hc, hf⟩ := Frame.fired_site (fun _ => sound hpre) hX he hσ
  refine ⟨fun a bs hk => ?_, fun a bs hk => ?_, fun a sp hk => tensorStore_cons hc hf hk⟩
  · have hn := read_kind hc hf hk
    rcases d with p | (l | m | s | c)
    · cases hs : p.site <;> simp [nextKind, prologueKind, hs] at hn
    · have hl : l.site = .clcLoad := by
        cases hs : l.site <;> simp [nextKind, loaderKind, hs] at hn ⊢
      obtain ⟨a', bs', hk', ha, hsz⟩ := clcLoad_read hpre (d := .inr (.loader l)) hl hat hc hf
      rw [hk] at hk'
      cases hk'
      exact .inl ⟨ha, hsz⟩
    · have hl : m.site = .clcLoad := by
        cases hs : m.site <;> simp [nextKind, mmaKind, hs] at hn ⊢
      obtain ⟨a', bs', hk', ha, hsz⟩ := clcLoad_read hpre (d := .inr (.mma m)) hl hat hc hf
      rw [hk] at hk'
      cases hk'
      exact .inl ⟨ha, hsz⟩
    · have hl : s.site = .clcLoad := by
        cases hs : s.site <;> simp [nextKind, schedKind, hs] at hn ⊢
      obtain ⟨a', bs', hk', ha, hsz⟩ := clcLoad_read hpre (d := .inr (.sched s)) hl hat hc hf
      rw [hk] at hk'
      cases hk'
      exact .inl ⟨ha, hsz⟩
    · have hl : c.site = .clcLoad ∨ c.site = .ldBase := by
        cases hs : c.site <;> simp [nextKind, consKind, hs] at hn ⊢
      rcases hl with hl | hl
      · obtain ⟨a', bs', hk', ha, hsz⟩ := clcLoad_read hpre (d := .inr (.cons c)) hl hat hc hf
        rw [hk] at hk'
        cases hk'
        exact .inl ⟨ha, hsz⟩
      · exact .inr (Consumer.ldBase_read hpre hl hat hc hf a bs hk)
  · rcases write_site hc (fires_write_op hf hk) with hcons | halloc
    · exact .inl hcons
    obtain ⟨p, rfl, hs⟩ := alloc_site hc halloc
    exact .inr (alloc_write hpre hs hat hc hf a bs hk)

end
end PTX.Kernels.Fp16Gemm8192.Proof
