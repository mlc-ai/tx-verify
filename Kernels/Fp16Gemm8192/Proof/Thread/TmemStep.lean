-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Thread.RoleRun
public import Kernels.Fp16Gemm8192.Proof.Thread.TmemDefs
public import Lemmas.Flow.Resource
public import Lemmas.Flow.OpPcsFast

@[expose] public section

/-! # The paired Tensor Memory operations along a thread's run

A paired Tensor Memory operation fires only at a state at one (`tmem_site`, decided on the
code; the allocation's write shares the allocation's instruction and is told apart by its
sub-step). At such a state the instruction fires its operation or undefined behaviour
(`tmem_tmpl`). A step keeps the operations of a thread's events without undefined behaviour
counting its state's (`tmem_step`). The step is one conjunct of the run invariant `ClInv` of
`ClusterCount.lean`. -/

namespace PTX.Kernels.Fp16Gemm8192.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}

/-- The kernel's paired Tensor Memory instructions are at its three sites (decided on the code,
in one pass). -/
theorem kernel_tmem_pcs :
    OpPcsFast kernel.code tmemOp [Flow.tmemAlloc_0, Flow.tmemRelinquish_0, Flow.tmemDealloc_0] =
      true := by
  decide +kernel

/-- A state at a paired Tensor Memory site is at that site's instruction, whose template fires
the operation or undefined behaviour. -/
theorem tmem_tmpl {d : ThreadD} {t : TState} {ins : Instr} (hat : (code L g).AtD d t)
    (h : d.AtTmem) (hc : kernel.code[(code L g).pc d]? = some ins) :
    TmemTmpl .two (eventTmpl Prod L g t ins.op) := by
  rcases d with ⟨site, w⟩ | (l | m | s | c)
  · change site = .alloc at h
    subst h
    change kernel.code[Flow.tmemAlloc_0]? = some ins at hc
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tmemAlloc_0)
    exact tmemTmpl_alloc (by simpa [code, Prologue.sub] using hat.2.1)
  · exact h.elim
  · exact h.elim
  · exact h.elim
  · rcases h with h | h
    · change kernel.code[c.site.pc]? = some ins at hc
      rw [h] at hc
      obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tmemRelinquish_0)
      exact tmemTmpl_relinquish
    · change kernel.code[c.site.pc]? = some ins at hc
      rw [h] at hc
      obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tmemDealloc_0)
      exact tmemTmpl_dealloc

/-- A paired Tensor Memory operation fires at a state at one: the allocation, not its write. -/
theorem tmem_site {d : ThreadD} {t : TState} {ins : Instr} {e : Event} {o : Option TState}
    (hat : (code L g).AtD d t) (hc : kernel.code[(code L g).pc d]? = some ins)
    (hf : Fires ((code L g).pc d) (eventTmpl Prod L g t ins.op) e o) (h : isTmemOp e = true) :
    d.AtTmem := by
  unfold isTmemOp at h
  split at h
  · rename_i grp dst act hk
    have hop := fires_resource_op hf hk
    have hpc := OpPcsFast.mem kernel_tmem_pcs hc hop
    rcases d with ⟨site, w⟩ | (⟨site, m, n, q, cp, r, x⟩ | ⟨site, w', q, fp, ap, cp, r, x⟩ |
        ⟨site, ap, cp, r, x⟩ | ⟨site, mm, n, m', n', cp, ap, resp, x, acc, base⟩)
    · change site.pc ∈ _ at hpc
      cases site
      case alloc => rfl
      case allocWrite =>
        exfalso
        change kernel.code[Flow.tmemAlloc_0]? = some ins at hc
        obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tmemAlloc_0)
        have h1 := (fires_tcAlloc_resource hf hk).1
        have h2 : t.sub = 1 := by simpa [code, Prologue.sub] using hat.2.1
        omega
      all_goals (exfalso; clear * - hpc; revert hpc; decide +revert)
    all_goals change site.pc ∈ _ at hpc
    all_goals (cases site <;> first
      | (simp [ThreadD.AtTmem]; done)
      | (exfalso; clear * - hpc; revert hpc; decide +revert))
  · cases h

/-- The count and the warp of the paired Tensor Memory operations. -/
def TmemInv (w0 : Bool) (d : ThreadD) (es : List Event) : Prop :=
  (NoUb es → tmemOps es = d.tmemOps w0) ∧ d.TmemWarp w0

theorem NoUb.of_append {es : List Event} {e : Event} (h : NoUb (es ++ [e])) :
    NoUb es ∧ ∀ f, e.kind ≠ .ub f :=
  ⟨fun x hx => h x (List.mem_append_left _ hx), h e (List.mem_append_right _ (by simp))⟩

/-- A prologue step off the allocation keeps the count and the warp. -/
theorem Prologue.next_tmem {p : Prologue.D} {e : Event} {d' : ThreadD} {w0 : Bool}
    (hw0 : w0 = decide (g % L.block / 32 = 0))
    (hn : Prologue.next L g p e = some (some d')) (hs : p.site ≠ .alloc)
    (hw : ThreadD.TmemWarp w0 (.inl p)) :
    d'.tmemOps w0 = ThreadD.tmemOps w0 (.inl p) ∧ d'.TmemWarp w0 := by
  subst hw0
  obtain ⟨site, w⟩ := p
  simp only [ThreadD.TmemWarp] at hw
  cases site
  case alloc => exact absurd rfl hs
  all_goals
    simp only [Prologue.next] at hn
    repeat' split at hn
  all_goals first
    | (cases hn; done)
    | (cases hn
       simp_all [ThreadD.tmemOps, ThreadD.TmemWarp, Prologue.afterInits, Prologue.afterElect,
         Prologue.consStart, Consumer.tidOf]; done)
    | (cases hn
       simp_all [ThreadD.tmemOps, ThreadD.TmemWarp, Prologue.afterInits, Prologue.afterElect]
       omega)
    | (cases hn
       simp_all [ThreadD.tmemOps, ThreadD.TmemWarp, Prologue.afterInits, Prologue.afterElect]
       split_ifs <;> simp_all)

/-- A consumer step off the relinquishment and the deallocation keeps the count and the warp. -/
theorem Consumer.next_tmem {c c' : Consumer.D} {e : Event} {w0 : Bool}
    (hw0 : w0 = decide (g % L.block / 32 = 0))
    (hn : Consumer.next L g c e = some (some c')) (hs : c.site ≠ .relinquish)
    (hs' : c.site ≠ .dealloc) (hw : ThreadD.TmemWarp w0 (.inr (.cons c))) :
    ThreadD.tmemOps w0 (.inr (.cons c')) = ThreadD.tmemOps w0 (.inr (.cons c)) ∧
      ThreadD.TmemWarp w0 (.inr (.cons c')) := by
  subst hw0
  obtain ⟨site, m, n, m', n', cp, ap, resp, x, acc, base⟩ := c
  simp only [ThreadD.TmemWarp] at hw
  simp only at hs hs'
  cases site <;> simp only [Consumer.next] at hn
  all_goals repeat' (first | split_ifs at hn | split at hn)
  all_goals (try simp only [Option.some.injEq, reduceCtorEq] at hn)
  all_goals (try (simp only [Option.map_eq_some_iff, Option.some.injEq] at hn; obtain ⟨_, -, rfl⟩ :=
    hn))
  all_goals (try subst hn)
  all_goals (try simp_all [ThreadD.tmemOps, ThreadD.TmemWarp, Consumer.tidOf])
  all_goals (split_ifs <;> omega)

set_option maxHeartbeats 8000000 in
/-- **A step keeps the paired Tensor Memory operations**: the operations of a thread's events
without undefined behaviour count its state's, and only warp 0 holds the states around them. -/
theorem tmem_step {d d' : ThreadD} {t : TState} {ins : Instr} {e : Event} {o : Option TState}
    {pre : List Event} (hat : (code L g).AtD d t) (hc : kernel.code[(code L g).pc d]? = some ins)
    (hf : Fires ((code L g).pc d) (eventTmpl Prod L g t ins.op) e o)
    (hn : (code L g).next d e = some (some d'))
    (hq : TmemInv (decide (g % L.block / 32 = 0)) d pre) :
    TmemInv (decide (g % L.block / 32 = 0)) d' (pre ++ [e]) := by
  obtain ⟨hcnt, hw⟩ := hq
  have hsnoc : tmemOps (pre ++ [e]) = tmemOps pre + (if isTmemOp e then 1 else 0) := by
    simp [tmemOps, List.countP_append]
  by_cases hat' : d.AtTmem
  · -- the operation, or undefined behaviour
    rcases fires_tmemTmpl (tmem_tmpl hat hat' hc) hf with ⟨f, rfl⟩ | ⟨dst, act, rfl⟩
    · refine ⟨fun hnu => ?_, ?_⟩
      · exact absurd rfl ((NoUb.of_append hnu).2 f)
      · rcases d with ⟨site, w⟩ | (l | m | s | c)
        · change site = .alloc at hat'
          subst hat'
          simp [code, Prologue.next] at hn
        · exact hat'.elim
        · exact hat'.elim
        · exact hat'.elim
        · obtain ⟨c', hn', rfl⟩ := next_of_cons hn
          rcases hat' with h | h <;>
            · obtain ⟨site, m, n, m', n', cp, ap, resp, x, acc, base⟩ := c
              simp only at h
              subst h
              simp only [Consumer.next, Option.some.injEq] at hn'
              subst hn'
              simp only [ThreadD.TmemWarp] at hw ⊢
              simp_all
    · simp only [isTmemOp, ↓reduceIte] at hsnoc
      rcases d with ⟨site, w⟩ | (l | m | s | c)
      · change site = .alloc at hat'
        subst hat'
        change kernel.code[Flow.tmemAlloc_0]? = some ins at hc
        obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tmemAlloc_0)
        obtain ⟨-, -, n, -, rfl⟩ := fires_tcAlloc_resource hf rfl
        replace hn : Prologue.next L g ⟨.alloc, w⟩
            ⟨Flow.tmemAlloc_0, .tc (.resource .two dst (.alloc n.toNat))⟩ = some (some d') := hn
        simp only [Prologue.next] at hn
        have hw0 : w = 0 := hw (.inl rfl)
        split_ifs at hn
        all_goals
          cases hn
          refine ⟨fun hnu => ?_, fun _ => hw0⟩
          rw [hsnoc, hcnt (NoUb.of_append hnu).1]
          simp [ThreadD.tmemOps]
      · exact hat'.elim
      · exact hat'.elim
      · exact hat'.elim
      · obtain ⟨c', hn', rfl⟩ := next_of_cons hn
        have hw' : decide (g % L.block / 32 = 0) = true :=
          hw (by rcases hat' with h | h <;> simp [h])
        have h32 : g % L.block < 32 := by simpa using hw'
        rcases hat' with h | h <;>
          · obtain ⟨site, m, n, m', n', cp, ap, resp, x, acc, base⟩ := c
            simp only at h
            subst h
            simp only [Consumer.next, Option.some.injEq] at hn'
            subst hn'
            refine ⟨fun hnu => ?_, ?_⟩
            · rw [hsnoc, hcnt (NoUb.of_append hnu).1]
              simp [ThreadD.tmemOps, h32]
            · simp [ThreadD.TmemWarp, h32]
  · have hne : isTmemOp e = false := by
      by_contra h
      exact hat' (tmem_site hat hc hf (by simpa using h))
    simp only [hne, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at hsnoc
    rcases d with p | (l | m | s | c)
    · have h := Prologue.next_tmem rfl hn (by simpa [ThreadD.AtTmem] using hat') hw
      exact ⟨fun hnu => by rw [hsnoc, hcnt (NoUb.of_append hnu).1, h.1], h.2⟩
    · obtain ⟨l', -, rfl⟩ := next_of_loader hn
      exact ⟨fun hnu => by rw [hsnoc, hcnt (NoUb.of_append hnu).1]; rfl, trivial⟩
    · obtain ⟨m', -, rfl⟩ := next_of_mma hn
      exact ⟨fun hnu => by rw [hsnoc, hcnt (NoUb.of_append hnu).1]; rfl, trivial⟩
    · obtain ⟨s', -, rfl⟩ := next_of_sched hn
      exact ⟨fun hnu => by rw [hsnoc, hcnt (NoUb.of_append hnu).1]; rfl, trivial⟩
    · obtain ⟨c', hn', rfl⟩ := next_of_cons hn
      have hs : c.site ≠ .relinquish ∧ c.site ≠ .dealloc := by
        simp only [ThreadD.AtTmem, not_or] at hat'
        exact hat'
      have h := Consumer.next_tmem rfl hn' hs.1 hs.2 hw
      exact ⟨fun hnu => by rw [hsnoc, hcnt (NoUb.of_append hnu).1, h.1], h.2⟩

end
end PTX.Kernels.Fp16Gemm8192.Proof
