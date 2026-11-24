-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TcGemm.Proof.Thread.Tmpl
public import Lemmas.Flow.Code
public import Lemmas.Flow.Next

@[expose] public section

/-! # `tc_gemm`: the steps of the issue

Each site up to the read of the address as a step of the abstract machine: after its event,
local steps reach a concrete state of the successor. Warp 0's allocation continues on lane 0 into
the address store and elsewhere to the first barrier; thread 0 then loads its parameters and
issues; the read of the address keeps its low 16 bits (`and.b32`), or is undefined behaviour when
its bytes are no word, and branches to `bar0`'s poll on thread 0 and to `bar1`'s elsewhere. -/

namespace PTX.Kernels.TcGemm.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {L : Launch} {A B D : Nat} {a b : Nat → Nat → Int} {mem0 : Mem0} {g : Nat}

/-- What a step of the machine owes. -/
abbrev Step (L : Launch) (A B D g : Nat) (d : ThreadD) (u : TState) (e : Event) : Prop :=
  ((code L A B D g).next d e = some none ∨ ∃ d' t', (code L A B D g).next d e = some (some d') ∧
      Relation.ReflTransGen (Tau kernel [] L g) u t' ∧ (code L A B D g).Good (some d') t') ∨
    ((code L A B D g).next d e = none ∧ Machine.Dead (K := kernel) (A := []) (L := L) (g := g) u)

theorem step_to {d d' : ThreadD} {u t' : TState} {e : Event} (hn : next g d e = some (some d'))
    (hl : Relation.ReflTransGen (Tau kernel [] L g) u t') (hat : (code L A B D g).AtD d' t')
    (hi : Inv g d') : Step L A B D g d u e :=
  .inl (.inr ⟨d', t', hn, hl, hat, hi⟩)

/-- A concrete state of an abstract state at a site without sub-steps. -/
theorem atD_of {d : ThreadD} {t : TState} (hs : d.site.sub = 0)
    (h : At t d.site.pc (facts L A B D g d)) : (code L A B D g).AtD d t :=
  ⟨h.1, h.2.1.trans hs.symm, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

theorem at_of {d : ThreadD} {t : TState} (hs : d.site.sub = 0) (h : (code L A B D g).AtD d t) :
    At t d.site.pc (facts L A B D g d) :=
  ⟨h.1, h.2.1.trans hs, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

/-- The next instruction is the next site, live with fewer registers. -/
theorem atD_next {s s' : Site} {c : Nat} {vals : List Value} {t : TState}
    (h : (code L A B D g).AtD ⟨s, c, vals⟩ t) (hsub : s.sub = 0) (hpc : s'.pc = s.pc + 1)
    (hs' : s'.sub = 0) (hl : ∀ r ∈ liveAt s', r ∈ liveAt s) :
    (code L A B D g).AtD ⟨s', c, vals⟩ (PTX.next t) := by
  have h1 : t.pc = s.pc := h.1
  have h2 : t.sub = s.sub := h.2.1
  exact ⟨show t.pc + 1 = s'.pc by rw [h1, hpc], show t.sub = s'.sub by rw [h2, hsub, hs'],
    h.2.2.1, h.2.2.2.1, Flow.holds_factsFrom_mono (val := valueOf L A B D g ⟨s, c, vals⟩)
      h.2.2.2.2 hl⟩

/-- An abstract state's invariant, for its successor, from the invariant's fields. -/
macro "inv_tac " hi:term : tactic => `(tactic| (
  obtain ⟨h0, hnz, hw, hcol, hst, hv⟩ := $hi
  constructor <;> simp_all [Site.zero]))

/-- Evaluate a segment of the thread from `h` and close the facts of its end state. -/
syntax "tc_seg" term:max term:max (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| tc_seg $h $hpre $[[$extra,*]]?) => do
    let extra := (extra.map (·.getElems)).getD #[]
    `(tactic| (
      have hbase := ($hpre).sharedRange
      seg_fp $h using
        try tc_values
        all_goals seg_close [$extra,*]))

section
variable (hpre : Pre L A B D a b mem0) (hg : g < L.threads) {c : Nat} {vals : List Value}
  {t u : TState} {e : Event} {ins : Instr}
include hpre hg

/-- Warp 0's allocation: lane 0 stays for the address store, the other lanes go to the first
barrier. -/
theorem step_alloc (h : (code L A B D g).AtD ⟨.alloc, c, vals⟩ t) (hi : Inv g ⟨.alloc, c, vals⟩)
    (hc : kernel.code[Site.alloc.pc]? = some ins)
    (hf : Fires Site.alloc.pc (eventTmpl [] L g t ins.op) e (some u)) :
    Step L A B D g ⟨.alloc, c, vals⟩ u e := by
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tmemAlloc_0)
  have hw := hi.warp (.inl rfl)
  rw [tmpl_alloc hpre hg hw (tc_reg h.2.2.2.2) h.2.1] at hf
  obtain ⟨rfl, hu⟩ := hf
  cases hu
  by_cases hg0 : g = 0
  · subst hg0
    simp only [↓reduceIte]
    exact step_to (d' := ⟨.allocSt, c, vals⟩) (by simp [next]) .refl
      ⟨h.1, rfl, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩ (by inv_tac hi)
  · simp only [hg0, ↓reduceIte]
    have h9 : At (PTX.next t) 9 (facts L A B D g ⟨.alloc, c, vals⟩) := At.next (at_of rfl h)
    have h2 : (PTX.next t).regs 2 = some (.pred true) := by
      show t.regs 2 = _
      rw [reg_at (d := ⟨.alloc, c, vals⟩) h.2.2.2.2 (by table_decide)]
      simp only [valueOf, values, PTX.Flow.lookupLit, Option.getD_some, hg0, ne_eq,
        not_false_eq_true, decide_true]
    obtain ⟨v, hv, hatv⟩ := run_bra (K := kernel) (A := []) (L := L) (g := g) Flow.code_9 _ h9 h2
      (fun _ h => by cases h)
    simp only [↓reduceIte] at hatv
    exact step_to (d' := ⟨.bar0 false, c, vals⟩) (by simp [next, hg0]) (run_rtg hv)
      (atD_of rfl (At.mono hatv (Flow.holds_factsFrom_mono hatv.2.2.2.2 (by table_decide))))
      (by inv_tac hi)

/-- Lane 0's address store: thread 0 then loads its parameters and the shared addresses. -/
theorem step_allocSt (h : (code L A B D g).AtD ⟨.allocSt, c, vals⟩ t)
    (hi : Inv g ⟨.allocSt, c, vals⟩) (hc : kernel.code[Site.allocSt.pc]? = some ins)
    (hf : Fires Site.allocSt.pc (eventTmpl [] L g t ins.op) e (some u)) :
    Step L A B D g ⟨.allocSt, c, vals⟩ u e := by
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tmemAlloc_0)
  obtain rfl := hi.zero rfl
  rw [tmpl_allocSt hpre hg (tc_reg h.2.2.2.2) h.2.1] at hf
  obtain ⟨col, -, rfl, hu⟩ := hf
  cases hu
  have h9 : At { t with pc := t.pc + 1, sub := 0 } 9 (facts L A B D 0 ⟨.allocSt, c, vals⟩) :=
    ⟨show t.pc + 1 = 9 by rw [h.1]; rfl, rfl, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩
  have h2 : ({ t with pc := t.pc + 1, sub := 0 } : TState).regs 2 = some (.pred false) := by
    show t.regs 2 = _
    rw [reg_at (d := ⟨.allocSt, c, vals⟩) h.2.2.2.2 (by table_decide)]; tc_values; rfl
  obtain ⟨v, hv, hatv⟩ := run_bra (K := kernel) (A := []) (L := L) (g := 0) Flow.code_9 _ h9 h2
      (fun _ h => by cases h)
  simp only [Bool.false_eq_true, ↓reduceIte] at hatv
  obtain ⟨t', hr, ht'⟩ : ∃ t', run kernel [] (explicitParams L (ps A B D)) 0 6 v = some t' ∧
      At t' Site.init0.pc (facts L A B D 0 ⟨.init0, c, vals⟩) := by
    have hrA := hpre.rangeA
    have hrB := hpre.rangeB
    tc_seg hatv hpre [explicitParams]
  rw [params hpre] at hr
  exact step_to (d' := ⟨.init0, c, vals⟩) (by simp [next]) (run_rtg (run_comp hv hr))
    (atD_of rfl ht') (by inv_tac hi)

omit hpre hg in
/-- An event continuing at the next instruction, which is the next site. -/
theorem step_next {s s' : Site} (h : (code L A B D g).AtD ⟨s, c, vals⟩ t) (hi : Inv g ⟨s', c, vals⟩)
    (hsub : s.sub = 0) (hpc : s'.pc = s.pc + 1) (hs' : s'.sub = 0)
    (hl : ∀ r ∈ liveAt s', r ∈ liveAt s) (hn : next g ⟨s, c, vals⟩ e = some (some ⟨s', c, vals⟩)) :
    Step L A B D g ⟨s, c, vals⟩ (PTX.next t) e :=
  step_to hn .refl (atD_next h hsub hpc hs' hl) hi

theorem step_init0 (h : (code L A B D g).AtD ⟨.init0, c, vals⟩ t) (hi : Inv g ⟨.init0, c, vals⟩)
    (hc : kernel.code[Site.init0.pc]? = some ins)
    (hf : Fires Site.init0.pc (eventTmpl [] L g t ins.op) e (some u)) :
    Step L A B D g ⟨.init0, c, vals⟩ u e := by
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarInit_0)
  rw [tmpl_init0 hpre hg (tc_reg h.2.2.2.2)] at hf
  obtain ⟨rfl, hu⟩ := hf
  cases hu
  exact step_next h (by inv_tac hi) rfl rfl rfl (by table_decide) rfl

theorem step_init1 (h : (code L A B D g).AtD ⟨.init1, c, vals⟩ t) (hi : Inv g ⟨.init1, c, vals⟩)
    (hc : kernel.code[Site.init1.pc]? = some ins)
    (hf : Fires Site.init1.pc (eventTmpl [] L g t ins.op) e (some u)) :
    Step L A B D g ⟨.init1, c, vals⟩ u e := by
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarInit_1)
  rw [tmpl_init1 hpre hg (tc_reg h.2.2.2.2)] at hf
  obtain ⟨rfl, hu⟩ := hf
  cases hu
  exact step_next h (by inv_tac hi) rfl rfl rfl (by table_decide) rfl

omit hpre hg in
theorem step_fence (h : (code L A B D g).AtD ⟨.fence, c, vals⟩ t) (hi : Inv g ⟨.fence, c, vals⟩)
    (hc : kernel.code[Site.fence.pc]? = some ins)
    (hf : Fires Site.fence.pc (eventTmpl [] L g t ins.op) e (some u)) :
    Step L A B D g ⟨.fence, c, vals⟩ u e := by
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_fenceProxy_0)
  rw [tmpl_fenceProxy] at hf
  obtain ⟨rfl, hu⟩ := hf
  cases hu
  exact step_next h (by inv_tac hi) rfl rfl rfl (by table_decide) rfl

theorem step_arrive (h : (code L A B D g).AtD ⟨.arrive, c, vals⟩ t) (hi : Inv g ⟨.arrive, c, vals⟩)
    (hc : kernel.code[Site.arrive.pc]? = some ins)
    (hf : Fires Site.arrive.pc (eventTmpl [] L g t ins.op) e (some u)) :
    Step L A B D g ⟨.arrive, c, vals⟩ u e := by
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarArrive_0)
  rw [tmpl_arrive hpre hg (tc_reg h.2.2.2.2)] at hf
  obtain ⟨rfl, hu⟩ := hf
  cases hu
  exact step_next h (by inv_tac hi) rfl rfl rfl (by table_decide) rfl

theorem step_bulkA (h : (code L A B D g).AtD ⟨.bulkA, c, vals⟩ t) (hi : Inv g ⟨.bulkA, c, vals⟩)
    (hc : kernel.code[Site.bulkA.pc]? = some ins)
    (hf : Fires Site.bulkA.pc (eventTmpl [] L g t ins.op) e (some u)) :
    Step L A B D g ⟨.bulkA, c, vals⟩ u e := by
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_bulkCopy_0)
  rw [tmpl_bulkA hpre hg (tc_reg h.2.2.2.2) (tc_reg h.2.2.2.2) (tc_reg h.2.2.2.2)] at hf
  obtain ⟨rfl, hu⟩ := hf
  cases hu
  exact step_next h (by inv_tac hi) rfl rfl rfl (by table_decide) rfl

theorem step_bulkB (h : (code L A B D g).AtD ⟨.bulkB, c, vals⟩ t) (hi : Inv g ⟨.bulkB, c, vals⟩)
    (hc : kernel.code[Site.bulkB.pc]? = some ins)
    (hf : Fires Site.bulkB.pc (eventTmpl [] L g t ins.op) e (some u)) :
    Step L A B D g ⟨.bulkB, c, vals⟩ u e := by
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_bulkCopy_1)
  rw [tmpl_bulkB hpre hg (tc_reg h.2.2.2.2) (tc_reg h.2.2.2.2) (tc_reg h.2.2.2.2)] at hf
  obtain ⟨rfl, hu⟩ := hf
  cases hu
  exact step_next h (by inv_tac hi) rfl rfl rfl (by table_decide) rfl

omit hpre hg in
theorem step_bar0 {z : Bool} (h : (code L A B D g).AtD ⟨.bar0 z, c, vals⟩ t)
    (hi : Inv g ⟨.bar0 z, c, vals⟩) (hc : kernel.code[(Site.bar0 z).pc]? = some ins)
    (hf : Fires (Site.bar0 z).pc (eventTmpl [] L g t ins.op) e (some u)) :
    Step L A B D g ⟨.bar0 z, c, vals⟩ u e := by
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_bar_0)
  rw [tmpl_bar] at hf
  obtain ⟨rfl, hu⟩ := hf
  cases hu
  cases z
  · exact step_next h (by inv_tac hi) rfl rfl rfl (by table_decide) rfl
  · exact step_next h (by inv_tac hi) rfl rfl rfl (by table_decide) rfl

end

/-! ### The read of the address -/

theorem mask16_lt (x : BitVec 64) : (mask16 x).toNat < 2 ^ 16 := by
  have h : (truncBits 32 (BitVec.ofInt 64 65535)).toNat = 65535 := by decide
  rw [mask16, BitVec.toNat_and, h]
  exact lt_of_le_of_lt Nat.and_le_right (by norm_num)

theorem readBits_wordOf {t : TState} {r w : Nat} {v : Value} {x : BitVec 64}
    (h : t.regs r = some v) (hx : wordOf v = some x) :
    readBits L g t w (.reg r) = .ok (truncBits w x) := by
  cases v <;> simp only [wordOf, Option.map_eq_some_iff, Option.some.injEq, reduceCtorEq] at hx <;>
    first
    | (subst hx; simp [readBits, readReg, h, bind, Except.bind, pure, Except.pure])
    | (obtain ⟨n, hn, -⟩ := hx
       simp [Value.bitPattern] at hn; done)
    | (obtain ⟨n, hn, rfl⟩ := hx
       simp [readBits, readReg, h, hn, bind, Except.bind, pure, Except.pure])

/-- The `and.b32` after the read keeps the low 16 bits of a word. -/
theorem out_mask {t : TState} {v : Value} {x : BitVec 64} (hpc : t.pc = Flow.load_0 + 1)
    (hf : t.fault = none) (h14 : t.regs 14 = some v) (hx : wordOf v = some x) :
    out kernel [] L g t = .tau (PTX.next (setReg t 14 (.bits 32 (mask16 x)))) := by
  refine out_tau hf (by rw [hpc]; exact Flow.code_24) rfl rfl ?_
  rw [execLocalA_nil]
  refine (execLocal_int (by rfl)).trans ?_
  simp only [execInt, DType.width]
  rw [readBits_wordOf h14 hx]
  simp [mask16, readBits, bind, Except.bind, pure, Except.pure]

/-- The `and.b32` after the read of bytes that are no word is undefined behaviour. -/
theorem out_mask_ub {t : TState} {v : Value} (hpc : t.pc = Flow.load_0 + 1) (hf : t.fault = none)
    (h14 : t.regs 14 = some v) (hx : wordOf v = none) :
    ∃ f, out kernel [] L g t = .ev (.ub f) := by
  have he : ∃ f, execLocalA [] L g t (.int ⟨.and, .int .b 32, false, [some 14],
      [.reg 14, .imm 65535]⟩) = .error f := by
    rw [execLocalA_nil, execLocal_int (L := L) (g := g) (t := t)
      (i := ⟨.and, .int .b 32, false, [some 14], [.reg 14, .imm 65535]⟩) (by rfl)]
    cases v <;> simp only [wordOf, Option.map_eq_none_iff, reduceCtorEq] at hx <;>
      simp [execInt, DType.width, readBits, readReg, h14, hx, bind, Except.bind, pure, Except.pure,
        throw, throwThe, MonadExceptOf.throw]
  obtain ⟨f, he⟩ := he
  exact ⟨f, out_ub hf (by rw [hpc]; exact Flow.code_24) rfl rfl he⟩

section
variable (hpre : Pre L A B D a b mem0) (hg : g < L.threads) {c : Nat} {vals : List Value}
  {t u : TState} {e : Event} {ins : Instr}
include hpre hg

/-- The read of the address: the column on to `bar0`'s poll on thread 0 and to `bar1`'s
elsewhere; bytes that are no word stop the machine. -/
theorem step_load {z : Bool} (h : (code L A B D g).AtD ⟨.load z, c, vals⟩ t)
    (hi : Inv g ⟨.load z, c, vals⟩) (hc : kernel.code[(Site.load z).pc]? = some ins)
    (hf : Fires (Site.load z).pc (eventTmpl [] L g t ins.op) e (some u)) :
    Step L A B D g ⟨.load z, c, vals⟩ u e := by
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_load_0)
  have hbase := hpre.sharedRange
  have h11 : t.regs 11 = some (b32 (L.sharedBase + 4368)) := by
    rw [reg_at h.2.2.2.2 (show 11 ∈ liveAt (.load z) by cases z <;> table_decide)]; tc_values
  rw [tmpl_load hpre hg h11 h.2.1] at hf
  obtain ⟨bs, -, rfl, hu⟩ := hf
  cases hu
  cases hv : rebuild 3 bs with
  | error f =>
    exact .inr ⟨by simp [code, next, rdCol, hv],
      Machine.dead_of_fault (f := f) (by simp [afterLoad, hv])⟩
  | ok v =>
    rw [afterLoad_ok h.2.1 h.2.2.1 hv]
    have h24 : At { setReg t 14 v with pc := t.pc + 1, sub := 0, acc := [] } (Flow.load_0 + 1)
        ((14, v) :: facts L A B D g ⟨.load z, c, vals⟩) :=
      ⟨show t.pc + 1 = Flow.load_0 + 1 by rw [h.1]; rfl, rfl, rfl, h.2.2.2.1, by simp [setReg],
        holds_update h.2.2.2.2 (not_mem_factsFrom
          (show 14 ∉ liveAt (.load z) by cases z <;> decide +kernel))⟩
    cases hx : wordOf v with
    | none =>
      obtain ⟨f, hf⟩ := out_mask_ub (L := L) (g := g) h24.1 h24.2.2.2.1 h24.2.2.2.2.1 hx
      exact .inr ⟨by simp [code, next, rdCol, hv, hx], Machine.dead_of_ub hf⟩
    | some x =>
      have hout := out_mask (L := L) (g := g) h24.1 h24.2.2.2.1 h24.2.2.2.2.1 hx
      have hcol : rdCol bs = some (mask16 x).toNat := by simp [rdCol, hv, hx]
      have h25 : At (PTX.next (setReg { setReg t 14 v with pc := t.pc + 1, sub := 0, acc := [] } 14
          (.bits 32 (mask16 x)))) (Flow.load_0 + 2)
          ((14, b32 (mask16 x).toNat) :: facts L A B D g ⟨.load z, c, vals⟩) := by
        rw [show b32 (mask16 x).toNat = Value.bits 32 (mask16 x) by simp [b32]]
        exact At.set ⟨h24.1, h24.2.1, h24.2.2.1, h24.2.2.2.1, h24.2.2.2.2.2⟩ (not_mem_factsFrom
          (show 14 ∉ liveAt (.load z) by cases z <;> decide +kernel))
      have h2 := holds_mem h25.2.2.2.2
        (List.mem_cons_of_mem _ (Flow.mem_factsFrom (show 2 ∈ liveAt (.load z) by
          cases z <;> table_decide)))
      have hcl := mask16_lt x
      cases z
      · have hg0 := hi.nz (.inr rfl)
        have h2' : (PTX.next (setReg { setReg t 14 v with pc := t.pc + 1, sub := 0, acc := [] } 14
            (.bits 32 (mask16 x)))).regs 2 = some (.pred true) := by
          rw [h2]; simp only [valueOf, values, PTX.Flow.lookupLit, Option.getD_some, hg0, ne_eq,
            not_false_eq_true, decide_true]
        obtain ⟨u1, hu1, hat1⟩ := run_bra (K := kernel) (A := []) (L := L) (g := g) Flow.code_25 _
          h25 h2' (fun _ h => by cases h)
        simp only [↓reduceIte] at hat1
        obtain ⟨t', hr, ht'⟩ : ∃ t', run kernel [] L g 0 u1 = some t' ∧
            At t' Site.wait1.pc (facts L A B D g ⟨.wait1, (mask16 x).toNat, vals⟩) := by
          tc_seg hat1 hpre
        exact step_to (d' := ⟨.wait1, (mask16 x).toNat, vals⟩) (by simp [next, hcol])
          (.head hout (run_rtg (run_comp hu1 hr))) (atD_of rfl ht') (by inv_tac hi)
      · obtain rfl := hi.zero rfl
        have h2' : (PTX.next (setReg { setReg t 14 v with pc := t.pc + 1, sub := 0, acc := [] } 14
            (.bits 32 (mask16 x)))).regs 2 = some (.pred false) := by
          rw [h2]; tc_values; rfl
        obtain ⟨u1, hu1, hat1⟩ := run_bra (K := kernel) (A := []) (L := L) (g := 0) Flow.code_25 _
          h25 h2' (fun _ h => by cases h)
        simp only [Bool.false_eq_true, ↓reduceIte] at hat1
        obtain ⟨t', hr, ht'⟩ : ∃ t', run kernel [] L 0 0 u1 = some t' ∧
            At t' Site.wait0.pc (facts L A B D 0 ⟨.wait0, (mask16 x).toNat, vals⟩) := by
          tc_seg hat1 hpre
        exact step_to (d' := ⟨.wait0, (mask16 x).toNat, vals⟩) (by simp [next, hcol])
          (.head hout (run_rtg (run_comp hu1 hr))) (atD_of rfl ht') (by inv_tac hi)

end

end
end PTX.Kernels.TcGemm.Proof
