-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.ParamLoad
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.ParamSteps
public import Kernels.FlashMlaSparseDecodeH64.Proof.Startup.Machine
public import Kernels.FlashMlaSparseDecodeH64.Proof.Startup.Seg
public import Lemmas.Flow.SegChain
public import Lemmas.Flow.Step.Alloc
public import Lemmas.Flow.Step.SiteIte
import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.ParamName

@[expose] public section

/-! # The startup's obligations at every state that is not an exit -/

/-! # The startup's obligations: the initializations, and the first state

The 23 initializations each continue to the next one, the last to the fence (`initSucc`). The
first state is reached from the empty state by the six local instructions of the ABI prefix. -/

/-! # The startup's read-back of the allocated address, over any value

The read at pc 92 returns bytes another thread wrote, so the value they rebuild to is abstract;
the comparison `setp.eq.b32` at pc 93 reads it through Core's `readBits`, which the evaluation of a
segment does not reduce on an abstract value. This file takes the two local steps by hand: the
comparison writes `scmpi .eq .b w 0` of the word `ldWord` names (`seg_setp`), the branch at pc 94
then goes to the relinquishment or the `trap` (`st_seg`), and a value the comparison cannot read
faults at pc 93 (`dead_setp`). -/

/-! # The startup's obligations: the shuffles, the elections and the tail

Every state of the startup other than its exits and the initializations (`Steps2.lean`) satisfies
its step obligation, by `site_cases`, one successor family per declaration. The first election's
elected lane runs the descriptor prefetches (`seg_leader`). -/

/-! # The prefetch of the elected lane of warp 0, as a segment

Pcs 21 to 27: `cvta.param` of the `param_1` object's address, three descriptor-offset additions
(`+128`, `+512`, `+768`) that the kernel's parameter-pointer reading turns into numeric
addresses, and the three `prefetch.tensormap` of the published descriptors. The steps are
`run_cvtaParam`, `run_paramAdd` and `run_prefetchMap` (`Lib/Launch.lean`); here they are stated
for any facts that hold the parameter pointer, as one segment `seg_leader` that `site_cases`
composes with the evaluated segments around it. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Startup
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {g : Nat}

/-- The facts after the prefetches: the generic pointer and the three descriptor addresses. -/
def leaderFacts (P : Params) (F : List (Nat × Value)) : List (Nat × Value) :=
  (3021, .bits 64 (BitVec.ofNat 64 (P.param1Base + 768))) ::
  (3020, .bits 64 (BitVec.ofNat 64 (P.param1Base + 512))) ::
  (3019, .bits 64 (BitVec.ofNat 64 (P.param1Base + 128))) ::
  (3022, .ptr 64 true (.param (param "1")) 0) :: F

private theorem fresh_cons {F : List (Nat × Value)} {r s : Nat} {v : Value} (h1 : s ≠ r)
    (h2 : ∀ p ∈ F, p.1 ≠ r) : ∀ p ∈ (s, v) :: F, p.1 ≠ r :=
  not_mem_facts_cons h1 h2

/-- **The elected lane's prefetches** (pcs 21 to 27) from any facts holding the `param_1`
pointer in `%rd1` and none of the four registers the steps write. -/
theorem seg_leader (hp : Pre P L m) {F : List (Nat × Value)}
    (h1 : (2990, .ptr 64 false (.param (param "1")) 0) ∈ F)
    (hk : ∀ q ∈ F, q.1 ≠ 3019 ∧ q.1 ≠ 3020 ∧ q.1 ≠ 3021 ∧ q.1 ≠ 3022) :
    Seg kernel Assumptions.all L g 7 21 F 28 (leaderFacts P F) := by
  have k1 : ∀ q ∈ F, q.1 ≠ 3019 := fun q hq => by obtain ⟨h1, -, -, -⟩ := hk q hq; exact h1
  have k2 : ∀ q ∈ F, q.1 ≠ 3020 := fun q hq => by obtain ⟨-, h2, -, -⟩ := hk q hq; exact h2
  have k3 : ∀ q ∈ F, q.1 ≠ 3021 := fun q hq => by obtain ⟨-, -, h3, -⟩ := hk q hq; exact h3
  have k4 : ∀ q ∈ F, q.1 ≠ 3022 := fun q hq => by obtain ⟨-, -, -, h4⟩ := hk q hq; exact h4
  intro t h
  have hr0 : t.regs 2990 = some (.ptr 64 false (.param (param "1")) 0) := holds_mem (atHolds h) h1
  have hR := hp.param1Range
  set v1 : Value := .ptr 64 true (.param (param "1")) 0
  set t1 := PTX.next (setReg t 3022 v1) with ht1
  have e1 : run kernel Assumptions.all L g 1 t = some t1 := run_cvtaParam Flow.code_21 h hr0
  have a1 : At t1 22 ((3022, v1) :: F) := At.set h k4
  have r1 : t1.regs 3022 = some v1 := holds_mem (atHolds a1) (by simp)
  set v2 : Value := .bits 64 (BitVec.ofNat 64 (P.param1Base + 128))
  set t2 := PTX.next (setReg t1 3019 v2) with ht2
  have e2 : run kernel Assumptions.all L g 1 t1 = some t2 :=
    run_paramAdd (pc := 22) (k := 128) Flow.code_22 a1 (by decide) r1 hp.param1Object
      (by norm_num)
  have a2 : At t2 23 ((3019, v2) :: (3022, v1) :: F) :=
    At.set a1 (fresh_cons (by decide) k1)
  have r2 : t2.regs 3019 = some v2 := holds_mem (atHolds a2) (by simp)
  set t3 := PTX.next t2 with ht3
  have e3 : run kernel Assumptions.all L g 1 t2 = some t3 :=
    run_prefetchMap (pc := 23) Flow.code_23 a2 (by decide) (by decide) r2
      (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), hp.mapQBind]; rfl)
  have a3 : At t3 24 ((3019, v2) :: (3022, v1) :: F) := At.next a2
  have r3 : t3.regs 3022 = some v1 := holds_mem (atHolds a3) (by simp)
  set v4 : Value := .bits 64 (BitVec.ofNat 64 (P.param1Base + 512))
  set t4 := PTX.next (setReg t3 3020 v4) with ht4
  have e4 : run kernel Assumptions.all L g 1 t3 = some t4 :=
    run_paramAdd (pc := 24) (k := 512) Flow.code_24 a3 (by decide) r3 hp.param1Object
      (by norm_num)
  have a4 : At t4 25 ((3020, v4) :: (3019, v2) :: (3022, v1) :: F) :=
    At.set a3 (fresh_cons (by decide) (fresh_cons (by decide) k2))
  have r4 : t4.regs 3020 = some v4 := holds_mem (atHolds a4) (by simp)
  set t5 := PTX.next t4 with ht5
  have e5 : run kernel Assumptions.all L g 1 t4 = some t5 :=
    run_prefetchMap (pc := 25) Flow.code_25 a4 (by decide) (by decide) r4
      (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), hp.mapOBind]; rfl)
  have a5 : At t5 26 ((3020, v4) :: (3019, v2) :: (3022, v1) :: F) := At.next a4
  have r5 : t5.regs 3022 = some v1 := holds_mem (atHolds a5) (by simp)
  set v6 : Value := .bits 64 (BitVec.ofNat 64 (P.param1Base + 768))
  set t6 := PTX.next (setReg t5 3021 v6) with ht6
  have e6 : run kernel Assumptions.all L g 1 t5 = some t6 :=
    run_paramAdd (pc := 26) (k := 768) Flow.code_26 a5 (by decide) r5 hp.param1Object
      (by norm_num)
  have a6 : At t6 27 (leaderFacts P F) :=
    At.set a5 (fresh_cons (by decide) (fresh_cons (by decide) (fresh_cons (by decide)
      k3)))
  have r6 : t6.regs 3021 = some v6 := holds_mem (atHolds a6) List.mem_cons_self
  set t7 := PTX.next t6 with ht7
  have e7 : run kernel Assumptions.all L g 1 t6 = some t7 :=
    run_prefetchMap (pc := 27) Flow.code_27 a6 (by decide) (by decide) r6
      (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), hp.mapKVBind]; rfl)
  exact ⟨t7, run_comp (run_comp (run_comp (run_comp (run_comp (run_comp e1 e2) e3) e4) e5) e6)
    e7, At.next a6⟩

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Startup

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Startup
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32

noncomputable section
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable {P : Params} {L : Launch} {m : Mem0} {g : Nat}

/-- **The shuffles.** -/
theorem stepAt_sh (hp : Pre P L m) (d : D) (hs : ∃ j, d.site = .sh j) : (code L g).StepAt d := by
  obtain ⟨s, x1, x2⟩ := d
  site_cases s skip_by (simp at hs)
    trans [succ, word32]
    seg_by (st_seg hp) inv_by (exact fun _ => trivial) guard_by (trivial)

/-- **The second election**: the elected lane initializes, the others allocate. -/
theorem stepAt_elect1 (hp : Pre P L m) (d : D) (hs : d.site = .elect 1) :
    (code L g).StepAt d := by
  obtain ⟨s, x1, x2⟩ := d
  site_cases s skip_by (simp at hs)
    trans [succ]
    seg_by (st_seg hp) inv_by (exact fun _ => trivial) guard_by (trivial)

/-- **The first election**: the elected lane prefetches the three descriptors
(`seg_leader`). -/
theorem stepAt_elect0 (hp : Pre P L m) (d : D) (hs : d.site = .elect 0) :
    (code L g).StepAt d := by
  obtain ⟨s, x1, x2⟩ := d
  site_cases s except [.elect 0 => (by
        refine Code.step_elect (dl := ⟨.elect 1, x1, x2⟩) (ds := ⟨.elect 1, x1, x2⟩)
          (by code_lookup) (by fact_free) ?_ (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl) rfl rfl
          ?_ ?_
        · intro r hr
          cases hr
          exact ⟨by fact_free, by decide⟩
        · intro ld
          refine ⟨fun _ => ?_, rfl, rfl, fun _ => trivial⟩
          site_norm
          dsimp only [Code.electFacts]
          refine Seg.comp_ex (q := 21)
            (H := factsFrom (liveAt 21) (valueOf L g ⟨.elect 1, x1, x2⟩))
            (by seg_auto using (st_seg hp)) ?_
          refine Seg.comp_ex (q := 28)
            (H := leaderFacts P (factsFrom (liveAt 21) (valueOf L g ⟨.elect 1, x1, x2⟩)))
            ⟨7, seg_leader hp (Flow.mem_factsFrom (by lit_mem))
              (fun q hq => ⟨Flow.not_mem_factsFrom (by lit_not_mem) q hq,
                Flow.not_mem_factsFrom (by lit_not_mem) q hq,
                Flow.not_mem_factsFrom (by lit_not_mem) q hq,
                Flow.not_mem_factsFrom (by lit_not_mem) q hq⟩)⟩ ?_
          dsimp only [leaderFacts]
          seg_auto using (st_seg hp)
        · intro ld
          lands_auto (st_seg hp) (exact fun _ => trivial))]
    skip_by (simp at hs)
    trans [succ]
    seg_by (st_seg hp) inv_by (exact fun _ => trivial) guard_by (trivial)

/-- **The `trap`**: undefined behaviour, the thread's last event, so no successor state. -/
theorem stepAt_trap (x1 x2 : BitVec 64) : (code L g).StepAt ⟨.trap, x1, x2⟩ where
  site := fun _ => ⟨⟨none, .trap⟩, by code_lookup, rfl, trivial⟩
  step := by
    intro t e u ins _ _ hc hf
    have hc' : kernel.code[95]? = some ins := hc
    rw [show kernel.code[95]? = some ⟨none, .trap⟩ by code_lookup] at hc'
    obtain rfl := Option.some.inj hc'
    exact absurd hf.2 (by simp)

/-- **The tail of warp 0**: the fence and the relinquishment (the read-back is
`StepsLd.lean`'s). -/
theorem stepAt_tail (hp : Pre P L m) (d : D) (hs : d.site = .fence ∨ d.site = .relinq) :
    (code L g).StepAt d := by
  obtain ⟨s, x1, x2⟩ := d
  site_cases s skip_by (simp at hs)
    trans [succ]
    seg_by (st_seg hp) inv_by (exact fun _ => trivial) guard_by (trivial)

/-- **The allocation's two steps**: the request, and lane 0's store of the address. -/
theorem stepAt_alloc (hp : Pre P L m) (d : D) (hs : d.site = .alloc ∨ d.site = .allocSt) :
    (code L g).StepAt d := by
  obtain ⟨s, x1, x2⟩ := d
  site_cases s except [.alloc => (by
        refine Code.step_alloc (dw := ⟨.allocSt, x1, x2⟩) (dn := ⟨.ld, x1, x2⟩)
          (by code_lookup) rfl rfl (fun h e => by simp [succ, h]) (fun h e => by simp [succ, h])
          rfl rfl rfl rfl (fun _ => trivial)
          (by lands_auto (st_seg hp) (exact fun _ => trivial))),
      .allocSt => (by
        refine Code.step_allocWr (dn := ⟨.ld, x1, x2⟩) (by code_lookup) rfl rfl
          (fun e => rfl) (by lands_auto (st_seg hp) (exact fun _ => trivial)))]
    skip_by (simp at hs)
    trans [succ]
    seg_by (st_seg hp) inv_by (exact fun _ => trivial) guard_by (trivial)

/-- **The CTA barrier**: the dispatch on the warpgroup word. -/
theorem stepAt_bar (hp : Pre P L m) (d : D) (hs : d.site = .bar) : (code L g).StepAt d := by
  obtain ⟨s, x1, x2⟩ := d
  site_cases s skip_by (simp at hs)
    trans [succ, enterOf]
    seg_by (st_seg hp) inv_by (exact fun _ => trivial) guard_by (trivial)

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Startup

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Startup
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32

noncomputable section
set_option linter.unusedTactic false

variable {P : Params} {L : Launch} {m : Mem0} {g : Nat}

/-- Core's integer read of a register holding `v` is the word `ldWord v` names. -/
theorem readBits_ldWord {w r : Nat} {t : TState} {v : Value} {x : BitVec 64}
    (hr : t.regs r = some v) (hw : ldWord v = some x) :
    readBits L g t w (.reg r) = .ok (truncBits w x) := by
  cases v <;> simp only [ldWord, Option.map_eq_some_iff, Option.some.injEq, reduceCtorEq] at hw <;>
    first
    | (obtain ⟨a, ha, rfl⟩ := hw
       simp [readBits, readReg, hr, ha, bind, Except.bind, pure, Except.pure])
    | (subst hw; simp [readBits, readReg, hr, bind, Except.bind, pure, Except.pure])

/-- Core's integer read of a register holding a value without a word faults. -/
theorem readBits_ldWord_none {w r : Nat} {t : TState} {v : Value}
    (hr : t.regs r = some v) (hw : ldWord v = none) :
    ∃ f, readBits L g t w (.reg r) = .error f := by
  cases v <;> simp_all [readBits, readReg, ldWord, bind, Except.bind, pure, Except.pure] <;>
    exact ⟨_, rfl⟩

/-- The comparison at pc 93. -/
abbrev setp93 : Op := .int ⟨.setp .eq none, .int .b 32, false, [some 7], [.reg 557, .imm 0]⟩

theorem noRule93 : NoRuleAt Assumptions.all L g 93 setp93 :=
  fun t ht a ha => asms_localRule_int (t := t) (by rw [ht]; decide) (by rw [ht]; decide)
    (by rw [ht]; decide) (by simp [Assumptions.peerPackRule]) a ha

/-- **The comparison** of a value with a word: one step that writes the predicate. -/
theorem seg_setp {F : List (Nat × Value)} {v : Value} {x : BitVec 64}
    (hv : (557, v) ∈ F) (hw : ldWord v = some x)
    (hk : freshKeys [(7, .pred (scmpi .eq .b x 0))] F = true) :
    ∃ n, Seg kernel Assumptions.all L g n 93 F 94
      ([(7, .pred (scmpi .eq .b x 0))].reverse ++ F) :=
  Seg.writes Flow.code_93 rfl (fun R cf hR => by
    rw [execLocalA_core noRule93 noSegments.segFreePc rfl, execLocal_int rfl]
    have hb := readBits_ldWord (L := L) (g := g) (w := 32) (t := ⟨93, R, cf, 0, [], none⟩)
      (holds_mem hR hv) hw
    simp [execInt, DType.width, hb, bind, Except.bind, pure, Except.pure, setRegsL]
    rfl) hk

/-- **The comparison's fault** on a value without a word. -/
theorem dead_setp {F : List (Nat × Value)} {v : Value}
    (hv : (557, v) ∈ F) (hw : ldWord v = none) : DeadFrom kernel Assumptions.all L g 93 F :=
  DeadFrom.local_error Flow.code_93 rfl (fun R cf hR => by
    obtain ⟨f, hf⟩ := readBits_ldWord_none (L := L) (g := g) (w := 32)
      (t := ⟨93, R, cf, 0, [], none⟩) (holds_mem hR hv) hw
    refine ⟨f, ?_⟩
    rw [execLocalA_core noRule93 noSegments.segFreePc rfl, execLocal_int rfl]
    simp [execInt, DType.width, hf, bind, Except.bind])

/-- The facts after the read-back: the value read and the read's other facts. -/
abbrev ldFacts (L : Launch) (g : Nat) (x1 x2 : BitVec 64) (v : Value) : List (Nat × Value) :=
  (557, v) :: Code.dropReg 557 ((code L g).facts ⟨.ld, x1, x2⟩)

/-- **The branch** after a comparison that wrote `c`: the relinquishment or the `trap`. -/
theorem lands_ld (hp : Pre P L m) {x1 x2 w : BitVec 64} {v : Value} (hw : ldWord v = some w)
    (c : Bool) (hc : scmpi .eq .b w 0 = c) :
    (code L g).Lands ⟨.ld, x1, x2⟩ 93 (ldFacts L g x1 x2 v)
      ⟨if c then .relinq else .trap, x1, x2⟩ := by
  refine ⟨fun _ => ?_, by cases c <;> rfl, by cases c <;> rfl, fun _ => trivial⟩
  refine Seg.comp_ex (seg_setp List.mem_cons_self hw ?_) ?_
  · simp only [ldFacts, freshKeys, facts]
    simp only [Code.dropReg_factsFrom]
    simp only [factsFrom, List.map_cons, List.map_map, Function.comp_def, List.map_id']
    decide
  refine Seg.pred_ex (c' := c) List.mem_cons_self hc ?_
  simp only [ldFacts, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
  cases c
  all_goals
    site_norm
    try drop_norm
    seg_auto using (st_seg hp)

/-- **The read-back**: every value it returns is followed to the relinquishment or the `trap`,
or kills the thread at the comparison. -/
theorem stepAt_ld (hp : Pre P L m) (x1 x2 : BitVec 64) : (code L g).StepAt ⟨.ld, x1, x2⟩ :=
  Code.StepAt.of (fun _ => ⟨_, Flow.code_92, rfl, trivial⟩)
    (Code.step_load_dead (nv := afterLd ⟨.ld, x1, x2⟩) Flow.code_92 rfl rfl rfl rfl
      (fun _ bs v hv => by simp [succ, hv])
      (fun _ bs f hv => .inl (by simp [succ, hv])) rfl rfl
      (fun v d' hv => by
        unfold afterLd at hv
        cases hw : ldWord v with
        | none => simp [hw] at hv
        | some w =>
          simp only [hw] at hv
          split at hv <;> rename_i hc <;> obtain rfl := Option.some.inj (Option.some.inj hv)
          · exact lands_ld hp hw true hc
          · exact lands_ld hp hw false (Bool.eq_false_iff.mpr hc))
      (fun v hv _ u hu => by
        unfold afterLd at hv
        cases hw : ldWord v with
        | none => exact dead_setp List.mem_cons_self hw u hu
        | some w => simp only [hw] at hv; split at hv <;> cases hv))

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Startup

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Startup
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32

noncomputable section
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable {P : Params} {L : Launch} {m : Mem0} {g : Nat}

/-- **The initializations.** -/
theorem stepAt_init (hp : Pre P L m) (d : D) (hs : ∃ n, d.site = .init n) :
    (code L g).StepAt d := by
  obtain ⟨s, x1, x2⟩ := d
  site_cases s skip_by (simp at hs)
    trans [succ, initSucc]
    seg_by (st_seg hp) inv_by (exact fun _ => trivial) guard_by (trivial)

/-- **The startup's first state**: from the empty state, the six local instructions of the ABI
prefix (the two parameter objects' addresses, `%ctaid.x`, `%ctaid.y`, `%tid.x` and the warpgroup
index) reach the first shuffle with the table's facts. -/
theorem start (hp : Pre P L m) :
    ∃ t, Relation.ReflTransGen (Tau kernel Assumptions.all L g) {} t ∧
      (code L g).AtD (code L g).init t ∧ (code L g).inv (code L g).init := by
  obtain ⟨n, h⟩ : ∃ n, Seg kernel Assumptions.all L g n 0 [] ((code L g).pc (code L g).init)
      ((code L g).facts (code L g).init) := by
    site_norm
    refine ⟨6, fun t h => ?_⟩
    have hbase := sharedBase_lt hp
    seg_fp h using
      try simp only [valueOf, values, entryVal, entryVals, r2W, PTX.Flow.lookupLit,
        Option.getD_some, Option.getD_none]
      all_goals (try launch_norm hp)
      all_goals first
        | (rw [param0_lit])
        | (rw [param1_lit])
        | rfl
        | (simp only [w32]; rw [truncBits_ofNat_mod]; done)
        | (simp only [w32, tw, tidOf_eq hp]
           rw [truncBits_ofNat_mod, Nat.mod_eq_of_lt (by omega : g % 384 < 2 ^ 32)]
           done)
        | (rw [truncBits_ofNat (n := g % 384) (by omega) (by omega)]
           exact congrArg _ (shr7_word _ (by omega)))
  obtain ⟨t, hr, ht⟩ := h {} ⟨rfl, rfl, rfl, rfl, trivial⟩
  exact ⟨t, run_rtg hr, ht, trivial⟩

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Startup

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Startup
open PTX PTX.Proof PTX.Flow

variable {P : Params} {L : Launch} {m : Mem0} {g : Nat}

/-- **Every state of the startup that is not an exit obeys its step obligation.** -/
theorem stepAt_all (hp : Pre P L m) (d : D) (hx : exitOf d = none) : (code L g).StepAt d := by
  obtain ⟨s, x1, x2⟩ := d
  cases s with
  | sh j => exact stepAt_sh hp _ ⟨j, rfl⟩
  | elect j =>
    match j with
    | 0 => exact stepAt_elect0 hp _ rfl
    | 1 => exact stepAt_elect1 hp _ rfl
  | init n => exact stepAt_init hp _ ⟨n, rfl⟩
  | fence => exact stepAt_tail hp _ (.inl rfl)
  | alloc => exact stepAt_alloc hp _ (.inl rfl)
  | allocSt => exact stepAt_alloc hp _ (.inr rfl)
  | ld => exact stepAt_ld hp x1 x2
  | trap => exact stepAt_trap x1 x2
  | relinq => exact stepAt_tail hp _ (.inr rfl)
  | bar => exact stepAt_bar hp _ rfl
  | enter r => simp [exitOf] at hx

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Startup
