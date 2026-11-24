-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Thread.Consumer
public import Kernels.Fp16Gemm8192.Proof.Thread.Cluster
public import Lemmas.Flow.Local
public import Lemmas.Flow.Async
public import Mathlib.Tactic.FinCases

@[expose] public section

/-! Definitions and helper facts of `ConsumerEpilogue`. -/

namespace PTX.Kernels.Fp16Gemm8192.Proof.Consumer
open PTX PTX.Proof PTX.Flow
noncomputable section
set_option maxRecDepth 100000

/-- The continuation of a step of this role: the thread leaves the role, or steps to `d'` at
`t'` by a run of `Tau` (the conclusion of each step lemma). -/
syntax "epi_cont " term:max term:max term:max term:max term:max : term
macro_rules
  | `(epi_cont $L $g $d $e $u) => `(next $L $g $d $e = some none ∨ ∃ d' t', next $L $g $d $e =
    some (some d') ∧
      Relation.ReflTransGen (Tau kernel [Assumptions.idealArith,
        Assumptions.clusterMbar, Assumptions.pollAgree] $L $g) $u t' ∧
      At t' d'.site.pc (facts $L $g d') ∧ Inv d')


/-- The predicate that slice `k`'s second barrier branches on (set before the commit). -/
def epi_barPred : Fin 8 → Nat
  | 0 => 11 | 1 => 12 | 2 => 13 | 3 => 14
  | 4 => 15 | 5 => 16 | 6 => 17 | 7 => 18

theorem epi_flip_bits : ∀ cp < 2,
    truncBits 32 (BitVec.ofNat 64 cp) ^^^ truncBits 32 (BitVec.ofInt 64 1) =
      BitVec.ofNat 64 (1 - cp) := by
  table_decide

/-- A `setp.ne` of a value below 32 against zero. -/
theorem epi_setp_bounded : ∀ x < 32,
    PTX.compare Cmp.ne IType.b 32 (truncBits 32 (BitVec.ofNat 64 x))
      (truncBits 32 (BitVec.ofInt 64 0)) = decide (x ≠ 0) := by
  table_decide

/-- A `setp.ne` of a 32-bit value against the all-ones word. -/
theorem epi_setp_none (x : Nat) (hx : x < 2 ^ 32) :
    PTX.compare Cmp.ne IType.b 32 (truncBits 32 (BitVec.ofNat 64 x))
      (truncBits 32 (BitVec.ofInt 64 (-1))) = decide (x ≠ Loader.none32) := by
  have h1 : (truncBits 32 (BitVec.ofNat 64 x)).toNat = x := by
    simp only [truncBits, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show x < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt hx]
  have h2 : (truncBits 32 (BitVec.ofInt 64 (-1))).toNat = 4294967295 := by decide
  unfold PTX.compare
  simp only [h1, h2, Loader.none32, decide_eq_decide]
  constructor <;> intro hh <;> omega

theorem epi_lead_lt (L : Launch) (g : Nat) : tidOf L g / 32 % 4 ||| tidOf L g % 32 < 32 := by
  have h : tidOf L g / 32 % 4 ||| tidOf L g % 32 < 2 ^ 5 := Nat.or_lt_two_pow (by omega) (by omega)
  simpa using h

def epi_fenceLocals (k : Fin 8) : Nat := if k.val = 0 then 8 else 9

theorem epi_pc_barB_fence (k : Fin 8) : (Site.barB k).pc + 1 + 1 = (Site.fence k).pc := by
  fin_cases k <;> rfl

theorem epi_pc_drain_barA (k : Fin 8) : (Site.drain k).pc + 1 = (Site.barA k).pc := by
  fin_cases k <;> rfl

theorem epi_pc_barA_store (k : Fin 8) : (Site.barA k).pc + 1 = (Site.store k 0 0).pc := by
  fin_cases k <;> rfl

theorem epi_pc_commit_drain (k : Fin 8) (hk : k.val + 1 < 8) :
    (Site.commit k).pc + 1 = (Site.drain ⟨k.val + 1, hk⟩).pc := by
  fin_cases k <;> first | rfl | simp at hk

theorem epi_drain_code (k : Fin 8) :
    ∃ ins, kernel.code[(Site.drain k).pc]? = some ins ∧ AsyncAdvancesOp ins.op := by
  fin_cases k
  exacts [⟨_, Flow.code_bulkWait_0, by exact trivial⟩, ⟨_, Flow.code_bulkWait_1, by exact trivial⟩,
    ⟨_, Flow.code_bulkWait_2, by exact trivial⟩, ⟨_, Flow.code_bulkWait_3, by exact trivial⟩,
    ⟨_, Flow.code_bulkWait_4, by exact trivial⟩, ⟨_, Flow.code_bulkWait_5, by exact trivial⟩,
    ⟨_, Flow.code_bulkWait_6, by exact trivial⟩, ⟨_, Flow.code_bulkWait_7, by exact trivial⟩]

theorem epi_barA_code (k : Fin 8) :
    ∃ ins, kernel.code[(Site.barA k).pc]? = some ins ∧ AsyncAdvancesOp ins.op := by
  fin_cases k
  exacts [⟨_, Flow.code_bar_1, by exact trivial⟩, ⟨_, Flow.code_bar_3, by exact trivial⟩,
    ⟨_, Flow.code_bar_5, by exact trivial⟩, ⟨_, Flow.code_bar_7, by exact trivial⟩,
    ⟨_, Flow.code_bar_9, by exact trivial⟩, ⟨_, Flow.code_bar_11, by exact trivial⟩,
    ⟨_, Flow.code_bar_13, by exact trivial⟩, ⟨_, Flow.code_bar_15, by exact trivial⟩]

theorem epi_barB_code (k : Fin 8) :
    ∃ ins, kernel.code[(Site.barB k).pc]? = some ins ∧ AsyncAdvancesOp ins.op := by
  fin_cases k
  exacts [⟨_, Flow.code_bar_2, by exact trivial⟩, ⟨_, Flow.code_bar_4, by exact trivial⟩,
    ⟨_, Flow.code_bar_6, by exact trivial⟩, ⟨_, Flow.code_bar_8, by exact trivial⟩,
    ⟨_, Flow.code_bar_10, by exact trivial⟩, ⟨_, Flow.code_bar_12, by exact trivial⟩,
    ⟨_, Flow.code_bar_14, by exact trivial⟩, ⟨_, Flow.code_bar_16, by exact trivial⟩]

theorem epi_commit_code (k : Fin 8) :
    ∃ ins, kernel.code[(Site.commit k).pc]? = some ins ∧ AsyncAdvancesOp ins.op := by
  fin_cases k
  exacts [⟨_, Flow.code_bulkCommit_0, by exact trivial⟩,
    ⟨_, Flow.code_bulkCommit_1, by exact trivial⟩,
    ⟨_, Flow.code_bulkCommit_2, by exact trivial⟩, ⟨_, Flow.code_bulkCommit_3, by exact trivial⟩,
    ⟨_, Flow.code_bulkCommit_4, by exact trivial⟩, ⟨_, Flow.code_bulkCommit_5, by exact trivial⟩,
    ⟨_, Flow.code_bulkCommit_6, by exact trivial⟩, ⟨_, Flow.code_bulkCommit_7, by exact trivial⟩]

theorem epi_tma_code (k : Fin 8) :
    ∃ ins, kernel.code[(Site.tma k).pc]? = some ins ∧ AsyncAdvancesOp ins.op := by
  fin_cases k
  exacts [⟨_, Flow.code_tensorCopy_24, by exact trivial⟩,
    ⟨_, Flow.code_tensorCopy_25, by exact trivial⟩,
    ⟨_, Flow.code_tensorCopy_26, by exact trivial⟩, ⟨_, Flow.code_tensorCopy_27, by exact trivial⟩,
    ⟨_, Flow.code_tensorCopy_28, by exact trivial⟩, ⟨_, Flow.code_tensorCopy_29, by exact trivial⟩,
    ⟨_, Flow.code_tensorCopy_30, by exact trivial⟩, ⟨_, Flow.code_tensorCopy_31, by exact trivial⟩]

theorem epi_fence_code (k : Fin 8) :
    ∃ ins, kernel.code[(Site.fence k).pc]? = some ins ∧ AdvancesOp ins.op := by
  fin_cases k
  exacts [⟨_, Flow.code_fenceProxy_5, by exact trivial⟩,
    ⟨_, Flow.code_fenceProxy_6, by exact trivial⟩,
    ⟨_, Flow.code_fenceProxy_7, by exact trivial⟩, ⟨_, Flow.code_fenceProxy_8, by exact trivial⟩,
    ⟨_, Flow.code_fenceProxy_9, by exact trivial⟩, ⟨_, Flow.code_fenceProxy_10, by exact trivial⟩,
    ⟨_, Flow.code_fenceProxy_11, by exact trivial⟩, ⟨_, Flow.code_fenceProxy_12, by exact trivial⟩]

theorem epi_barB_branch (k : Fin 8) :
    kernel.code[(Site.barB k).pc + 1]? =
      some ⟨some (epi_barPred k, false), .bra ((Site.commit k).pc - 1) false⟩ := by
  fin_cases k
  exacts [Flow.code_921, Flow.code_941, Flow.code_962, Flow.code_983, Flow.code_1004,
    Flow.code_1025, Flow.code_1046, Flow.code_1067]

theorem epi_barPred_val (L : Launch) (g : Nat) (d : D) (k : Fin 8) :
    valueOf L g d (epi_barPred k) =
      Value.pred (decide ((tidOf L g / 32 % 4) ||| (tidOf L g % 32) ≠ 0)) := by
  fin_cases k
  all_goals
    simp only [epi_barPred]
    cons_values

theorem epi_holds_of_mem {R : Nat → Option Value} :
    ∀ {l : List (Nat × Value)}, (∀ p ∈ l, R p.1 = some p.2) → Holds R l
  | [], _ => trivial
  | p :: l, h => ⟨h p (by simp), epi_holds_of_mem fun q hq => h q (by simp [hq])⟩

theorem epi_holds_facts_of {R : Nat → Option Value} {L : Launch} {g pc pc' : Nat} {d d' : D}
    (h : Holds R (factsAt L g pc d)) (hsub : ∀ r ∈ Flow.live pc', r ∈ Flow.live pc)
    (hval : ∀ r ∈ Flow.live pc', valueOf L g d r = valueOf L g d' r) :
    Holds R (factsAt L g pc' d') := by
  unfold factsAt Flow.factsFrom
  apply epi_holds_of_mem
  intro p hp
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hp
  have hm := holds_mem h (Flow.mem_factsFrom (hsub r hr))
  simp only
  rw [← hval r hr]
  exact hm

/-- The fence's row coordinate `512 m + 128 q + 256 r` as the code computes it: the shifted
`m`, or-ed with `128 q`, plus the shifted cluster rank `r`. -/
theorem epi_r408 (m q r : Nat) (hm : m < 16) (hq : q < 2) (hr : r < 2) :
    truncBits 32 (truncBits 32 (truncBits 32 (if (truncBits 32 (BitVec.ofInt 64 9)).toNat ≥ 32 then
      0
        else truncBits 32 (truncBits 32 (BitVec.ofNat 64 m) <<<
          (truncBits 32 (BitVec.ofInt 64 9)).toNat))
      ||| truncBits 32 (BitVec.ofNat 64 (128 * q))) +
      truncBits 32 (if (truncBits 32 (BitVec.ofInt 64 8)).toNat ≥ 32 then 0
        else truncBits 32 (truncBits 32 (truncBits 32 (BitVec.ofNat 64 r)) <<<
          (truncBits 32 (BitVec.ofInt 64 8)).toNat))) =
      BitVec.ofNat 64 (512 * m + 128 * q + 256 * r) := by
  have key : ∀ m < 16, ∀ q < 2, ∀ r < 2,
      truncBits 32 (truncBits 32 (truncBits 32 (if (truncBits 32 (BitVec.ofInt 64 9)).toNat ≥
        32 then 0
          else truncBits 32 (truncBits 32 (BitVec.ofNat 64 m) <<<
            (truncBits 32 (BitVec.ofInt 64 9)).toNat))
        ||| truncBits 32 (BitVec.ofNat 64 (128 * q))) +
        truncBits 32 (if (truncBits 32 (BitVec.ofInt 64 8)).toNat ≥ 32 then 0
          else truncBits 32 (truncBits 32 (truncBits 32 (BitVec.ofNat 64 r)) <<<
            (truncBits 32 (BitVec.ofInt 64 8)).toNat))) =
        BitVec.ofNat 64 (512 * m + 128 * q + 256 * r) := by
    table_decide
  exact key m hm q hq r hr

/-- `256 n` or-ed with a constant `c` below `256` (a multiple of 32) is `256 n + c`: the store
offsets of the fence's slice, one lemma per constant. -/
syntax "epi_or_lemma " ident num : command
macro_rules
  | `(command| epi_or_lemma $name $c) => `(
    theorem $name (n : Nat) (hn : n < 32) :
        truncBits 32 (if (truncBits 32 (BitVec.ofInt 64 8)).toNat ≥ 32 then 0
          else truncBits 32 (truncBits 32 (BitVec.ofNat 64 n) <<<
            (truncBits 32 (BitVec.ofInt 64 8)).toNat))
          ||| truncBits 32 (BitVec.ofInt 64 $c) = BitVec.ofNat 64 (256 * n + $c) := by
      have key : ∀ n < 32, truncBits 32 (if (truncBits 32 (BitVec.ofInt 64 8)).toNat ≥ 32 then 0
          else truncBits 32 (truncBits 32 (BitVec.ofNat 64 n) <<<
            (truncBits 32 (BitVec.ofInt 64 8)).toNat))
          ||| truncBits 32 (BitVec.ofInt 64 $c) = BitVec.ofNat 64 (256 * n + $c) := by
        table_decide
      exact key n hn)

epi_or_lemma epi_or_32 32
epi_or_lemma epi_or_64 64
epi_or_lemma epi_or_96 96
epi_or_lemma epi_or_128 128
epi_or_lemma epi_or_160 160
epi_or_lemma epi_or_192 192
epi_or_lemma epi_or_224 224

/-- The sub-aware abstract state of a thread at a site: the pc and the element of the
instruction (`sub`), the registers the site's facts give. -/
def AtS (L : Launch) (g : Nat) (t : TState) (d : D) : Prop :=
  t.pc = d.site.pc ∧ t.sub = d.site.sub ∧ t.acc = [] ∧ t.fault = none ∧ Holds t.regs (facts L g d)

/-- Every store site is a four-element vector store. -/
theorem epi_store_code (k : Fin 8) (i : Fin 4) (el : Fin 4) :
    ∃ ins, kernel.code[(Site.store k i el).pc]? = some ins ∧
      ∃ base off a0 a1 a2 a3, ins.op = .mem
        { kind := .store, space := some (.shared .cta), sem := .weak, elem := .int .u 32,
          vec := 4, addr := ⟨.reg base 32, off⟩, srcs := [a0, a1, a2, a3] } := by
  fin_cases k <;> fin_cases i
  exacts [⟨_, Flow.code_916, _, _, _, _, _, _, rfl⟩,
    ⟨_, Flow.code_917, _, _, _, _, _, _, rfl⟩,
    ⟨_, Flow.code_918, _, _, _, _, _, _, rfl⟩,
    ⟨_, Flow.code_919, _, _, _, _, _, _, rfl⟩,
    ⟨_, Flow.code_936, _, _, _, _, _, _, rfl⟩,
    ⟨_, Flow.code_937, _, _, _, _, _, _, rfl⟩,
    ⟨_, Flow.code_938, _, _, _, _, _, _, rfl⟩,
    ⟨_, Flow.code_939, _, _, _, _, _, _, rfl⟩,
    ⟨_, Flow.code_957, _, _, _, _, _, _, rfl⟩,
    ⟨_, Flow.code_958, _, _, _, _, _, _, rfl⟩,
    ⟨_, Flow.code_959, _, _, _, _, _, _, rfl⟩,
    ⟨_, Flow.code_960, _, _, _, _, _, _, rfl⟩,
    ⟨_, Flow.code_978, _, _, _, _, _, _, rfl⟩,
    ⟨_, Flow.code_979, _, _, _, _, _, _, rfl⟩,
    ⟨_, Flow.code_980, _, _, _, _, _, _, rfl⟩,
    ⟨_, Flow.code_981, _, _, _, _, _, _, rfl⟩,
    ⟨_, Flow.code_999, _, _, _, _, _, _, rfl⟩,
    ⟨_, Flow.code_1000, _, _, _, _, _, _, rfl⟩,
    ⟨_, Flow.code_1001, _, _, _, _, _, _, rfl⟩,
    ⟨_, Flow.code_1002, _, _, _, _, _, _, rfl⟩,
    ⟨_, Flow.code_1020, _, _, _, _, _, _, rfl⟩,
    ⟨_, Flow.code_1021, _, _, _, _, _, _, rfl⟩,
    ⟨_, Flow.code_1022, _, _, _, _, _, _, rfl⟩,
    ⟨_, Flow.code_1023, _, _, _, _, _, _, rfl⟩,
    ⟨_, Flow.code_1041, _, _, _, _, _, _, rfl⟩,
    ⟨_, Flow.code_1042, _, _, _, _, _, _, rfl⟩,
    ⟨_, Flow.code_1043, _, _, _, _, _, _, rfl⟩,
    ⟨_, Flow.code_1044, _, _, _, _, _, _, rfl⟩,
    ⟨_, Flow.code_1062, _, _, _, _, _, _, rfl⟩,
    ⟨_, Flow.code_1063, _, _, _, _, _, _, rfl⟩,
    ⟨_, Flow.code_1064, _, _, _, _, _, _, rfl⟩,
    ⟨_, Flow.code_1065, _, _, _, _, _, _, rfl⟩]

/-- The element write of a four-element store continues at `afterStore`. -/
theorem epi_fires_store {A : List Assumption} {L : Launch} {g : Nat} {t u : TState}
    {base : Nat} {off : Int} {a0 a1 a2 a3 : Opnd} {pc : Nat} {e : Event}
    (hf : Fires pc (eventTmpl A L g t (.mem
      { kind := .store, space := some (.shared .cta), sem := .weak, elem := .int .u 32,
        vec := 4, addr := ⟨.reg base 32, off⟩, srcs := [a0, a1, a2, a3] })) e (some u)) :
    u = afterStore t [a0, a1, a2, a3] := by
  have hm := memTmpl_store (A := A) (L := L) (g := g) (t := t) (sp := .shared) (base := base)
    (w := 32)
    (a := { kind := .store, space := some (.shared .cta), sem := .weak, elem := .int .u 32,
            vec := 4, addr := ⟨.reg base 32, off⟩, srcs := [a0, a1, a2, a3] })
    rfl rfl rfl rfl (by simp)
  simp only [eventTmpl, hm, storeTmpl] at hf
  split at hf
  · simp [Fires] at hf
  · split at hf
    · simp [Fires] at hf
    · split at hf
      · simp [Fires] at hf
      · obtain ⟨-, hu⟩ := hf
        exact Option.some.inj hu

theorem epi_pc_store_succ : ∀ (k : Fin 8) (i : Fin 4), i.val + 1 < 4 →
    Flow.store.getD (4 * k.val + i.val) 0 + 1 = Flow.store.getD (4 * k.val + (i.val + 1)) 0 := by
  table_decide

theorem epi_pc_store_barB : ∀ (k : Fin 8) (i : Fin 4), ¬ (i.val + 1 < 4) →
    Flow.store.getD (4 * k.val + i.val) 0 + 1 = Flow.bar.getD (2 + 2 * k.val) 0 := by
  table_decide

theorem site_ok {L : Launch} {g : Nat} (d : D) :
    ∃ ins, kernel.code[d.site.pc]? = some ins ∧ ins.op.isLocal = false ∧
      Code.GuardTrue (facts L g d) ins.guard := by
  obtain ⟨s, m, n, m', n', cp, ap, resp, x, acc, base⟩ := d
  cases s with
  | setMaxReg => exact ⟨_, Flow.code_setMaxReg_1, rfl, trivial⟩
  | clcWait => exact ⟨_, Flow.code_707, rfl, trivial⟩
  | clcLoad => exact ⟨_, Flow.code_711, rfl, trivial⟩
  | clcStatus => exact ⟨_, Flow.code_714, rfl, trivial⟩
  | clcFirst =>
    refine ⟨_, Flow.code_718, rfl, ?_⟩
    have hm := Flow.mem_factsFrom (val := valueOf L g ⟨.clcFirst, m, n, m', n', cp, ap, resp, x,
      acc, base⟩)
      (show 1028 ∈ Flow.live Site.clcFirst.pc by table_decide)
    have hv : valueOf L g ⟨.clcFirst, m, n, m', n', cp, ap, resp, x, acc, base⟩ 1028 =
        Value.pred true := by
      cons_values
      rfl
    show (1028, Value.pred true) ∈ facts L g ⟨.clcFirst, m, n, m', n', cp, ap, resp, x, acc, base⟩
    exact hv ▸ hm
  | clcFence => exact ⟨_, Flow.code_719, rfl, trivial⟩
  | clcBar => exact ⟨_, Flow.code_720, rfl, trivial⟩
  | ack =>
    refine ⟨_, Flow.code_728, rfl, ?_⟩
    have hm := Flow.mem_factsFrom (val := valueOf L g ⟨.ack, m, n, m', n', cp, ap, resp, x, acc,
      base⟩)
      (show 1029 ∈ Flow.live Site.ack.pc by table_decide)
    have hv : valueOf L g ⟨.ack, m, n, m', n', cp, ap, resp, x, acc, base⟩ 1029 =
        Value.pred true := by
      cons_values
    show (1029, Value.pred true) ∈ facts L g ⟨.ack, m, n, m', n', cp, ap, resp, x, acc, base⟩
    exact hv ▸ hm
  | accWait => exact ⟨_, Flow.code_746, rfl, trivial⟩
  | load j =>
    fin_cases j
    exacts [⟨_, Flow.code_749, rfl, trivial⟩, ⟨_, Flow.code_759, rfl, trivial⟩,
      ⟨_, Flow.code_769, rfl, trivial⟩, ⟨_, Flow.code_779, rfl, trivial⟩,
      ⟨_, Flow.code_789, rfl, trivial⟩, ⟨_, Flow.code_799, rfl, trivial⟩,
      ⟨_, Flow.code_809, rfl, trivial⟩, ⟨_, Flow.code_819, rfl, trivial⟩,
      ⟨_, Flow.code_829, rfl, trivial⟩, ⟨_, Flow.code_839, rfl, trivial⟩,
      ⟨_, Flow.code_849, rfl, trivial⟩, ⟨_, Flow.code_859, rfl, trivial⟩,
      ⟨_, Flow.code_869, rfl, trivial⟩, ⟨_, Flow.code_879, rfl, trivial⟩,
      ⟨_, Flow.code_889, rfl, trivial⟩, ⟨_, Flow.code_899, rfl, trivial⟩]
  | loadWait j =>
    fin_cases j
    exacts [⟨_, Flow.code_750, rfl, trivial⟩, ⟨_, Flow.code_760, rfl, trivial⟩,
      ⟨_, Flow.code_770, rfl, trivial⟩, ⟨_, Flow.code_780, rfl, trivial⟩,
      ⟨_, Flow.code_790, rfl, trivial⟩, ⟨_, Flow.code_800, rfl, trivial⟩,
      ⟨_, Flow.code_810, rfl, trivial⟩, ⟨_, Flow.code_820, rfl, trivial⟩,
      ⟨_, Flow.code_830, rfl, trivial⟩, ⟨_, Flow.code_840, rfl, trivial⟩,
      ⟨_, Flow.code_850, rfl, trivial⟩, ⟨_, Flow.code_860, rfl, trivial⟩,
      ⟨_, Flow.code_870, rfl, trivial⟩, ⟨_, Flow.code_880, rfl, trivial⟩,
      ⟨_, Flow.code_890, rfl, trivial⟩, ⟨_, Flow.code_900, rfl, trivial⟩]
  | accArrive =>
    refine ⟨_, Flow.code_913, rfl, ?_⟩
    have hm := Flow.mem_factsFrom (val := valueOf L g ⟨.accArrive, m, n, m', n', cp, ap, resp, x,
      acc, base⟩)
      (show 1031 ∈ Flow.live Site.accArrive.pc by table_decide)
    have hv : valueOf L g ⟨.accArrive, m, n, m', n', cp, ap, resp, x, acc, base⟩ 1031 =
        Value.pred true := by
      cons_values
    show (1031, Value.pred true) ∈ facts L g ⟨.accArrive, m, n, m', n', cp, ap, resp, x, acc, base⟩
    exact hv ▸ hm
  | drain k =>
    fin_cases k
    exacts [⟨_, Flow.code_914, rfl, trivial⟩, ⟨_, Flow.code_934, rfl, trivial⟩,
      ⟨_, Flow.code_955, rfl, trivial⟩, ⟨_, Flow.code_976, rfl, trivial⟩,
      ⟨_, Flow.code_997, rfl, trivial⟩, ⟨_, Flow.code_1018, rfl, trivial⟩,
      ⟨_, Flow.code_1039, rfl, trivial⟩, ⟨_, Flow.code_1060, rfl, trivial⟩]
  | barA k =>
    fin_cases k
    exacts [⟨_, Flow.code_915, rfl, trivial⟩, ⟨_, Flow.code_935, rfl, trivial⟩,
      ⟨_, Flow.code_956, rfl, trivial⟩, ⟨_, Flow.code_977, rfl, trivial⟩,
      ⟨_, Flow.code_998, rfl, trivial⟩, ⟨_, Flow.code_1019, rfl, trivial⟩,
      ⟨_, Flow.code_1040, rfl, trivial⟩, ⟨_, Flow.code_1061, rfl, trivial⟩]
  | barB k =>
    fin_cases k
    exacts [⟨_, Flow.code_920, rfl, trivial⟩, ⟨_, Flow.code_940, rfl, trivial⟩,
      ⟨_, Flow.code_961, rfl, trivial⟩, ⟨_, Flow.code_982, rfl, trivial⟩,
      ⟨_, Flow.code_1003, rfl, trivial⟩, ⟨_, Flow.code_1024, rfl, trivial⟩,
      ⟨_, Flow.code_1045, rfl, trivial⟩, ⟨_, Flow.code_1066, rfl, trivial⟩]
  | store k i el =>
    fin_cases k <;> fin_cases i
    exacts [⟨_, Flow.code_916, rfl, trivial⟩, ⟨_, Flow.code_917, rfl, trivial⟩,
      ⟨_, Flow.code_918, rfl, trivial⟩, ⟨_, Flow.code_919, rfl, trivial⟩,
      ⟨_, Flow.code_936, rfl, trivial⟩, ⟨_, Flow.code_937, rfl, trivial⟩,
      ⟨_, Flow.code_938, rfl, trivial⟩, ⟨_, Flow.code_939, rfl, trivial⟩,
      ⟨_, Flow.code_957, rfl, trivial⟩, ⟨_, Flow.code_958, rfl, trivial⟩,
      ⟨_, Flow.code_959, rfl, trivial⟩, ⟨_, Flow.code_960, rfl, trivial⟩,
      ⟨_, Flow.code_978, rfl, trivial⟩, ⟨_, Flow.code_979, rfl, trivial⟩,
      ⟨_, Flow.code_980, rfl, trivial⟩, ⟨_, Flow.code_981, rfl, trivial⟩,
      ⟨_, Flow.code_999, rfl, trivial⟩, ⟨_, Flow.code_1000, rfl, trivial⟩,
      ⟨_, Flow.code_1001, rfl, trivial⟩, ⟨_, Flow.code_1002, rfl, trivial⟩,
      ⟨_, Flow.code_1020, rfl, trivial⟩, ⟨_, Flow.code_1021, rfl, trivial⟩,
      ⟨_, Flow.code_1022, rfl, trivial⟩, ⟨_, Flow.code_1023, rfl, trivial⟩,
      ⟨_, Flow.code_1041, rfl, trivial⟩, ⟨_, Flow.code_1042, rfl, trivial⟩,
      ⟨_, Flow.code_1043, rfl, trivial⟩, ⟨_, Flow.code_1044, rfl, trivial⟩,
      ⟨_, Flow.code_1062, rfl, trivial⟩, ⟨_, Flow.code_1063, rfl, trivial⟩,
      ⟨_, Flow.code_1064, rfl, trivial⟩, ⟨_, Flow.code_1065, rfl, trivial⟩]
  | fence k =>
    fin_cases k
    exacts [⟨_, Flow.code_922, rfl, trivial⟩, ⟨_, Flow.code_942, rfl, trivial⟩,
      ⟨_, Flow.code_963, rfl, trivial⟩, ⟨_, Flow.code_984, rfl, trivial⟩,
      ⟨_, Flow.code_1005, rfl, trivial⟩, ⟨_, Flow.code_1026, rfl, trivial⟩,
      ⟨_, Flow.code_1047, rfl, trivial⟩, ⟨_, Flow.code_1068, rfl, trivial⟩]
  | tma k =>
    fin_cases k
    exacts [⟨_, Flow.code_931, rfl, trivial⟩, ⟨_, Flow.code_952, rfl, trivial⟩,
      ⟨_, Flow.code_973, rfl, trivial⟩, ⟨_, Flow.code_994, rfl, trivial⟩,
      ⟨_, Flow.code_1015, rfl, trivial⟩, ⟨_, Flow.code_1036, rfl, trivial⟩,
      ⟨_, Flow.code_1057, rfl, trivial⟩, ⟨_, Flow.code_1078, rfl, trivial⟩]
  | commit k =>
    fin_cases k
    exacts [⟨_, Flow.code_933, rfl, trivial⟩, ⟨_, Flow.code_954, rfl, trivial⟩,
      ⟨_, Flow.code_975, rfl, trivial⟩, ⟨_, Flow.code_996, rfl, trivial⟩,
      ⟨_, Flow.code_1017, rfl, trivial⟩, ⟨_, Flow.code_1038, rfl, trivial⟩,
      ⟨_, Flow.code_1059, rfl, trivial⟩, ⟨_, Flow.code_1080, rfl, trivial⟩]
  | finalDrain => exact ⟨_, Flow.code_1086, rfl, trivial⟩
  | exitArrive => exact ⟨_, Flow.code_1088, rfl, trivial⟩
  | exitWait => exact ⟨_, Flow.code_1089, rfl, trivial⟩
  | relinquish => exact ⟨_, Flow.code_1091, rfl, trivial⟩
  | ldBase => exact ⟨_, Flow.code_1093, rfl, trivial⟩
  | dealloc => exact ⟨_, Flow.code_1095, rfl, trivial⟩
  | exit => exact ⟨_, Flow.code_1096, rfl, trivial⟩

end
end PTX.Kernels.Fp16Gemm8192.Proof.Consumer
