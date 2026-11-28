-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Softmax.Strict.Base
public import Lemmas.Flow.SegQFCtl
public import Lemmas.Flow.SegQFLane
public import Lemmas.Flow.StepsQFP
import Kernels.InklingRelDecode.Proof.Lib.RulesFrame
import Kernels.InklingRelDecode.Gen.StepSoftmax39
import Kernels.InklingRelDecode.Flow.Code.Part036
import Lemmas.Flow.IssueNext
public import Kernels.InklingRelDecode.Proof.Lib.LaneStrict

@[expose] public section

/-! # Strict spans that write control registers, and the steps around them

`late_ctl a, b using vals` is `segqf_ctlt` for the late range: the stretch `[a, b)` is cut into
exact pieces (the instructions that write a register of the facts at the end, proved by `seg_fp` and
the closing tactic `vals`) and typed pieces (the tables of `lateQt`). A site's span starts at the
facts of the next pc, which `SegQ.fromFacts` weakens to the facts of the site. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Strict
open PTX PTX.Proof PTX.Flow PTX.Flow.TyG PTX.Flow.Havoc PTX.Assumption
open PTX.Kernels.InklingRelDecode.Gen.TypedLateQt

set_option maxRecDepth 100000

set_option hygiene false in
macro "late_ctl " a:num ", " b:num " using " vals:tacticSeq : tactic => `(tactic|
  segqf_ctlt lateQt, (absF5_sound (fp3_of (L := L) (g := g) (a := $a) (b := $b)
    (by decide +kernel))),
    (fp3_of (L := L) (g := g) (a := $a) (b := $b) (by decide +kernel)).plain.plain.segs,
    Lib.rulesFrame using $vals)

theorem val_1709 (e : Control.Entry) (L : Launch) (g : Nat) (d : Control.D) :
    Control.valueOf e L g d 1709 = Control.u32 (L.sharedBase + d.i % 2 * 8 + 213296) := by
  simp [Control.valueOf, Control.scalarValue]

theorem sum_1709 (n : Nat) :
    Value.bits 32 (truncBits 32 (truncBits 32 (BitVec.ofNat 64 (n % 2 ^ 32)) +
      truncBits 32 (BitVec.ofInt 64 213296))) = Control.u32 (n + 213296) := by
  have h : BitVec.ofInt 64 213296 = BitVec.ofNat 64 213296 := rfl
  rw [h, Lib.sum_bits]
  exact congrArg b32 (by omega)

theorem val_942 (e : Control.Entry) (L : Launch) (g : Nat) (d : Control.D) :
    Control.valueOf e L g d 942 = b32 (d.i % 2 * 128) := by
  simp [Control.valueOf, Control.scalarValue]

theorem val_943 (e : Control.Entry) (L : Launch) (g : Nat) (d : Control.D) :
    Control.valueOf e L g d 943 = Control.basePlus e.base (d.i % 2 * 128) := by
  simp [Control.valueOf, Control.scalarValue]

theorem shl_1259 (n : Nat) (_h : n < 2) :
    Value.bits 32 (if (truncBits 32 (BitVec.ofInt 64 7)).toNat ≥ 32 then 0
      else truncBits 32 (truncBits 32 (BitVec.ofNat 64 n) <<<
        (truncBits 32 (BitVec.ofInt 64 7)).toNat)) = b32 (n * 128) := by
  interval_cases n <;> decide

theorem add_1260 (a : Nat) :
    Value.bits 32 (truncBits 32 (truncBits 32 (BitVec.ofNat 64 a) + truncBits 32 0#64)) =
      Control.basePlus (b32 0) a := by
  rw [Lib.sum_bits a 0]
  simp [Control.basePlus, Control.u32, Lib.word, b32, Value.regBits]
  have h0 : (truncBits 32 0#64).toNat = 0 := by decide
  rw [h0, Nat.zero_add]

/-- The closing tactic of the exact pieces whose values are closed forms of `valueOf`. -/
macro "late_vals" : tactic => `(tactic| first
  | (simp [Control.valueOf, Control.scalarValue]; done)
  | (rw [val_1709]; exact sum_1709 _)
  | (rw [val_942]; exact shl_1259 _ (Nat.mod_lt _ (by decide)))
  | (rw [val_943]; exact add_1260 _)
  | decide)

variable {e : Control.Entry} {L : Launch} {g : Nat}

/-- The facts of a span's table that the control facts of the site `s` (at `p`) contain. -/
theorem ctl_in {i : Nat} {v : Control.Carry} {w : Data.Vals} {q p : Nat} (s : Site) (hp : s.pc = p)
    (h : ∀ r ∈ Control.ctlLive q, r ∈ Control.ctlLive p) :
    ∀ a ∈ factsFrom (Control.ctlLive q) (Control.valueOf e L g ⟨s, i, v⟩),
      a ∈ (Data.code e L g).facts ⟨⟨s, i, v⟩, w⟩ := by
  intro a ha
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp ha
  refine List.mem_append_left _ ?_
  change _ ∈ factsFrom (Control.ctlLive s.pc) _
  rw [hp]
  exact mem_factsFrom (h r hr)

/-- The facts of the state of the site `s` are its table at `q` and its data facts. -/
theorem ctl_out {i : Nat} {v : Control.Carry} {w : Data.Vals} {q : Nat} (s : Site) (hp : s.pc = q) :
    ∀ a ∈ (Data.code e L g).facts ⟨⟨s, i, v⟩, w⟩,
      a ∈ factsFrom (Control.ctlLive q) (Control.valueOf e L g ⟨s, i, v⟩) ++
        Data.dF L ⟨⟨s, i, v⟩, w⟩ := by
  intro a ha
  rcases List.mem_append.mp ha with h | h
  · refine List.mem_append_left _ ?_
    change _ ∈ factsFrom (Control.ctlLive s.pc) _ at h
    rwa [hp] at h
  · exact List.mem_append_right _ h

variable {i : Nat} {v : Control.Carry} {w : Data.Vals}

/-- The `bar.sync` before the accumulator store: the span sets the predicate of the guard. -/
theorem sstep_bar24 (ev : Event) :
    (Data.code e L g).StepForQP (QTF lateQt) (TauAll kernel Assumptions.all L g (LateR' L g))
      LWf ⟨⟨.bar24, i, v⟩, w⟩ ev := by
  refine Code.StepForQP.ofInv fun hinv => Code.advanceFP (C := Data.code e L g)
    (d := ⟨⟨.bar24, i, v⟩, w⟩) (dn := ⟨⟨.stO, i, v⟩, w⟩) Flow.code_2326
    (fun h => fires_barSyncN_next h) (fun _ => rfl) rfl rfl rfl rfl
    (Control.body_inv hinv rfl rfl) (by change afterF lateQt 2326 [] = true; decide +kernel) ?_ ev
  have e1 : (Data.code e L g).pc ⟨⟨.bar24, i, v⟩, w⟩ = 2326 := by
    change Site.pc .bar24 = 2326; decide +kernel
  have e2 : (Data.code e L g).pc ⟨⟨.stO, i, v⟩, w⟩ = 2328 := by
    change Site.pc .stO = 2328; decide +kernel
  rw [e1, e2]
  refine SegQ.laneConv _ (a := 2327) (b := 2328)
    (F' := Gen.rs_facts2 (Data.rsV L w) ++ factsFrom (Control.ctlLive 2327)
      (Control.valueOf e L g ⟨.bar24, i, v⟩))
    (G' := Gen.rs_facts2 (Data.rsV L w) ++ factsFrom (Control.ctlLive 2328)
      (Control.valueOf e L g ⟨.bar24, i, v⟩)) ?_ ?_ ?_
  · intro p hp
    rcases List.mem_append.mp hp with h | h
    · exact List.mem_append_right _ (by simpa [Data.dF, Data.dFS] using h)
    · exact ctl_in (w := w) .bar24 (q := 2327) (by decide +kernel : Site.pc .bar24 = 2326)
        (by decide +kernel) p h
  · intro p hp
    obtain h | h := List.mem_append.mp
      (ctl_out (w := w) .stO (by decide +kernel : Site.pc .stO = 2328) p hp)
    · exact List.mem_append_right _ h
    · exact List.mem_append_left _ (by simpa [Data.dF, Data.dFS] using h)
  · simp only [Gen.rs_facts2, List.cons_append, List.nil_append]
    late_ctl 2327, 2328 using late_vals

end PTX.Kernels.InklingRelDecode.Proof.Softmax.Strict
