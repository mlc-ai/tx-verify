-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsBar2
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsStatic
public import Kernels.FlashAttn4Fwd.Proof.Thread.SoftmaxEvents
public import Kernels.FlashAttn4Fwd.Proof.Interface.Stats
public import Kernels.FlashAttn4Fwd.Proof.Interface.Score
public import Kernels.FlashAttn4Fwd.Proof.Interface.Schedule
public import Lemmas.Flow.WaitAcquire

@[expose] public section

/-! # The softmax warps' events

An event of a thread of warps 0 to 7 is fired from a prologue state (of a prologue kind) or from
a softmax state, with the role's run invariant (`Softmax.Counts`), its state invariant, its
concrete state and its site's event (`soft_origin`). From the site events: the thread's
named-barrier events are the start and end barriers (`bar 2, 416`) and the arrivals on its
statistics barrier `w + 3` (count 64), so its ordinal on the statistics barrier is its count of
arrivals there (`soft_barOrd`); its polls are of its stage's credit barrier at a `statsW` site
and of its stage's S-full barrier at a `sW` site, with the parity of the site's register
(`soft_wait`); its arrivals are on the leader's P-ready barriers (`soft_arrive`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- A softmax warp's statistics barrier: `k + 3 + 4 st` is the warp plus three. -/
theorem soft_statsId (L : Launch) (g : Nat) :
    Softmax.kOf L g + 3 + 4 * Softmax.stOf L g = warpOf L g + 3 := by
  simp only [Softmax.kOf, Softmax.stOf]
  omega

/-- The role's trips are the key blocks. -/
theorem soft_trips_eq (hpre : Pre P L mem0) : Softmax.trips L = kvBlocks P := by
  rw [Softmax.trips, kvBlocks, ← skOf_eq hpre]
  rfl

/-- The role's trips are at least one. -/
theorem soft_trips_pos (hpre : Pre P L mem0) : 1 ≤ Softmax.trips L := by
  have := skOf_eq hpre; have := hpre.skPos
  unfold Softmax.trips Work.n Work.sk
  omega

/-- Item `i` exists exactly when its work index is below the item count. -/
theorem soft_lt_items (hpre : Pre P L mem0) {g i : Nat} :
    i < Softmax.items L g ↔ workOf L g i < totOf L := by
  rw [Work.totOf_eq' hpre]
  exact Work.lt_T_iff hpre

/-- The leader CTA's location at offset `off` of the softmax. -/
theorem soft_leadLoc (L : Launch) (g off : Nat) :
    Softmax.leadLoc L g off = ⟨.shared, leadCta (ctaOf L g), L.sharedBase + off⟩ := by
  simp only [Softmax.leadLoc, leadCta, Softmax.sb, Loc.mk.injEq, true_and, and_true]
  omega

/-- **The origin of a softmax thread's event**: a prologue event, or the site event of a
softmax state with the role's run invariant. -/
theorem soft_origin (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (ht : Frame.Tracked (code L) X) {g k : Nat} {e : Event} (he : X.get (g, k) = some e)
    (hw : warpOf L g < 8) (hub : ∀ pc f, e ≠ ⟨pc, .ub f⟩) :
    (∃ p, Frame.stateAt (code L) X g k = some (some (.inl p)) ∧ Prologue.ProKind e.kind) ∨
    ∃ (d : Softmax.D) (t : TState) (ins : Instr) (o : Option TState),
      Frame.stateAt (code L) X g k = some (some (.inr (.softmax d))) ∧
      Softmax.Counts L g d ((X.tr g).take k) ∧ Softmax.Inv L g d ∧ Softmax.AtS L g d t ∧
      kernel.code[d.site.pc]? = some ins ∧ Fires d.site.pc (eventTmpl asms L g t ins.op) e o ∧
      Softmax.Ev L g d e := by
  have hg := Frame.lt_of_get hX he
  obtain ⟨d, t, ins, o, hσ, hJ, hat, hi, hc, hf⟩ :=
    event_origin hpre hX ht (fun g hg => roleJ_run hpre hg) he hub
  rcases d with p | r
  · refine .inl ⟨p, hσ, ?_⟩
    exact (pro_event hpre hX he hσ (fun f h => hub e.pc f (by rw [← h]))).proKind
  · have hrw := role_warp_run hpre hg
      (Frame.trace (C := code L) (fun _ hg => sound hpre hg) hX hg) k r hσ
    cases r with
    | softmax d =>
      refine .inr ⟨d, t, ins, o, hσ, hJ, hi, hat, hc, hf, ?_⟩
      cases o with
      | some u => exact Softmax.site_event hpre hg hi hat hc hf
      | none =>
        have hend := fires_none_ends hf
        have hx : e.kind = .exit := by
          rcases hend with ⟨f, hf'⟩ | hx
          · exact absurd (by obtain ⟨pc, k⟩ := e; simp only at hf'; rw [hf']) (hub e.pc f)
          · exact hx
        have hret : retOp ins.op = true := retOp_of_fires hf hx
        have hpc := OpPcsFast.mem kernel_ret_pcs hc hret
        simp only [List.mem_singleton] at hpc
        have hs := Cross.Softmax.site_exit d.site hpc
        unfold Softmax.Ev
        rw [hs]
        exact hx
    | _ => simp only [Role.kind, RoleKind.Warp] at hrw; omega

section
variable (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
  (ht : Frame.Tracked (code L) X)
include hpre hX ht

/-- The softmax state of a softmax thread's event of a kind the prologue does not fire. -/
theorem soft_state {g k : Nat} {e : Event} (he : X.get (g, k) = some e) (hw : warpOf L g < 8)
    (hub : ∀ pc f, e ≠ ⟨pc, .ub f⟩) (hpk : ¬ Prologue.ProKind e.kind) :
    ∃ (d : Softmax.D) (t : TState) (ins : Instr) (o : Option TState),
      Frame.stateAt (code L) X g k = some (some (.inr (.softmax d))) ∧
      Softmax.Counts L g d ((X.tr g).take k) ∧ Softmax.Inv L g d ∧ Softmax.AtS L g d t ∧
      kernel.code[d.site.pc]? = some ins ∧ Fires d.site.pc (eventTmpl asms L g t ins.op) e o ∧
      Softmax.Ev L g d e := by
  rcases soft_origin hpre hX ht he hw hub with ⟨p, -, hk⟩ | h
  · exact absurd hk hpk
  · exact h

/-- **A softmax thread's named-barrier event**: the start or end barrier (`bar 2, 416`), or an
arrival on its statistics barrier `w + 3`. -/
theorem soft_bar {g i pc id : Nat} {cnt : Option Nat} {m : BarMode} (hw : warpOf L g < 8)
    (he : X.get (g, i) = some ⟨pc, .bar id cnt m⟩) :
    (id = 2 ∧ cnt = some 416) ∨ (cnt = some 64 ∧ m = .arrive ∧ id = warpOf L g + 3) := by
  obtain ⟨d, -, -, -, -, -, -, -, -, -, hev⟩ :=
    soft_state hpre hX ht he hw (fun _ _ h => by cases h) (by simp [Prologue.ProKind])
  have hk := soft_statsId L g
  obtain ⟨site, i, tt, w, mm, l⟩ := d
  cases site <;> simp only [Softmax.Ev, Kind.bar.injEq, reduceCtorEq, exists_false] at hev
  all_goals first
    | exact .inl ⟨hev.1, hev.2.1⟩
    | exact .inr ⟨hev.2.1, hev.2.2, hev.1.trans hk⟩

/-- **The statistics-barrier ordinal of a softmax thread** is its count of arrivals there. -/
theorem soft_barOrd {g : Nat} (hw : warpOf L g < 8) (i : Nat) {id : Nat} (hid : id ≠ 2) :
    barOrd X g i id = barEvents id 64 .arrive ((X.tr g).take i) := by
  unfold barOrd barEvents
  apply List.countP_congr
  intro x hx
  obtain ⟨j, -, hj⟩ := get_of_mem_take hx
  obtain ⟨pc, k⟩ := x
  constructor
  · intro h
    cases k <;> simp only [Execution.isBarId, beq_iff_eq, reduceCtorEq] at h
    rename_i id' cnt m
    subst h
    rcases soft_bar hpre hX ht hw hj with ⟨rfl, -⟩ | ⟨rfl, rfl, -⟩
    · exact absurd rfl hid
    · simp [barIs]
  · intro h
    cases k <;> simp only [barIs] at h
    all_goals (try split at h) <;> simp_all [Execution.isBarId]

/-- The statistics-barrier ordinal of a softmax thread is the `gen` count of its state. -/
theorem soft_barOrd_gen {g i : Nat} {d : Softmax.D} (hw : warpOf L g < 8)
    (hc : Softmax.Counts L g d ((X.tr g).take i)) :
    barOrd X g i (warpOf L g + 3) = (Softmax.trips L + 1) * d.i + Softmax.genPos d := by
  rw [soft_barOrd hpre hX ht hw i (by omega), ← soft_statsId, hc.gen]

end

/-- A poll of the thread's CTA's barrier at `off`, with the parity its register holds. -/
theorem ev_waitPar {g : Nat} {t u : TState} {e : Event} {ins : Instr} {pc p r q off x : Nat}
    (hpre : Pre P L mem0)
    (hc : kernel.code[pc]? = some ⟨none, .mbarWait p r 0 (.reg q) true .cta⟩)
    (hr : t.regs r = some (Prologue.sb L off)) (hq : t.regs q = some (b32 (x % 2)))
    (hoff : off < 1024) (h8 : off % 8 = 0) (hins : kernel.code[pc]? = some ins)
    (hf : Fires pc (eventTmpl asms L g t ins.op) e (some u)) :
    ∃ ok acq sc, e.kind = .wait (Softmax.ownLoc L g off) (x % 2) ok acq sc := by
  obtain rfl := Option.some.inj (hins.symm.trans hc)
  have hbase := hpre.sharedRange
  have hal := hpre.sharedAlignment
  unfold sharedBytes at hbase
  simp only [Prologue.sb] at hr
  obtain ⟨ok, acq, sc, he, -⟩ := fires_wait_at (L := L) (g := g) (A := asms)
    (mbarLoc_b32 (L := L) (g := g) hr (by omega) (by omega)) (readBits_b32' hq) hf
  refine ⟨ok, acq, sc, ?_⟩
  rw [he]
  have hx : x % 2 < 2 := Nat.mod_lt _ (by decide)
  simp only [truncBits, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (show x % 2 < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show x % 2 < 2 ^ 32 by omega),
    Nat.mod_eq_of_lt (show x % 2 < 2 ^ 64 by omega), Nat.mod_mod]
  rfl

section
variable (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
  (ht : Frame.Tracked (code L) X)
include hpre hX ht

/-- **A softmax thread's exit** is at the exit site. -/
theorem soft_exit_state {g k pc : Nat} (hw : warpOf L g < 8)
    (he : X.get (g, k) = some ⟨pc, .exit⟩) :
    ∃ d : Softmax.D, Frame.stateAt (code L) X g k = some (some (.inr (.softmax d))) ∧
      Softmax.Counts L g d ((X.tr g).take k) ∧ Softmax.Inv L g d ∧ d.site = .exit := by
  obtain ⟨d, t, ins, o, hσ, hc, hi, -, hcode, hf, -⟩ :=
    soft_state hpre hX ht he hw (fun _ _ h => by cases h) (by simp [Prologue.ProKind])
  refine ⟨d, hσ, hc, hi, ?_⟩
  have hret : retOp ins.op = true := retOp_of_fires hf rfl
  have hpc := OpPcsFast.mem kernel_ret_pcs hcode hret
  simp only [List.mem_singleton] at hpc
  exact Cross.Softmax.site_exit d.site hpc

end

end
end PTX.Kernels.FlashAttn4Fwd.Proof
