-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.BlockSum.Proof.Protocol.Sync
public import Kernels.BlockSum.Proof.Thread.Facts
public import Lemmas.Flow.Scalars
public import Lemmas.Kernel.Memory
public import Lemmas.Execution.NoAsync
public import Lemmas.Order.Order
public import Lemmas.Step.ExitLast

@[expose] public section

/-! # The values the threads read and write

A thread's input load reads the launch content `A[g]`: no write covers it (`input_read`). So
its loaded value is that input, and its store to its shared cell writes it (`shared_write`).
Every access is a 4-byte aligned access of its word (`access_shape`), and two writes of one
footprint are one event (`writes_unique`). The barrier orders every thread's shared store
before the reads of its CTA's thread 0 (`shared_sync`), so each such read returns the cell's
input (`shared_read`). -/

namespace PTX.Kernels.BlockSum.Proof

open PTX PTX.Proof PTX.Flow

noncomputable section

local notation "Prod" => [Assumptions.idealAdd]

variable {L : Launch} {A B : Nat} {x : Nat → ℝ} {mem0 : Mem0} {X : Execution}

/-- The bytes of the `f32` value `y` as a read returns them. -/
def bytesOf (y : ℝ) : List (Option Byte) := (fl y).toBytes.map some

theorem rebuild_bytesOf (y : ℝ) : rebuild 3 (bytesOf y) = .ok (fl y) :=
  rebuild_scalar (by show 0 < 4; decide) rfl

theorem readVal_bytesOf (y : ℝ) : readVal (bytesOf y) = some (y : EReal) := by
  simp [readVal, rebuild_bytesOf, fl, Assumption.readEReal, pure, Except.pure]

/-- A sum of real readings is the reading of the sum. -/
theorem sum_coe {s : Finset Nat} {f : Nat → ℝ} :
    (∑ j ∈ s, ((f j : ℝ) : EReal)) = ((∑ j ∈ s, f j : ℝ) : EReal) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro a t ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, EReal.coe_add, ih]

theorem erealValue_coe_value (y : ℝ) :
    Assumption.erealValue .f32 (y : EReal) = .float .f32 y := by
  unfold Assumption.erealValue
  rw [ite_eq_right (EReal.coe_ne_top y), ite_eq_right (EReal.coe_ne_bot y)]
  simp

theorem noTma : kernel.NoTma := rfl

/-- **The input load reads the launch content**: no write covers `A[g]`. -/
theorem input_read (hpre : Pre L A B x mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts A B L X) {g pc : Nat} {bs : List (Option Byte)}
    (he : X.get (g, 0) = some ⟨pc, .rd { loc := gl (A + 4 * g), size := 4 } bs⟩) :
    bs = bytesOf (x g) := by
  have hg := Frame.lt_of_get hX he
  have hr : X.MemReads (.thread (g, 0)) { loc := gl (A + 4 * g), size := 4 } bs := Or.inl ⟨pc, he⟩
  have hlen := hX.read_length hr
  apply List.ext_getElem?
  intro k
  by_cases hk : k < 4
  · have hb : (bytesOf (x g))[k]? = some (some (fl (x g), k)) := by
      simp only [bytesOf, List.getElem?_map]
      exact congrArg _ (PTX.Proof.fl_byte _ hk)
    rw [hb]
    refine hX.launch_byte (e := .thread (g, 0)) (a := { loc := gl (A + 4 * g), size := 4 })
      (bs := bs) hr hk ?_
      (by simpa [gl, Loc.at, Nat.add_assoc] using hpre.input g hg k hk)
    intro w a' bs' hw hc
    obtain ⟨w, rfl, hw | ⟨old, hrmw⟩⟩ := Execution.NoTma.memWrites_thread
      ((noTma_of_consistent noTma hX).emptyAsync hX) hw
    · obtain ⟨pcw, hw⟩ := hw
      have hgw := Frame.lt_of_get hX hw
      rcases write_cases hpre hX ht hw with ⟨-, rfl, -⟩ | ⟨-, -, rfl, -⟩
      · simp [Acc.Covers, Loc.InRange, sh, gl, Loc.at] at hc
      · have hd := hpre.disjoint
        have hcw : w.1 / 256 < L.grid := by
          simp only [Launch.threads, hpre.block] at hgw; omega
        simp only [Acc.Covers, Loc.InRange, gl, Loc.at] at hc
        simp only [Launch.threads, hpre.block] at hg hd
        omega
    · exact absurd hrmw (no_rmw hpre hX)
  · rw [List.getElem?_eq_none (by simp only at hlen; omega), List.getElem?_eq_none]
    simp only [bytesOf, List.length_map]
    rw [show (fl (x g)).toBytes.length = 4 from rfl]
    omega

/-- A thread's first event is its input load, when it has one. -/
theorem first_event (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts A B L X) {g : Nat} {e : Event} (he : X.get (g, 0) = some e) :
    ∃ bs, e = ⟨Flow.load_0, .rd { loc := gl (A + 4 * g), size := 4 } bs⟩ := by
  have hg := Frame.lt_of_get hX he
  have hσ : stateAt A B L X g 0 = some (some { site := .input }) := Frame.stateAt_zero
  exact ht.event hg he hσ

/-- **A thread's second event is the store of its input to its shared cell.** -/
theorem shared_write (hpre : Pre L A B x mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts A B L X) {g : Nat} (hg : g < L.threads) (hl : 1 < (X.tr g).length) :
    X.get (g, 1) = some ⟨Flow.store_0,
      .wr { loc := sh (g / 256) (L.sharedBase + 4 * (g % 256)), size := 4 }
        (fl (x g)).toBytes⟩ := by
  obtain ⟨e0, he0⟩ : ∃ e, X.get (g, 0) = some e :=
    ⟨_, List.getElem?_eq_getElem (show 0 < (X.tr g).length by omega)⟩
  obtain ⟨bs0, rfl⟩ := first_event hX ht he0
  have hgood := input_read hpre hX ht he0
  subst hgood
  obtain ⟨e, he⟩ : ∃ e, X.get (g, 1) = some e := ⟨_, List.getElem?_eq_getElem hl⟩
  have hub : ∀ pc f, e ≠ ⟨pc, .ub f⟩ := by
    rintro pc f rfl
    have hσ := ht.ub hg he
    obtain ⟨j, d, e', hj, hσj, hej, hbad⟩ := ht.dead hg hl.le hσ
    obtain rfl : j = 0 := by omega
    have hd : d = { site := .input } := by
      have h0 : stateAt A B L X g 0 = some (some { site := .input }) := Frame.stateAt_zero
      rw [h0] at hσj
      exact (Option.some.inj (Option.some.inj hσj)).symm
    subst hd
    rcases hbad with hx | ⟨pc', a, bs, rfl, hb⟩
    · cases hx
    · rw [he0] at hej
      simp only [Option.some.injEq, Event.mk.injEq, Kind.rd.injEq] at hej
      obtain ⟨-, -, rfl⟩ := hej
      rcases hb with ⟨-, hb⟩ | ⟨h, -⟩
      · exact hb _ (rebuild_bytesOf _) rfl
      · cases h
  obtain ⟨-, d, hσ, hev, hk, hi⟩ := event_facts hpre hX ht he hub
  obtain ⟨bs', h0, hv⟩ := ht.input hg hσ (by
    intro hs; simp [D.idx, hs] at hk)
  rw [he0] at h0
  simp only [Option.some.injEq, Event.mk.injEq, Kind.rd.injEq, true_and] at h0
  rw [← h0, rebuild_bytesOf] at hv
  obtain ⟨s, v, i, acc, sm⟩ := d
  cases hv
  cases s with
  | share => simp only [SiteEvent] at hev; rw [he, hev]; rfl
  | exit => simp only [D.idx] at hk; split at hk <;> omega
  | input => simp only [D.idx] at hk; omega
  | bar => simp only [D.idx] at hk; omega
  | sum => simp only [D.idx] at hk; omega
  | out => simp only [D.idx] at hk; omega

theorem access_shape (hpre : Pre L A B x mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts A B L X) {e : EvId} {a : Acc} {w : Bool} (he : X.Access e a w) :
    (∃ addr, a = { loc := ⟨.global, 0, addr⟩, size := 4 } ∧ addr % 4 = 0) ∨
    (∃ addr, a = { loc := ⟨.shared, e.1 / 256, addr⟩, size := 4 } ∧ addr % 4 = 0) := by
  have ha := hpre.alignA
  have hb := hpre.alignB
  have hs := hpre.sharedAlign
  rcases he with ⟨bs, ⟨pc, hr⟩, -⟩ | ⟨bs, ⟨pc, hw⟩, -⟩ | ⟨old, new, hrmw⟩
  · rcases read_cases hpre hX ht hr with ⟨-, -, rfl⟩ | ⟨-, i, -, -, -, rfl⟩
    · exact .inl ⟨_, rfl, by omega⟩
    · exact .inr ⟨_, rfl, by omega⟩
  · rcases write_cases hpre hX ht hw with ⟨-, rfl, -⟩ | ⟨-, -, rfl, -⟩
    · exact .inr ⟨_, rfl, by omega⟩
    · exact .inl ⟨_, rfl, by omega⟩
  · exact absurd hrmw (no_rmw hpre hX)

/-- **Two overlapping accesses have one footprint.** -/
theorem overlapping_access_eq (hpre : Pre L A B x mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts A B L X) {e f : EvId} {a b : Acc} {we wf : Bool} (he : X.Access e a we)
    (hf : X.Access f b wf) (hov : a.Overlap b) : a = b := by
  obtain ⟨l, ⟨hs1, hc1, hl1, hu1⟩, ⟨hs2, hc2, hl2, hu2⟩⟩ := hov
  rcases access_shape hpre hX ht he with ⟨p, rfl, hp⟩ | ⟨p, rfl, hp⟩ <;>
    rcases access_shape hpre hX ht hf with ⟨q, rfl, hq⟩ | ⟨q, rfl, hq⟩
  · have hpq : p = q := by simp only at hl1 hu1 hl2 hu2; omega
    rw [hpq]
  · rw [hs1] at hs2; cases hs2
  · rw [hs1] at hs2; cases hs2
  · have hpq : p = q := by simp only at hl1 hu1 hl2 hu2; omega
    have hc : e.1 / 256 = f.1 / 256 := hc1.symm.trans hc2
    rw [hpq, hc]

/-- **Two writes of one footprint are one event.** -/
theorem writes_unique (hpre : Pre L A B x mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts A B L X) {e f : EvId} {a : Acc} {bs cs : List Byte}
    (he : X.Writes e a bs) (hf : X.Writes f a cs) : e = f := by
  obtain ⟨⟨g, k⟩, pc⟩ := (⟨e, he.choose⟩ : EvId × Nat)
  obtain ⟨pce, he⟩ := he
  obtain ⟨pcf, hf⟩ := hf
  have hge := Frame.lt_of_get hX he
  have hgf := Frame.lt_of_get hX hf
  rcases write_cases hpre hX ht he with ⟨hk, ha, -⟩ | ⟨hz, hk, ha, -⟩ <;>
    rcases write_cases hpre hX ht hf with ⟨hk', hb, -⟩ | ⟨hz', hk', hb, -⟩
  · have hloc := congrArg Acc.loc (ha.symm.trans hb)
    simp only [sh, Loc.mk.injEq] at hloc
    exact Prod.ext (by omega) (by omega)
  · rw [ha] at hb; cases hb
  · rw [ha] at hb; cases hb
  · have haddr := congrArg (fun a : Acc => a.loc.addr) (ha.symm.trans hb)
    simp only [gl] at haddr
    exact Prod.ext (by omega) (by omega)

/-- **A read of the reduction loop returns its cell's input.** -/
theorem shared_read (hpre : Pre L A B x mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts A B L X) {r i k pc : Nat}
    {bs : List (Option Byte)} (hi : i < 256) (hk : k = 3 + i)
    (he : X.get (r, k) = some ⟨pc,
      .rd { loc := sh (r / 256) (L.sharedBase + 4 * i), size := 4 } bs⟩) :
    bs = bytesOf (x (256 * (r / 256) + i)) := by
  have hr := Frame.lt_of_get hX he
  have hc : r / 256 < L.grid := by simp only [Launch.threads, hpre.block] at hr; omega
  set w := 256 * (r / 256) + i with hwdef
  have hw : w < L.threads := by simp only [Launch.threads, hpre.block]; omega
  have hwc : w / 256 = r / 256 := by omega
  obtain ⟨hlw, hbefore⟩ := shared_sync hpre hX ht r w k pc _ bs hw hwc he (by omega)
  have hwr := shared_write hpre hX ht hw (by omega)
  have hloc : sh (w / 256) (L.sharedBase + 4 * (w % 256)) = sh (r / 256) (L.sharedBase + 4 * i) :=
    by
    simp only [sh, Loc.mk.injEq, true_and]; constructor <;> omega
  rw [hloc] at hwr
  have hW : X.Writes (w, 1) { loc := sh (r / 256) (L.sharedBase + 4 * i), size := 4 }
      (fl (x w)).toBytes := ⟨_, hwr⟩
  have hR : X.Reads (r, k) { loc := sh (r / 256) (L.sharedBase + 4 * i), size := 4 } bs := ⟨_, he⟩
  have hlen := hX.read_length (e := .thread (r, k)) (Or.inl hR)
  apply List.ext_getElem?
  intro j
  by_cases hj : j < 4
  · have hb : (bytesOf (x w))[j]? = some (some (fl (x w), j)) := by
      simp only [bytesOf, List.getElem?_map]
      exact congrArg _ (PTX.Proof.fl_byte _ hj)
    rw [hb]
    have hs := hX.rf (.thread (r, k)) _ _ (Or.inl hR) |>.2 j hj
    cases hrk : X.rf (.thread (r, k)) j with
    | none =>
      have hh := hX.hidden (.thread (r, k)) _ bs j (.thread (w, 1)) _ _ (Or.inl hR) hj
        (Or.inl hW) (Acc.covers_at hj) (.direct (.inl hbefore))
      rw [hrk] at hh
      exact hh.elim
    | some w' =>
      rw [hrk] at hs
      obtain ⟨a, cs, hw', hcov, hbyte⟩ := hs
      obtain ⟨w', rfl, hwT | ⟨old, hrmw⟩⟩ := Execution.NoTma.memWrites_thread
        ((noTma_of_consistent noTma hX).emptyAsync hX) hw'
      · obtain ⟨pcw, hwr'⟩ := hwT
        have hA : X.Access w' a true := .inr (.inl ⟨cs, ⟨pcw, hwr'⟩, rfl⟩)
        have hB : X.Access (r, k) { loc := sh (r / 256) (L.sharedBase + 4 * i), size := 4 }
            false := .inl ⟨bs, hR, rfl⟩
        have ha : a = { loc := sh (r / 256) (L.sharedBase + 4 * i), size := 4 } :=
          overlapping_access_eq hpre hX ht hA hB ⟨_, hcov, Acc.covers_at hj⟩
        have hAw : X.Writes w' a cs := ⟨pcw, hwr'⟩
        subst ha
        have hwe := writes_unique hpre hX ht hAw hW
        subst hwe
        rw [hwr] at hwr'
        simp only [Option.some.injEq, Event.mk.injEq, Kind.wr.injEq, true_and] at hwr'
        rw [← hwr'.2] at hbyte
        have hfl : (fl (x w)).toBytes[j]? = some (fl (x w), j) := PTX.Proof.fl_byte _ hj
        simpa [wbyte, Loc.at, hfl] using hbyte
      · exact absurd hrmw (no_rmw hpre hX)
  · rw [List.getElem?_eq_none (by simp only at hlen; omega), List.getElem?_eq_none]
    simp only [bytesOf, List.length_map]
    rw [show (fl (x w)).toBytes.length = 4 from rfl]
    omega

end
end PTX.Kernels.BlockSum.Proof
