-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Ref.Compute.Events

@[expose] public section

/-! # The ledger of the Compute phase along its steps

* The ledger of one event (`ledEv`) by the event's kind: a matrix event adds one matrix event
  (`dMat`), a read, a write and a fence add nothing (`dZero`), a `bar.sync 0` and the named
  barrier add one barrier (`dBar0`, `dBar8`), a successful poll of the mbarrier `b` adds one
  poll of `b` (`pollLed b`), an arrival on `b` one arrival (`arrLed b`), a failed poll nothing.
* The ledger of a position (`led`) along each step of the phase: `led_body` for the 262
  straight steps of a tile, and one lemma for each control step.
* The counted events of a position (`Pos.idx`) along a step.

`uses n t s` (`Protocol/Layout.lean`) is the number of tiles before `t` that use stage `s` of an
`n`-stage pipeline; tile `t` uses stage `t % n`, so the count of stage `s` grows by one exactly
when `t % n = s` (`uses_succ2`, `uses_succ3`). -/

namespace PTX.Kernels.FlashKdaFwd.Proof.Ref.Compute
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32
open PTX.Kernels.FlashKdaFwd PTX.Kernels.FlashKdaFwd.Proof.Thread
open PTX.Kernels.FlashKdaFwd.Proof.Ref PTX.Kernels.FlashKdaFwd.Recurrence
open PTX.Kernels.FlashKdaFwd.Protocol (Bar uses)

noncomputable section
set_option linter.unusedSimpArgs false

variable {P : Params} {L : Launch} {g t : Nat} {e : Event}

/-! ### The ledger of one event -/

/-- No event of the ledger's classes. -/
def dZero : Led := ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩
/-- One `bar.sync 0`. -/
def dBar0 : Led := ⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩
/-- One arrival on the named barrier. -/
def dBar8 : Led := ⟨0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩
/-- One matrix event. -/
def dMat : Led := ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩

/-- One successful poll of the mbarrier `b`. -/
def pollLed (b : Bar) : Led :=
  ⟨0, 0, if b = .state then 1 else 0, if b = .storeEmpty 0 then 1 else 0,
    if b = .storeEmpty 1 then 1 else 0, if b = .loadFull 0 then 1 else 0,
    if b = .loadFull 1 then 1 else 0, if b = .loadFull 2 then 1 else 0, 0, 0, 0, 0, 0, 0⟩

/-- One arrival on the mbarrier `b`. -/
def arrLed (b : Bar) : Led :=
  ⟨0, 0, 0, 0, 0, 0, 0, 0, if b = .storeFull 0 then 1 else 0, if b = .storeFull 1 then 1 else 0,
    if b = .loadEmpty 0 then 1 else 0, if b = .loadEmpty 1 then 1 else 0,
    if b = .loadEmpty 2 then 1 else 0, 0⟩

/-- Two mbarriers of a block are at one location only if they are the same mbarrier. -/
theorem loc_eq_iff {b b' : Bar} {c : Nat} : b.loc L c = b'.loc L c ↔ b = b' :=
  ⟨fun h => (Bar.loc_inj h).1, fun h => by rw [h]⟩

theorem ledEv_matrix {c : Nat} {op : MatrixOp} {own recv : List (Option Byte)}
    (hk : e.kind = .matrix op own recv) : ledEv L c e = dMat ∧ e.counts = true := by
  obtain ⟨pc, k⟩ := e
  simp only at hk
  subst hk
  exact ⟨rfl, rfl⟩

theorem ledEv_rd {c : Nat} {a : Acc} {bs : List (Option Byte)} (hk : e.kind = .rd a bs) :
    ledEv L c e = dZero ∧ e.counts = true := by
  obtain ⟨pc, k⟩ := e
  simp only at hk
  subst hk
  exact ⟨rfl, rfl⟩

theorem ledEv_wr {c : Nat} {a : Acc} {bs : List Byte} (hk : e.kind = .wr a bs) :
    ledEv L c e = dZero ∧ e.counts = true := by
  obtain ⟨pc, k⟩ := e
  simp only at hk
  subst hk
  exact ⟨rfl, rfl⟩

theorem ledEv_fence {c pc : Nat} {k : ProxyFence} {sc : Option MbarScope} :
    ledEv L c ⟨pc, .fenceProxy k sc⟩ = dZero := rfl

theorem ledEv_bar0 {c pc : Nat} : ledEv L c ⟨pc, .bar 0 none .sync⟩ = dBar0 := rfl

theorem ledEv_bar8 {c pc : Nat} : ledEv L c ⟨pc, .bar 8 (some 128) .sync⟩ = dBar8 := rfl

theorem ledEv_fail {c pc q : Nat} {m : Loc} {acq : Bool} {sc : MbarScope} :
    ledEv L c ⟨pc, .wait m q false acq sc⟩ = dZero := rfl

theorem ledEv_poll {c pc q : Nat} {b : Bar} {acq : Bool} {sc : MbarScope} :
    ledEv L c ⟨pc, .wait (b.loc L c) q true acq sc⟩ = pollLed b := by
  simp only [ledEv, pollLed, Execution.isBarId, okPoll, sourceWaitSuccess, arrivesOn,
    sourceArrive, isMatrix, loc_eq_iff, decide_eq_true_eq, Bool.false_eq_true, ↓reduceIte]

theorem ledEv_arrive {c pc tx n : Nat} {b : Bar} {rel : Bool} {sc : MbarScope} :
    ledEv L c ⟨pc, .arrive (b.loc L c) tx n rel sc⟩ = arrLed b := by
  simp only [ledEv, arrLed, Execution.isBarId, okPoll, sourceWaitSuccess, arrivesOn,
    sourceArrive, isMatrix, loc_eq_iff, decide_eq_true_eq, Bool.false_eq_true, ↓reduceIte]

/-! ### The ledger of a position along the steps -/

/-- Two ledgers with the same fourteen counts are equal. -/
theorem Led.ext' {a b : Led} (h0 : a.bar0 = b.bar0) (h1 : a.bar8 = b.bar8)
    (h2 : a.pollS = b.pollS) (h3 : a.pe0 = b.pe0) (h4 : a.pe1 = b.pe1) (h5 : a.pf0 = b.pf0)
    (h6 : a.pf1 = b.pf1) (h7 : a.pf2 = b.pf2) (h8 : a.af0 = b.af0) (h9 : a.af1 = b.af1)
    (h10 : a.ae0 = b.ae0) (h11 : a.ae1 = b.ae1) (h12 : a.ae2 = b.ae2) (h13 : a.mats = b.mats) :
    a = b := by
  cases a
  cases b
  simp only at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13
  subst h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13
  rfl

/-- An equation between ledgers of the form `ledAt`, count by count. -/
macro "led_eq" : tactic => `(tactic| (
  apply Led.ext' <;> simp only [ledAt, Led.add_def, uses, dBar0, dBar8, dMat, dZero] <;>
    (try omega)))

theorem pollLed_e0 : pollLed (.storeEmpty 0) = ⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩ := by
  decide
theorem pollLed_e1 : pollLed (.storeEmpty 1) = ⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩ := by
  decide
theorem pollLed_f0 : pollLed (.loadFull 0) = ⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0⟩ := by
  decide
theorem pollLed_f1 : pollLed (.loadFull 1) = ⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩ := by
  decide
theorem pollLed_f2 : pollLed (.loadFull 2) = ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩ := by
  decide
theorem arrLed_f0 : arrLed (.storeFull 0) = ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩ := by
  decide
theorem arrLed_f1 : arrLed (.storeFull 1) = ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩ := by
  decide
theorem arrLed_e0 : arrLed (.loadEmpty 0) = ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩ := by
  decide
theorem arrLed_e1 : arrLed (.loadEmpty 1) = ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩ := by
  decide
theorem arrLed_e2 : arrLed (.loadEmpty 2) = ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩ := by
  decide

/-- One more tile polled on the "empty" output mbarrier. -/
theorem ledAt_pollE (a b n c d m : Nat) :
    ledAt (a + 1) b n c d m = ledAt a b n c d m + pollLed (.storeEmpty (stage2 a)) := by
  obtain h0 | h1 : a % 2 = 0 ∨ a % 2 = 1 := by omega
  · rw [show stage2 a = 0 from Fin.ext h0, pollLed_e0]
    led_eq
  · rw [show stage2 a = 1 from Fin.ext h1, pollLed_e1]
    led_eq

/-- One more tile polled on the "full" input mbarrier. -/
theorem ledAt_pollF (a b n c d m : Nat) :
    ledAt a (b + 1) n c d m = ledAt a b n c d m + pollLed (.loadFull (stage3 b)) := by
  obtain h0 | h1 | h2 : b % 3 = 0 ∨ b % 3 = 1 ∨ b % 3 = 2 := by omega
  · rw [show stage3 b = 0 from Fin.ext h0, pollLed_f0]
    led_eq
  · rw [show stage3 b = 1 from Fin.ext h1, pollLed_f1]
    led_eq
  · rw [show stage3 b = 2 from Fin.ext h2, pollLed_f2]
    led_eq

/-- One more arrival on the "full" output mbarrier. -/
theorem ledAt_arrF (a b n c d m : Nat) :
    ledAt a b n (c + 1) d m = ledAt a b n c d m + arrLed (.storeFull (stage2 c)) := by
  obtain h0 | h1 : c % 2 = 0 ∨ c % 2 = 1 := by omega
  · rw [show stage2 c = 0 from Fin.ext h0, arrLed_f0]
    led_eq
  · rw [show stage2 c = 1 from Fin.ext h1, arrLed_f1]
    led_eq

/-- One more arrival on the "empty" input mbarrier. -/
theorem ledAt_arrE (a b n c d m : Nat) :
    ledAt a b n c (d + 1) m = ledAt a b n c d m + arrLed (.loadEmpty (stage3 d)) := by
  obtain h0 | h1 | h2 : d % 3 = 0 ∨ d % 3 = 1 ∨ d % 3 = 2 := by omega
  · rw [show stage3 d = 0 from Fin.ext h0, arrLed_e0]
    led_eq
  · rw [show stage3 d = 1 from Fin.ext h1, arrLed_e1]
    led_eq
  · rw [show stage3 d = 2 from Fin.ext h2, arrLed_e2]
    led_eq

theorem led_tile (t n : Nat) : led (.tile t n) =
    ledAt (t + ind 1 n) (t + ind 2 n) (t + ind 265 n) (t + ind 267 n) t (182 * t + matOf n) :=
  rfl

/-- **A straight step of a tile**: no poll, barrier or arrival; `m` matrix events (0 or 1). -/
theorem led_body {n m : Nat} (t : Nat) (h1 : ind 1 (n + 1) = ind 1 n)
    (h2 : ind 2 (n + 1) = ind 2 n) (h3 : ind 265 (n + 1) = ind 265 n)
    (h4 : ind 267 (n + 1) = ind 267 n) (hm : matOf (n + 1) = matOf n + m) :
    led (.tile t (n + 1)) = led (.tile t n) + ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, m⟩ := by
  simp only [led_tile, h1, h2, h3, h4, hm]
  led_eq

/-- From the entry to the first poll of tile 0. -/
theorem led_entry : led (.tile 0 0) = led .entry + dBar0 := by decide

/-- From the entry to the exit, for a sequence without tiles. -/
theorem led_entry_exit (hT : tilesOf P g = 0) : ledExit P g = led .entry + dBar0 := by
  rw [ledExit, hT]
  decide

/-- The first poll succeeds. -/
theorem led_pollE (t : Nat) :
    led (.tile t 1) = led (.tile t 0) + pollLed (.storeEmpty (stage2 t)) :=
  ledAt_pollE t t t t t (182 * t)

/-- The second poll succeeds. -/
theorem led_pollF (t : Nat) :
    led (.tile t 2) = led (.tile t 1) + pollLed (.loadFull (stage3 t)) :=
  ledAt_pollF (t + 1) t t t t (182 * t)

/-- The named barrier. -/
theorem led_bar8 (t : Nat) : led (.tile t 265) = led (.tile t 264) + dBar8 := by
  show ledAt (t + 1) (t + 1) (t + 1) t t (182 * t + 182) =
    ledAt (t + 1) (t + 1) t t t (182 * t + 182) + dBar8
  led_eq

/-- The proxy fence. -/
theorem led_fence (t : Nat) : led (.tile t 266) = led (.tile t 265) + dZero :=
  led_body t rfl rfl rfl rfl rfl

/-- The first arrival. -/
theorem led_arriveF (t : Nat) :
    led (.tile t 267) = led (.tile t 266) + arrLed (.storeFull (stage2 t)) :=
  ledAt_arrF (t + 1) (t + 1) (t + 1) t t (182 * t + 182)

/-- The second arrival, to the first poll of the next tile. -/
theorem led_arriveE (t : Nat) :
    led (.tile (t + 1) 0) = led (.tile t 267) + arrLed (.loadEmpty (stage3 t)) := by
  have h := ledAt_arrE (t + 1) (t + 1) (t + 1) (t + 1) t (182 * t + 182)
  have e : 182 * (t + 1) = 182 * t + 182 := by omega
  show ledAt (t + 1) (t + 1) (t + 1) (t + 1) (t + 1) (182 * (t + 1)) = _
  rw [e]
  exact h

/-- The second arrival of the last tile, to the exit. -/
theorem led_exit (hT : t + 1 = tilesOf P g) :
    ledExit P g = led (.tile t 267) + arrLed (.loadEmpty (stage3 t)) := by
  rw [← led_arriveE, ledExit, ← hT]
  rfl

/-! ### The counted events of a position along the steps -/

theorem idx_succ (t n : Nat) : (Pos.tile t (n + 1)).idx = (Pos.tile t n).idx + 1 := by
  simp only [Pos.idx]
  omega

theorem idx_next (t : Nat) : (Pos.tile (t + 1) 0).idx = (Pos.tile t 267).idx + 1 := by
  simp only [Pos.idx]
  omega

theorem idx_first : (Pos.tile 0 0).idx = Pos.entry.idx + 1 := rfl

end

end PTX.Kernels.FlashKdaFwd.Proof.Ref.Compute
