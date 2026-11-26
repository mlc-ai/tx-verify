-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Ref.Compute.Arith

@[expose] public section

/-! # Tools for the steps of the Compute phase

A step of the phase's invariant goes from position `n` of a tile to position `n + 1`: the
transition function of the thread machine rewrites some registers (`setW l w`) and the facts of
the new position are those of the old one plus the closed forms of the registers written. This
file has the parts of such a step that do not depend on the position.

* `Regs.frame`: the facts of a list of registers survive a rewriting of other registers; the
  side condition is a check on two lists of register ids (closed, so `decide` proves it).
* `Tile.step`: a step that writes registers; `Tile.same`: a step that writes none.
* `Regs.one`, `Regs.cons`, `Regs.nil`: the facts of the registers written, one by one.
* `addi_step`: the most frequent assignment, `add.s32 r, base, constant` on a base register
  with a fact.
* `regVal_le`: every closed form of the table but the loop counter's is at most 10,000,000
  (the bound that the 32-bit additions need).
* The forms of the successor function at the sites of the phase, and what a successor that is
  a state says about the event and the next state (`mxNext_some`, `rowNext_some`, …). The
  equations `next L g ⟨site, w, p, x⟩ e = <form>` are the generated `Thread.next_<site>`; the
  forms here are the same `match` expressions, stated once with the site's part as a
  parameter, so that one inversion lemma serves a family of sites. -/

namespace PTX.Kernels.FlashKdaFwd.Proof.Ref.Compute
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32
open PTX.Kernels.FlashKdaFwd PTX.Kernels.FlashKdaFwd.Proof.Thread
open PTX.Kernels.FlashKdaFwd.Proof.Ref PTX.Kernels.FlashKdaFwd.Recurrence

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {g t : Nat}

/-! ### Register facts across a rewriting -/

/-- A register that the list `l` does not name is not rewritten. -/
theorem setW_of_not_mem {l : List (Nat × BitVec 64)} {w : Nat → BitVec 64} {r : Nat}
    (h : (l.map Prod.fst).contains r = false) : setW l w r = w r := by
  have hl : l.lookup r = none := by
    rw [List.lookup_eq_none_iff]
    intro a ha
    have hm : a.1 ∈ l.map Prod.fst := List.mem_map.mpr ⟨a, ha, rfl⟩
    have hne : r ≠ a.1 := by
      rintro rfl
      have hc : (l.map Prod.fst).contains a.1 = true := List.contains_iff_mem.mpr hm
      rw [h] at hc
      cases hc
    simpa using hne
  simp [setW, hl]

theorem Regs.nil {val : Nat → Nat} {w : Nat → BitVec 64} : Regs [] val w :=
  fun _ h => absurd h List.not_mem_nil

theorem Regs.cons {val : Nat → Nat} {w : Nat → BitVec 64} {r : Nat} {keys : List Nat}
    (h : w r = W (val r)) (hk : Regs keys val w) : Regs (r :: keys) val w := by
  intro q hq
  rcases List.mem_cons.mp hq with rfl | hq
  · exact h
  · exact hk q hq

theorem Regs.one {val : Nat → Nat} {w : Nat → BitVec 64} {r : Nat} (h : w r = W (val r)) :
    Regs [r] val w := Regs.cons h Regs.nil

theorem Regs.append {val : Nat → Nat} {w : Nat → BitVec 64} {a b : List Nat}
    (ha : Regs a val w) (hb : Regs b val w) : Regs (a ++ b) val w := by
  intro q hq
  rcases List.mem_append.mp hq with h | h
  · exact ha q h
  · exact hb q h

/-- **The facts of the registers `keys` survive a rewriting of other registers.** -/
theorem Regs.frame {keys : List Nat} {val : Nat → Nat} {w : Nat → BitVec 64}
    (h : Regs keys val w) {l : List (Nat × BitVec 64)} {lk : List Nat}
    (hlk : l.map Prod.fst = lk) (hd : keys.all (fun r => !lk.contains r) = true) :
    Regs keys val (setW l w) := by
  intro r hr
  have h1 := List.all_eq_true.mp hd r hr
  rw [setW_of_not_mem (by rw [hlk]; simpa using h1)]
  exact h r hr

/-- A prefix of a list is a shorter prefix followed by the rest. -/
theorem take_split {α : Type} (l : List α) {k k' : Nat} (h : k ≤ k') :
    l.take k' = l.take k ++ (l.take k').drop k := by
  have h1 : (l.take k').take k = l.take k := by rw [List.take_take, Nat.min_eq_left h]
  rw [← h1, List.take_append_drop]

/-- **A step inside a tile that rewrites the registers `l`**: the old facts are kept (the
registers assigned so far are not among the ones written: `hd`) and the registers that become
known hold their closed forms (`hnew`). The step starts after the first poll (`hn`) and ends
before the last position (`hn'`). -/
theorem Tile.step {n n' : Nat} {w : Nat → BitVec 64} {p : Nat → Bool} {x x' : Nat → Value}
    (h : Tile P L g t n w p x) {l : List (Nat × BitVec 64)} {lk : List Nat}
    (hlk : l.map Prod.fst = lk) (hn : 1 ≤ n) (hn' : n' < 267) (hc : cntOf n ≤ cntOf n')
    (hd : (regKeys.take (cntOf n)).all (fun r => !lk.contains r) = true)
    (hnew : Regs ((regKeys.take (cntOf n')).drop (cntOf n)) (regVal P g t) (setW l w)) :
    Tile P L g t n' (setW l w) p x' where
  compute := h.compute
  lt := h.lt
  pos := by omega
  regs := by
    rw [take_split regKeys hc]
    exact (h.regs.frame hlk hd).append hnew
  p71 := h.p71
  p73 := h.p73
  p72 := fun _ => h.p72 hn
  rem := fun h267 => by omega

/-- **A step inside a tile that rewrites no register.** -/
theorem Tile.same {n n' : Nat} {w : Nat → BitVec 64} {p : Nat → Bool} {x x' : Nat → Value}
    (h : Tile P L g t n w p x) (hn : 1 ≤ n) (hn' : n' < 267) (hc : cntOf n' = cntOf n) :
    Tile P L g t n' w p x' where
  compute := h.compute
  lt := h.lt
  pos := by omega
  regs := by rw [hc]; exact h.regs
  p71 := h.p71
  p73 := h.p73
  p72 := fun _ => h.p72 hn
  rem := fun h267 => by omega

/-! ### Closed forms -/

/-- **Every closed form of the table, but the loop counter's, is at most 10,000,000.** -/
theorem regVal_le (hpre : Pre P L mem0) (hc : tid g < 128) {r : Nat} (hr : r ∈ regKeys)
    (h6 : r ≠ 2106) : regVal P g t r ≤ 10000000 := by
  have hs := shared_lt hpre
  have h1 := laneOff_le g
  have h2 := warpOff_le hc
  have h3 := accOff_le hc
  have h4 := krOff_le g
  have h5 := gtOff_le g
  have h7 := gateOff_le P g
  have h8 := pairOff_le g
  have h9 : tid g / 32 ≤ 3 := by omega
  simp only [regKeys, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact absurd rfl h6
    | (show (if lane g = 0 then 1 else 0) ≤ 10000000; split <;> omega)
    | (simp only [regVal, regTab, List.lookup, Nat.reduceBEq, Option.getD_some]; omega)

/-- **`add.s32 r, base, c`** on a base register that holds the word of a small number. -/
theorem addi_step {w : Nat → BitVec 64} {R a c : Nat} (hR : w R = W a) (ha : a ≤ 10000000)
    (hc : c ≤ 10000000) : addi (w R) (c : Int) = W (a + c) := by
  rw [hR]
  exact addi_W (by omega) (by omega)

/-! ### The forms of the successor function -/

variable {e : Event} {d' : D}

/-- The successor after a warp matrix event that returns `n` 32-bit registers: `f vs` for the
values `vs` received (dead on anything else). -/
def mxNext (n : Nat) (e : Event) (f : List Value → Option (Option D)) : Option (Option D) :=
  match e.kind with
  | .matrix _ _ recv =>
    match matrixVals 32 n recv with
    | .ok vs => f vs
    | .error _ => none
  | _ => none

theorem mxNext_some {n : Nat} {f : List Value → Option (Option D)}
    (h : mxNext n e f = some (some d')) :
    ∃ op own recv vs, e.kind = .matrix op own recv ∧ f vs = some (some d') := by
  unfold mxNext at h
  split at h
  · rename_i op own recv hk
    split at h
    · rename_i vs hv
      exact ⟨op, own, recv, vs, hk, h⟩
    · cases h
  · cases h

/-- The successor after the row read of an `ldmatrix` or after a scalar load: `f bs` for the
bytes read. -/
def rdNext (e : Event) (f : List (Option Byte) → Option (Option D)) : Option (Option D) :=
  match e.kind with
  | .rd _ bs => f bs
  | _ => none

theorem rdNext_some {f : List (Option Byte) → Option (Option D)}
    (h : rdNext e f = some (some d')) : ∃ a bs, e.kind = .rd a bs ∧ f bs = some (some d') := by
  unfold rdNext at h
  split at h
  · rename_i a bs hk
    exact ⟨a, bs, hk, h⟩
  · cases h

/-- The successor after the matrix event of an `stmatrix`: `f recv` for the bytes received. -/
def stNext (e : Event) (f : List (Option Byte) → Option (Option D)) : Option (Option D) :=
  match e.kind with
  | .matrix _ _ recv => f recv
  | _ => none

theorem stNext_some {f : List (Option Byte) → Option (Option D)}
    (h : stNext e f = some (some d')) :
    ∃ op own recv, e.kind = .matrix op own recv ∧ f recv = some (some d') := by
  unfold stNext at h
  split at h
  · rename_i op own recv hk
    exact ⟨op, own, recv, hk, h⟩
  · cases h

/-- The successor after the row write of an `stmatrix`. -/
def wrNext (e : Event) (o : Option (Option D)) : Option (Option D) :=
  match e.kind with
  | .wr _ _ => o
  | _ => none

theorem wrNext_some {o : Option (Option D)} (h : wrNext e o = some (some d')) :
    ∃ a bs, e.kind = .wr a bs ∧ o = some (some d') := by
  unfold wrNext at h
  split at h
  · rename_i a bs hk
    exact ⟨a, bs, hk, h⟩
  · cases h

/-- A successor across a data run that is a state is the state behind the run. -/
theorem across_some {C : Prop} {d : D} (h : across C d = some (some d')) : d' = d := by
  unfold across at h
  split at h
  · exact (Option.some.inj (Option.some.inj h)).symm
  · cases h

/-- The state after the row read of an `ldmatrix`, when it is a state. -/
theorem ldRow_some {d : D} {bs : List (Option Byte)} {s : List (Option Byte) → Site}
    (h : ldRow d bs s = some (some d')) : d' = ⟨s bs, d.w, d.p, d.x⟩ := by
  unfold ldRow at h
  split at h
  · exact (Option.some.inj (Option.some.inj h)).symm
  · cases h

/-- The state after the matrix event of an `stmatrix`, when it is a state. -/
theorem stRecv_some {d : D} {recv : List (Option Byte)} {s : List (Option Byte) → Site}
    (h : stRecv d recv s = some (some d')) : d' = ⟨s recv, d.w, d.p, d.x⟩ := by
  unfold stRecv at h
  split at h
  · exact (Option.some.inj (Option.some.inj h)).symm
  · cases h

end

end PTX.Kernels.FlashKdaFwd.Proof.Ref.Compute
