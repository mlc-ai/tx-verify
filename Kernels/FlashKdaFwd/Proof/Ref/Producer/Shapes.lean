-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Ref.Producer.Steps
public import Kernels.FlashKdaFwd.Proof.Ref.TensorLoad
public import Kernels.FlashKdaFwd.Proof.Ref.ParamBridge
public import Kernels.FlashKdaFwd.Flow.Code

@[expose] public section

/-! # The events of the Producer phase, in closed form

`Ev P L g pos e` says which event a thread fires at a position of the phase: kind, mbarrier,
parity, byte count, and for a tensor load the whole copy (`tileLoad`: tensor map, coordinates,
shared destination, completion mbarrier). `ev_bar`, `ev_poll`, `ev_arrive`, `ev_tile` prove it
for each class of instruction from the values of the operand registers; the events are *exact*:
none of these lemmas has an undefined-behaviour alternative or a hypothesis "the event is not
undefined behaviour", so they also say that the instruction's template is not undefined
behaviour at a state of the invariant.

* `stage t`: the input stage `t % 3` of tile `t`, as an index of the protocol layer's
  mbarriers (`emptyLoc L c (stage t)` is `(Bar.loadEmpty (stage t)).loc L c`).
* `coords P g t i`: the coordinates of the load at position `i` of tile `t`: for the values
  `v` (positions 0 to 15) the feature `8 i`, the tile's first token and the head; for the gate
  logits `beta` (16) the index `betaIdx`; for the workspace arrays the feature (or column), the
  row 0 and the workspace slot of the tile; for `g_total` (65) the feature 0 and the slot.
* `tileLoad P L g t i`: the copy of that load, `loadSpec` of `Ref/TensorLoad.lean` through the
  map of parameter object `mapFin i`, to byte `32768 + 18048 (t % 3) + (dstAbs i - 32768)` of the
  block's shared window, completing on the "full" mbarrier of stage `t % 3`.
* `ev_tile`: the event of the load at position `i` from its registers, by `tensorLoad_event`.
  The name equations of the parameter objects 0 to 7 are those of `Thread/ParamBridge.lean` and
  `Ref/ParamBridge.lean` (`mapName`).

The per-site lemmas that read the registers of the 210 load sites off the concrete state are
generated (`ShapesA.lean`, `ShapesB.lean`, `ShapesC.lean`). -/

namespace PTX.Kernels.FlashKdaFwd.Proof.Ref.Producer
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32
open PTX.Kernels.FlashKdaFwd PTX.Kernels.FlashKdaFwd.Proof.Thread
open PTX.Kernels.FlashKdaFwd.Proof.Ref PTX.Kernels.FlashKdaFwd.Recurrence
open PTX.Kernels.FlashKdaFwd.Proof.Ref.Startup (cu ft)
open PTX.Kernels.FlashKdaFwd.Protocol (Bar)

noncomputable section
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxRecDepth 4000

/-! ### The closed forms -/

/-- The input stage of tile `t`. -/
def stage (t : Nat) : Fin 3 := ⟨t % 3, Nat.mod_lt _ (by decide)⟩

/-- The parameter object of the tensor map of the load at position `i`. -/
def mapFin (i : Nat) : Fin 11 := ⟨mapOf i % 11, Nat.mod_lt _ (by decide)⟩

/-- The workspace slot of tile `t` of the block of thread `g`. -/
def slotOf (P : Params) (g t : Nat) : Nat :=
  P.totalTiles * headOf P g + ft P (seqOf P g) + t

/-- **The coordinates of the load at position `i` of tile `t`.** -/
def coords (P : Params) (g t i : Nat) : List Nat :=
  if i < 16 then [c0Tab i, cu P (seqOf P g) + 16 * t, headOf P g]
  else if i = 16 then [betaIdx P g t]
  else if i = 65 then [0, slotOf P g t]
  else [c0Tab i, 0, slotOf P g t]

/-- **The copy of the load at position `i` of tile `t`** of the block of thread `g`. -/
def tileLoad (P : Params) (L : Launch) (g t i : Nat) : TensorCopy.Spec :=
  loadSpec P (g / L.block) (mapFin i) (coords P g t i)
    (P.sharedBase + 18048 * (t % 3) + dstAbs i) (P.sharedBase + 98304 + 8 * (t % 3))

/-- **The event of a position**, in closed form. -/
def Ev (P : Params) (L : Launch) (g : Nat) : Pos → Event → Prop
  | .entry, e => e = ⟨1402, .bar 0 none .sync⟩
  | .poll c u, e => ∃ ok, e = ⟨(Pos.poll c u).site.pc,
      .wait (emptyLoc L (g / L.block) (stage (tile c u))) (par (tile c u)) ok true .cta⟩
  | .arrive c u, e => e = ⟨(Pos.arrive c u).site.pc,
      .arrive (fullLoc L (g / L.block) (stage (tile c u))) 17984 1 true .cta⟩
  | .load c u i, e => e = ⟨(Pos.load c u i).site.pc,
      .tensorIssue (P.objectBase (mapFin i.val)) (tileLoad P L g (tile c u) i.val)⟩
  | .tail j, e => ∃ ok, e = ⟨(Pos.tail j).site.pc,
      .wait (emptyLoc L (g / L.block) (stage (tilesOf P g + j.val)))
        (par (tilesOf P g + j.val)) ok true .cta⟩

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}
  {w : Nat → BitVec 64} {p : Nat → Bool} {x : Nat → Value}
  {t : TState} {ins : Instr} {e : Event} {o : Option TState}

/-! ### Mbarrier events -/

/-- No assumption of the kernel widens the scope of an mbarrier instruction. -/
theorem noWiden (pc : Nat) : Assumptions.all.any (·.clusterScopeMbar pc) = false := rfl

/-- The address register of the "empty" mbarrier of a stage names the mbarrier. -/
theorem emptyOk (hpre : Pre P L mem0) {r tt : Nat}
    (hr : t.regs r = some (.bits 32 (W (P.sharedBase + 98328 + 8 * (tt % 3))))) :
    mbarLoc L g t r 0 = .ok (emptyLoc L (g / L.block) (stage tt)) := by
  have hs := shared_lt hpre
  have ha := hpre.sharedAlignment
  have h3 : tt % 3 < 3 := Nat.mod_lt _ (by decide)
  rw [mbarLoc_b32 hr (by omega) (by omega)]
  simp only [emptyLoc, Bar.loc, Bar.off, stage, hpre.sharedBase, Nat.add_assoc]

/-- The address register of the "full" mbarrier of a stage names the mbarrier. -/
theorem fullOk (hpre : Pre P L mem0) {r tt : Nat}
    (hr : t.regs r = some (.bits 32 (W (P.sharedBase + 98304 + 8 * (tt % 3))))) :
    mbarLoc L g t r 0 = .ok (fullLoc L (g / L.block) (stage tt)) := by
  have hs := shared_lt hpre
  have ha := hpre.sharedAlignment
  have h3 : tt % 3 < 3 := Nat.mod_lt _ (by decide)
  rw [mbarLoc_b32 hr (by omega) (by omega)]
  simp only [fullLoc, Bar.loc, Bar.off, stage, hpre.sharedBase, Nat.add_assoc]

/-- The "full" mbarrier of a stage as the completion mbarrier of a copy. -/
theorem fullLoc_eq (hpre : Pre P L mem0) (c tt : Nat) :
    (⟨.shared, c, P.sharedBase + 98304 + 8 * (tt % 3)⟩ : Loc) = fullLoc L c (stage tt) := by
  simp only [fullLoc, Bar.loc, Bar.off, stage, hpre.sharedBase, Nat.add_assoc]

/-- The parity a poll records is the parity register's low bit. -/
theorem par_toNat (tt : Nat) : (W (par tt)).toNat % 2 = par tt := by
  have h := par_lt tt
  rw [toNat_W (by omega)]
  omega

/-- **A poll** whose address register holds the "empty" mbarrier of the stage of tile `tt` and
whose parity register holds `par tt`. -/
theorem ev_poll (hpre : Pre P L mem0) {pc pr r q tt : Nat}
    (hf : Fires pc (eventTmpl Assumptions.all L g t (.mbarWait pr r 0 (.reg q) true .cta)) e o)
    (hr : t.regs r = some (.bits 32 (W (P.sharedBase + 98328 + 8 * (tt % 3)))))
    (hq : t.regs q = some (.bits 32 (W (par tt)))) :
    ∃ ok, e = ⟨pc, .wait (emptyLoc L (g / L.block) (stage tt)) (par tt) ok true .cta⟩ := by
  have h := par_lt tt
  exact shape_wait (P := fun e' => ∃ ok, e' =
      ⟨pc, .wait (emptyLoc L (g / L.block) (stage tt)) (par tt) ok true .cta⟩) hf (noWiden _)
    (readBits_b32 hq (by omega)) (emptyOk hpre hr) (fun ok => ⟨ok, by rw [par_toNat]⟩)

/-- **An arrival** whose address register holds the "full" mbarrier of the stage of tile `tt`
and whose byte-count register holds 17984. -/
theorem ev_arrive (hpre : Pre P L mem0) {pc r q tt : Nat}
    (hf : Fires pc (eventTmpl Assumptions.all L g t
      (.mbarArrive r 0 (.reg q) (.imm 1) false true .cta none)) e o)
    (hr : t.regs r = some (.bits 32 (W (P.sharedBase + 98304 + 8 * (tt % 3)))))
    (hq : t.regs q = some (.bits 32 (W 17984))) :
    e = ⟨pc, .arrive (fullLoc L (g / L.block) (stage tt)) 17984 1 true .cta⟩ :=
  shape_arrive (P := fun e' => e' = _) hf (noWiden _) (readBits_b32 hq (by decide)) rfl
    (fullOk hpre hr) rfl

/-! ### Tensor loads -/

/-- The name equations of the parameter objects of the eight tensor maps of the tile loads. -/
theorem mapName (i : Nat) (hi : i < 70) :
    paramName (mapFin i).val = param (objName (mapFin i)) := by
  have h : ∀ k : Fin 11, k.val < 8 → paramName k.val = param (objName k) := by
    intro k hk
    fin_cases k
    · exact Thread.paramName_0
    · exact Ref.paramName_1
    · exact Ref.paramName_2
    · exact Ref.paramName_3
    · exact Ref.paramName_4
    · exact Ref.paramName_5
    · exact Ref.paramName_6
    · exact Ref.paramName_7
    all_goals (exfalso; revert hk; decide)
  refine h (mapFin i) ?_
  interval_cases i <;> decide

/-- A destination offset is a multiple of 128 inside the input buffer. -/
theorem dstAbs_ok (i : Nat) (hi : i < 70) : dstAbs i % 128 = 0 ∧ dstAbs i ≤ 50560 := by
  interval_cases i <;> decide

theorem c0Tab_le (i : Nat) (hi : i < 70) : c0Tab i ≤ 120 ∧ c0Tab i % 8 = 0 := by
  interval_cases i <;> decide

/-- A load has as many coordinates as its map has dimensions. -/
theorem coords_len (P : Params) (g tt : Nat) (i : Nat) (hi : i < 70) :
    (coords P g tt i).length = (preMap P (mapFin i)).1 + 1 := by
  interval_cases i <;> rfl

/-- The coordinates of a load of a tile of the block fit 31 bits. -/
theorem coords_lt (hpre : Pre P L mem0) (hg : g < L.threads) {tt : Nat}
    (ht : tt < tilesOf P g) (i : Nat) (hi : i < 70) : ∀ v ∈ coords P g tt i, v < 2 ^ 31 := by
  have h1 := token_lt hpre ht
  have h2 := Startup.total_lt hpre
  have h3 := headOf_lt hpre hg
  have h4 := hpre.headsLt
  have h5 := slot_lt hpre hg ht
  have h6 := hpre.slotsRange
  have h7 := beta_lt hpre hg ht
  have h8 := hpre.headTokensRange
  have h9 := (c0Tab_le i hi).1
  intro v hv
  simp only [coords, slotOf, betaIdx] at hv
  split_ifs at hv <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at hv <;>
    rcases hv with rfl | rfl | rfl <;> omega

/-- The element size of the map of the load at position `i`: 4 bytes for `g_total`, else 2. -/
theorem fmtBytes (P : Params) (i : Nat) (hi : i < 70) :
    (preMap P (mapFin i)).2.format.bytes = if i = 65 then 4 else 2 := by
  interval_cases i <;> rfl

/-- The first coordinate of the load at position `i`. -/
theorem coords_first (P : Params) (g tt i : Nat) :
    (coords P g tt i).getD 0 0 =
      if i < 16 then c0Tab i else if i = 16 then betaIdx P g tt else if i = 65 then 0
      else c0Tab i := by
  unfold coords
  split_ifs <;> rfl

/-- The box of a load starts at a 16-byte boundary of its tensor. -/
theorem coords_box (P : Params) (g tt : Nat) (i : Nat) (hi : i < 70) :
    (coords P g tt i).getD 0 0 * (preMap P (mapFin i)).2.format.bytes % 16 = 0 := by
  have hb : betaIdx P g tt % 8 = 0 := by
    simp only [betaIdx]
    omega
  have hc := (c0Tab_le i hi).2
  rw [fmtBytes P i hi, coords_first]
  split_ifs <;> omega

/-- Register facts with the bounds of their values. -/
theorem forall₂_and {α β : Type} {R : α → β → Prop} {Q : β → Prop} {l₁ : List α} {l₂ : List β}
    (h : List.Forall₂ R l₁ l₂) (hq : ∀ v ∈ l₂, Q v) :
    List.Forall₂ (fun r v => R r v ∧ Q v) l₁ l₂ := by
  induction h with
  | nil => exact .nil
  | cons hrv _ ih =>
    exact .cons ⟨hrv, hq _ List.mem_cons_self⟩ (ih fun v hv => hq v (List.mem_cons_of_mem _ hv))

/-- **The tensor load at position `i` of tile `tt`**, from its registers: the destination
register `dst`, the map register `rm`, the coordinate registers `rs`, the mbarrier register `mb`
and the policy register `pol`. -/
theorem ev_tile (hpre : Pre P L mem0) (hg : g < L.threads) {i : Nat} (hi : i < 70) {tt : Nat}
    (ht : tt < tilesOf P g) {pc dst rm mb pol : Nat} {rs : List Nat} {y : BitVec 64}
    (hf : Fires pc (eventTmpl Assumptions.all L g t
      (.cpTensor true false dst 0 (.reg rm) (rs.map Opnd.reg) mb 0 none .tile (some (.reg pol))))
      e o)
    (hrm : t.regs rm = some (.ptr 64 true (.param (paramName (mapFin i).val)) 0))
    (hdst : t.regs dst = some (.bits 32 (W (P.sharedBase + 18048 * (tt % 3) + dstAbs i))))
    (hmb : t.regs mb = some (.bits 32 (W (P.sharedBase + 98304 + 8 * (tt % 3)))))
    (hpol : t.regs pol = some (.bits 64 y))
    (hcs : List.Forall₂ (fun r v => t.regs r = some (.bits 32 (W v))) rs (coords P g tt i)) :
    e = ⟨pc, .tensorIssue (P.objectBase (mapFin i)) (tileLoad P L g tt i)⟩ := by
  have hs := shared_lt hpre
  have ha := hpre.sharedAlignment
  have h3 : tt % 3 < 3 := Nat.mod_lt _ (by decide)
  obtain ⟨hd1, hd2⟩ := dstAbs_ok i hi
  exact (tensorLoad_event hpre hg (mapName i hi) hf hrm hdst (by omega) (by omega) hmb (by omega)
    (by omega) hpol (forall₂_and hcs (coords_lt hpre hg ht i hi))
    (hcs.length_eq.trans (coords_len P g tt i hi)) (coords_box P g tt i hi)).1

end

end PTX.Kernels.FlashKdaFwd.Proof.Ref.Producer
