-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.DequantLane
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.FollowHead
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.FollowSub
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.MmaLane
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Roles
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.TmaLane
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.View
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Wg0Lane
public import Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.Measure
public import Kernels.FlashMlaSparseDecodeH64.Proof.Index.Measure
public import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Measure
public import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.RefCount
public import Kernels.FlashMlaSparseDecodeH64.Proof.Startup.Measure
public import Kernels.FlashMlaSparseDecodeH64.Proof.Tma.Measure
public import Kernels.FlashMlaSparseDecodeH64.Proof.Tma.RefCount
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Measure
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg1.Measure

@[expose] public section

/-! # The measure along a followed thread

Every step of a followed thread from a state before an event that is no undefined behaviour keeps
the glued measure (`Common/Measure.lean`) and every counted event raises it (`measure_raise`):
the startup and warpgroup 1's head and idle code raise their measures at every step, the
warpgroup-1 dispatch and the startup's exit enter a fragment above the state's slot, an MMA or
TMA lane that lost its election returns to the idle code above the MMA and TMA codes, and inside
a role the role's `measure_step` (a failed poll does not count) applies with the role's reference
invariant at both states: the role table's invariant (the thread is followed at both events), with
no undefined behaviour counted, globally (`state_ub`) and in the role's own class (the lanes'
`take_noUb`; the event is none). The index warp's measure is invariant-free (`Index.bplace`). -/

/-! # The termination measure of the thread machine

The glued measure, assembled from the roles' measures: the startup's (`Startup.measure`, at most
`34`), every warpgroup's state above it (from `fragBase`); in warpgroup 1 the head
(`Wg1.measure`, at most `2`), its sub-roles above it, and the idle code above the MMA and TMA
codes (a lane of warp 4 or 5 that lost its election enters it from them). Every role's slot
(`wg0Measure`, `dequantMeasure`, `mmaMeasure`, `tmaMeasure`, `indexMeasure`) holds its lane's
measure; `subTop` is the MMA and TMA codes' top. Every state's measure is at most `top`
(`measure_le`); along a followed thread every step keeps it and every counted event raises it
(`Common/Bound.lean`), so a thread's counted events are at most `top + 2`
(`Common/Export/Bound.lean`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

/-- The first measure of the warpgroups' states: above every startup state. -/
def fragBase : Nat := 35

/-! ### The slots -/

/-- **Slot `Wg0`**: warpgroup 0's place capped at its top (`Wg0/Measure.lean`). -/
def wg0Measure (P : Params) (L : Launch) (g : Nat) :
    (wg0Code P L g (warpW L g)).D → (Cls → Nat) → Nat :=
  fun d _ => Wg0.measure d

/-- **Slot `Dequant`**: warpgroup 2's place capped at its top (`Dequant/Measure.lean`). -/
def dequantMeasure (P : Params) (L : Launch) (g : Nat) :
    (dequantCode P L g (warpW L g)).D → (Cls → Nat) → Nat :=
  fun d _ => Dequant.measure d

/-- **Slot `Mma`**. -/
def mmaMeasure (P : Params) (L : Launch) (g : Nat) : (mmaCode P L g).D → (Cls → Nat) → Nat :=
  fun d _ => Mma.measure d

/-- **Slot `Tma`**: the TMA warp's place capped at its top (`Tma/Measure.lean`). -/
def tmaMeasure (P : Params) (L : Launch) (g : Nat) : (tmaCode P L g).D → (Cls → Nat) → Nat :=
  fun d _ => Tma.measure d

/-- **Slot `Index`**: the index warp's bound place, its loops ranked by their counters
(`Index/Measure.lean`, `Index.bplace`). -/
def indexMeasure (P : Params) (L : Launch) (g : Nat) : (indexCode P L g).D → (Cls → Nat) → Nat :=
  fun d _ => Index.bplace d

/-- The largest measure of the MMA and TMA codes (the lanes B and T raise it). -/
def subTop : Nat := max Mma.top Tma.top

/-- **Slot `Wg1`**: the head below its sub-roles, the idle code above the MMA and TMA codes. -/
def wg1Measure (P : Params) (L : Launch) (g : Nat) : (wg1Code P L g).D → (Cls → Nat) → Nat
  | .inl s, _ => Wg1.measure s
  | .inr ⟨.inl .mma, d⟩, n => 3 + mmaMeasure P L g d n
  | .inr ⟨.inl .tma, d⟩, n => 3 + tmaMeasure P L g d n
  | .inr ⟨.inl .index, d⟩, n => 3 + indexMeasure P L g d n
  | .inr ⟨.inl .idle, s⟩, _ => 4 + subTop + Wg1.imeasure s
  | .inr ⟨.inr _, _⟩, _ => 3

/-! ### The measure -/

/-- The measure of each warpgroup's state. -/
def fragMeasure (P : Params) (L : Launch) (g : Nat) :
    (i : Entry) → (frag P L g i).D → (Cls → Nat) → Nat
  | .wg0 => wg0Measure P L g
  | .wg1 => wg1Measure P L g
  | .dequant => dequantMeasure P L g

/-- **The measure of a state of the thread machine**; a stub's is `fragBase`. -/
def measure (P : Params) (L : Launch) (g : Nat) : (thread P L g).D → Nat
  | (.inl d, _) => Startup.measure d
  | (.inr ⟨.inl i, d⟩, n) => fragBase + fragMeasure P L g i d n
  | (.inr ⟨.inr _, _⟩, _) => fragBase

/-- **The largest measure.** -/
def top : Nat :=
  fragBase + (Wg0.top + Dequant.top + (4 + subTop + 3) + (3 + Index.btop))

/-- **Every state's measure is at most `top`.** -/
theorem measure_le (P : Params) (L : Launch) (g : Nat) (σ : (thread P L g).D) :
    measure P L g σ ≤ top := by
  have h0 := Wg0.measure_le
  have h1 := Dequant.measure_le
  have h2 := Mma.measure_le
  have h3 := Tma.measure_le
  have h4 := Index.bplace_le
  have h5 := Wg1.time_le
  have h6 := Wg1.itime_le
  have hm : Mma.top ≤ subTop := Nat.le_max_left _ _
  have ht : Tma.top ≤ subTop := Nat.le_max_right _ _
  obtain ⟨s, n⟩ := σ
  rcases s with d | ⟨i | r, d⟩
  · have := Startup.measure_le d
    simp only [measure, top, fragBase]
    omega
  · cases i with
    | wg0 => have := h0 d; simp only [measure, fragMeasure, wg0Measure, top]; omega
    | dequant => have := h1 d; simp only [measure, fragMeasure, dequantMeasure, top]; omega
    | wg1 =>
      rcases d with s | ⟨j | r, d⟩
      · have := h5 s; simp only [measure, fragMeasure, wg1Measure, Wg1.measure, top]; omega
      · cases j with
        | mma => have := h2 d; simp only [measure, fragMeasure, wg1Measure, mmaMeasure, top]; omega
        | tma => have := h3 d; simp only [measure, fragMeasure, wg1Measure, tmaMeasure, top]; omega
        | index =>
          have := h4 d; simp only [measure, fragMeasure, wg1Measure, indexMeasure, top]; omega
        | idle =>
          have := h6 d; simp only [measure, fragMeasure, wg1Measure, Wg1.imeasure, top]; omega
      · simp only [measure, fragMeasure, wg1Measure, top]; omega
  · simp only [measure, top]; omega

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- The measure keeps from `a` to `b`, and a counted event `e` raises it. -/
def Raise (a b : Nat) (e : Event) : Prop := a ≤ b ∧ (e.counts = true → a < b)

theorem Raise.of_lt {a b : Nat} {e : Event} (h : a < b) : Raise a b e :=
  ⟨Nat.le_of_lt h, fun _ => h⟩

theorem Raise.add {a b : Nat} {e : Event} (c : Nat) (h : Raise a b e) : Raise (c + a) (c + b) e :=
  ⟨Nat.add_le_add_left h.1 c, fun hc => Nat.add_lt_add_left (h.2 hc) c⟩

theorem map_some {α β : Type} {o : Option (Option α)} {f : α → β} {b : β}
    (h : o.map (Option.map f) = some (some b)) : ∃ a, o = some (some a) ∧ f a = b := by
  rcases o with _ | _ | a
  · cases h
  · cases h
  · simp only [Option.map_some, Option.some.injEq] at h
    exact ⟨a, rfl, h⟩

/-- A class the event is not in keeps its count. -/
theorem bump_keep {n : Cls → Nat} {e : Event} {c : Cls} (h : cls c e = false) :
    Code.bump cls n e c = n c := by
  simp [Code.bump, h]

theorem cls_ub {e : Event} (hu : ∀ f, e.kind ≠ .ub f) : cls .ub e = false := by
  show (match e.kind with | .ub _ => true | _ => false) = false
  split
  next f hf => exact absurd hf (hu f)
  next => rfl

theorem wg0_ub {e : Event} (hu : ∀ f, e.kind ≠ .ub f) : cls (.wg0 .ub) e = false := by
  have hk : Wg0.kindOf e ≠ some .ub := by unfold Wg0.kindOf; split <;> simp_all
  simp [cls, Wg0.cls, hk]

theorem dequant_ub {e : Event} (hu : ∀ f, e.kind ≠ .ub f) : cls (.dequant .ub) e = false := by
  have hk : Dequant.kindOf e ≠ some .ub := by unfold Dequant.kindOf; split <;> simp_all
  simp [cls, Dequant.cls, hk]

/-- A sub-role's state `d` of a lane that lost its election (MMA or TMA) returns to the idle code
above it, or (out of the idle gate) to a stub, which no followed state is. -/
theorem back_raise {e : Event} {j : SubEntry} {d : (subFrag P L g j).D} {d' : (subFrag P L g j).D}
    {n n' : Cls → Nat} {p : (wg1HeadCode P L g).D} (hx : wg1Measure P L g (.inr ⟨.inl j, d⟩) n ≤
      3 + subTop) (hb : subBack P L g j d' = some p)
    (hJ' : (table P L).J g (.inr ⟨.inl .wg1, Code.enter (wg1HeadCode P L g)
      (Code.withStubsAt (subFrag P L g) (SubEntry.pc P L g))
      (Code.gatedExit (wg1Enter P L g) (subSel P L g)) p⟩, n')) :
    Raise (measure P L g (.inr ⟨.inl .wg1, .inr ⟨.inl j, d⟩⟩, n))
      (measure P L g (.inr ⟨.inl .wg1, Code.enter (wg1HeadCode P L g)
        (Code.withStubsAt (subFrag P L g) (SubEntry.pc P L g))
        (Code.gatedExit (wg1Enter P L g) (subSel P L g)) p⟩, n')) e := by
  have hp : p = Wg1.Site.idle := by
    cases j <;> simp only [subBack, reduceCtorEq] at hb <;> split_ifs at hb <;>
      exact (Option.some.inj hb).symm
  subst hp
  cases ho : subOk L g .idle
  · simp only [Code.enter, Code.gatedExit, wg1Enter, Wg1.exitOf, subSel, ho, Option.map_some,
      Bool.false_eq_true, ↓reduceIte] at hJ'
    obtain ⟨-, hF, -⟩ := hJ'
    exact hF.elim
  · refine Raise.add fragBase (Raise.of_lt ?_)
    simp only [Code.enter, Code.gatedExit, wg1Enter, Wg1.exitOf, subSel, ho, Option.map_some,
      ↓reduceIte]
    exact Nat.lt_of_le_of_lt hx
      (show 3 + subTop < 4 + subTop + Wg1.imeasure (idleFirst P L g) by omega)

/-- **Every step of a followed thread keeps the measure, and a counted event raises it.** -/
theorem measure_raise (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hg : g < L.threads) {k : Nat} {σ σ' : (thread P L g).D} {e : Event}
    (he : X.get (g, k) = some e) (hσ : Frame.stateAt (thread P L) X g k = some (some σ))
    (hu : ∀ f, e.kind ≠ .ub f) (hn : (thread P L g).next σ e = some (some σ')) :
    Raise (measure P L g σ) (measure P L g σ') e := by
  have hF := follow_iff.mp hFw
  have hJ := (hF g hg k).2 σ hσ
  have hσ' : Frame.stateAt (thread P L) X g (k + 1) = some (some σ') := by
    rw [Frame.stateAt_succ he, hσ]; exact hn
  have hJ' := (hF g hg (k + 1)).2 σ' hσ'
  have h0 := state_ub hX hσ he
  obtain ⟨s, n⟩ := σ
  have hc := state_count hσ
  have h0' : Code.bump cls n e .ub = 0 := by rw [bump_keep (cls_ub hu)]; exact h0
  rcases s with d | ⟨i | r, d⟩
  · rw [next_startup] at hn
    obtain ⟨d', hs, rfl⟩ := map_some hn
    refine Raise.of_lt ?_
    have hlt := Startup.measure_step hs
    have hle := Startup.measure_le d
    unfold Code.enter
    split
    · next x _ =>
      rcases x with i | r
      · simp only [measure, fragBase]; omega
      · simp only [measure, fragBase]; omega
    · simp only [measure]; omega
  · cases i with
    | wg0 =>
      rw [next_frag] at hn
      obtain ⟨d', hs, rfl⟩ := map_some hn
      have hw : n (.wg0 .ub) = 0 := (hc _).trans (wg0_take_noUb hX he)
      have hw' : Code.bump cls n e (.wg0 .ub) = 0 := by rw [bump_keep (wg0_ub hu)]; exact hw
      obtain ⟨-, hW, -⟩ := hJ
      obtain ⟨-, hW', -⟩ := hJ'
      exact Raise.add fragBase (Wg0.measure_step (hW.1 h0 hw).1 (hW'.1 h0' hw').1 hs)
    | dequant =>
      rw [next_frag] at hn
      obtain ⟨d', hs, rfl⟩ := map_some hn
      have hw : n (.dequant .ub) = 0 := (hc _).trans (wg2_take_noUb hX he)
      have hw' : Code.bump cls n e (.dequant .ub) = 0 := by
        rw [bump_keep (dequant_ub hu)]; exact hw
      obtain ⟨-, hW, -⟩ := hJ
      obtain ⟨-, hW', -⟩ := hJ'
      exact Raise.add fragBase (Dequant.measure_step (hW h0) hw (hW' h0') hw' hs)
    | wg1 =>
      rcases d with s | ⟨j | r, d⟩
      · rw [next_head] at hn
        obtain ⟨s', hs, rfl⟩ := map_some hn
        refine Raise.add fragBase (Raise.of_lt ?_)
        have hlt := Wg1.measure_step hs
        have hle := Wg1.time_le s
        unfold Code.enter
        split
        · next x _ =>
          rcases x with j | r
          · cases j <;> simp only [fragMeasure, wg1Measure, Wg1.measure] at hlt hle ⊢ <;> omega
          · simp only [fragMeasure, wg1Measure, Wg1.measure] at hlt hle ⊢; omega
        · simp only [fragMeasure, wg1Measure]; exact hlt
      · rw [next_sub] at hn
        obtain ⟨d', hs, rfl⟩ := map_some hn
        cases j with
        | mma =>
          have hw : n (.mma .ub) = 0 := (hc _).trans (take_noUb hX he)
          obtain ⟨-, ⟨-, -, ⟨hM, -⟩, -⟩, -⟩ := hJ
          have hx : wg1Measure P L g (.inr ⟨.inl .mma, d⟩) n ≤ 3 + subTop := by
            have := Mma.measure_le d
            have : Mma.top ≤ subTop := Nat.le_max_left _ _
            simp only [wg1Measure, mmaMeasure]; omega
          cases hb : subBack P L g .mma d' with
          | some p =>
            simp only [Code.backEnter, hb] at hJ' ⊢
            exact back_raise hx hb hJ'
          | none =>
            simp only [Code.backEnter, hb] at hJ' ⊢
            obtain ⟨-, ⟨-, -, ⟨hM', -⟩, -⟩, -⟩ := hJ'
            have hw' := Mma.bump_ub (n := fun c => n (.mma c)) hu hw
            exact Raise.add fragBase (Raise.add 3 (Mma.measure_step (hM h0 hw) (hM' h0' hw') hs))
        | tma =>
          have hw : n (.tma .ub) = 0 := (hc _).trans (lane5_take_noUb hX he)
          obtain ⟨-, ⟨-, -, ⟨hM, -⟩, -⟩, -⟩ := hJ
          have hx : wg1Measure P L g (.inr ⟨.inl .tma, d⟩) n ≤ 3 + subTop := by
            have := Tma.measure_le d
            have : Tma.top ≤ subTop := Nat.le_max_right _ _
            simp only [wg1Measure, tmaMeasure]; omega
          cases hb : subBack P L g .tma d' with
          | some p =>
            simp only [Code.backEnter, hb] at hJ' ⊢
            exact back_raise hx hb hJ'
          | none =>
            simp only [Code.backEnter, hb] at hJ' ⊢
            obtain ⟨-, ⟨-, -, ⟨hM', -⟩, -⟩, -⟩ := hJ'
            have hw' := Tma.bump_ub0 (n := fun c => n (.tma c)) hu hw
            exact Raise.add fragBase (Raise.add 3 (Tma.measure_step (hM h0 hw) (hM' h0' hw') hs))
        | index =>
          simp only [Code.backEnter, subBack]
          exact Raise.add fragBase (Raise.add 3 (Index.bplace_mono hs))
        | idle =>
          simp only [Code.backEnter, subBack]
          exact Raise.add fragBase (Raise.add (4 + subTop) (Raise.of_lt (Wg1.imeasure_step hs)))
      · rw [next_frag] at hn
        simp [frag, wg1Code, Code.roleLoop, Code.loopGlue, Code.withStubsAt, Code.stopAt] at hn
  · simp [thread, Code.roleThread, Code.counted, Code.glue, Code.withStubs, Code.stop] at hn

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
