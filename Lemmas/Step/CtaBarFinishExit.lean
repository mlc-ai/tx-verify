-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Step.CtaBarAppendWarp
public import Lemmas.Step.CtaBarAllArrived

@[expose] public section

/-! # Releasing a `bar.sync` whose participants may have exited

A proof tool for named barriers whose participants use either form and may exit after their
last arrival. `NamedBar.wait_finish_arrive` asks that no participant exit; here a participant
that exited has its arrivals recorded before its exit (`recorded_or_last`), and the generation is
read from the records alone.

In a maximal execution of a kernel whose consistent executions have no CTA barrier fault, let
thread `g`'s last event be its `bar.sync` on named barrier `id` of ordinal `G`, and let every
participant lane of its CTA have made its arrival of ordinal `G`. Then a maximal execution with
the same traces releases `g` (`sync_release`): the warps whose arrivals are not recorded are
appended one at a time (`append_warp`, through `warp_step`), after which every participant warp
has a record in generation `G` (`Sources.arrival_key`), so generation `G` is released
(`CtaBarrier.released_of_all_arrived`). -/

namespace PTX.NamedBar
open PTX CtaBarrier

noncomputable section

variable {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0} {X : Execution}

/-- Every arrival of ordinal `G` on named barrier `id` of a lane of warp `w` of CTA `c` is
recorded in `Z`. -/
def WarpRec (L : Launch) (X Z : Execution) (c w id G : Nat) : Prop :=
  ∀ y, y < L.block → y / 32 = w → ∀ j pc m cnt,
    X.get (c * L.block + y, j) = some ⟨pc, .bar id cnt m⟩ →
    ((X.tr (c * L.block + y)).take j).countP (Execution.isBarId id) = G →
    (c * L.block + y, j) ∈ (Z.barriers c).flatMap Record.refs

/-- Every lane of the proposed warp is at the same local occurrence of the named resource. -/
def WarpLastOrdinal (L : Launch) (X : Execution) (c w id ordinal : Nat) : Prop :=
  ∀ lane < L.block, lane/32 = w →
    let g := c*L.block+lane
    ((X.tr g).take ((X.tr g).length-1)).countP (Execution.isBarId id) = ordinal

/-- Record one warp without changing memory writes, using absence of local append faults. -/
private theorem warp_step_preserving_objects
    (hA : Assumption.WfCtaHistory (L := L) (K := K) (mem0 := mem0) A)
    {count : Option Nat}
    {p : Finset Nat} {id c G : Nat} (hG : Shape L count p id) (hc : c < L.grid)
    (hlane : ∀ y, y < L.block → y / 32 ∈ p → ∃ j pc m,
      X.get (c * L.block + y, j) = some ⟨pc, .bar id count m⟩ ∧
      ((X.tr (c * L.block + y)).take j).countP (Execution.isBarId id) = G)
    {Z : Execution} (hZ : Maximal L K A mem0 Z) (htr : Z.tr = X.tr) {w : Nat} (hw : w ∈ p)
    (hf : WarpLastOrdinal L Z c w id G → ¬ WarpAppendFault L Z c w id count) :
    ∃ Z', Maximal L K A mem0 Z' ∧ Z'.tr = X.tr ∧ Z'.MemWrites = Z.MemWrites ∧
      Z'.objects = Z.objects ∧
      (∀ w', WarpRec L X Z c w' id G → WarpRec L X Z' c w' id G) ∧
      WarpRec L X Z' c w id G := by
  have hget : ∀ e, Z.get e = X.get e := fun e => by simp only [Execution.get, htr]
  have hZX := hZ.1
  have hwb := hG.bound w hw
  have hw32 : w * 32 < L.block := by omega
  -- a lane's arrival of ordinal `G` is recorded or is its last event, with no exit
  have hrol : ∀ y j pc m cnt, y < L.block →
      X.get (c * L.block + y, j) = some ⟨pc, .bar id cnt m⟩ →
      (c * L.block + y, j) ∈ (Z.barriers c).flatMap Record.refs ∨
        (j + 1 = (X.tr (c * L.block + y)).length ∧
          ∀ k pc', X.get (c * L.block + y, k) ≠ some ⟨pc', .exit⟩) := by
    intro y j pc m cnt hy hj
    have hdiv := (lane_cta (c := c) (block_pos_of_thread_lt (cta_thread_lt hc hy)) hy).1
    rcases recorded_or_last hZX (by rw [hget]; exact hj) with hr | hl
    · rw [hdiv] at hr
      exact .inl hr
    · simp only [htr] at hl
      refine .inr ⟨hl, fun k pc' hk => ?_⟩
      have := Execution.exit_last hZX (cta_thread_lt hc hy) (by rw [hget]; exact hk)
      rw [htr] at this
      have hkj : k = j := by omega
      rw [hkj, hj] at hk
      cases hk
  have h0w : w * 32 / 32 = w := Nat.mul_div_cancel _ (by decide)
  obtain ⟨j0, pc0, m0, hj0, ho0⟩ := hlane (w * 32) hw32 (by rw [h0w]; exact hw)
  by_cases hrec0 : (c * L.block + w * 32, j0) ∈ (Z.barriers c).flatMap Record.refs
  · refine ⟨Z, hZ, htr, rfl, rfl, fun _ h => h, ?_⟩
    intro y hy hyw j pc m cnt hj hord
    rcases hrol y j pc m cnt hy hj with hr | ⟨-, hno⟩
    · exact hr
    · exact recorded_of_lane hZX hc hw32 hy (by omega) (by rw [hget]; exact hj0)
        (by rw [hget]; exact hj) (by rw [htr, ho0, hord]) hrec0
        (fun k pc' hk => hno k pc' (by rw [← hget]; exact hk))
  -- the warp's arrivals are all unrecorded last events: append the warp's record
  have hlast : ∀ y, y < L.block → y / 32 = w → ∀ j pc m cnt,
      X.get (c * L.block + y, j) = some ⟨pc, .bar id cnt m⟩ →
      ((X.tr (c * L.block + y)).take j).countP (Execution.isBarId id) = G →
      (c * L.block + y, j) ∉ (Z.barriers c).flatMap Record.refs ∧
        j + 1 = (X.tr (c * L.block + y)).length := by
    intro y hy hyw j pc m cnt hj hord
    have hnr : (c * L.block + y, j) ∉ (Z.barriers c).flatMap Record.refs := by
      intro hr
      rcases hrol (w * 32) j0 pc0 m0 count hw32 hj0 with hr0 | ⟨-, hno0⟩
      · exact hrec0 hr0
      · exact hrec0 (recorded_of_lane hZX hc hy hw32 (by omega) (by rw [hget]; exact hj)
          (by rw [hget]; exact hj0) (by rw [htr, ho0, hord]) hr
          (fun k pc' hk => hno0 k pc' (by rw [← hget]; exact hk)))
    rcases hrol y j pc m cnt hy hj with hr | ⟨hl, -⟩
    · exact absurd hr hnr
    · exact ⟨hnr, hl⟩
  have hCandidate : WarpLastOrdinal L Z c w id G := by
    intro lt hlt hlw
    obtain ⟨j, pc, m, hj, hord⟩ := hlane lt hlt (hlw ▸ hw)
    obtain ⟨_, hEnd⟩ := hlast lt hlt hlw j pc m count hj hord
    dsimp only
    rw [htr, show (X.tr (c*L.block+lt)).length-1 = j by omega]
    exact hord
  let Z' := Z.withCtaHistory c (Z.barriers c ++ [warpRecord L Z c w id count])
  have hZ' : Maximal L K A mem0 Z' :=
    append_warp_in_history hZ hA (w := w) (cnt := count) (hf hCandidate) hc
    hw32 hG.id_lt hG.target (fun lt hlt hlw => by
      obtain ⟨j, pc, m, hj, hord⟩ := hlane lt hlt (hlw ▸ hw)
      obtain ⟨hnr, hl⟩ := hlast lt hlt hlw j pc m count hj hord
      have hj' : (Z.tr (c * L.block + lt)).length - 1 = j := by rw [htr]; omega
      rw [hj', hget]
      exact ⟨⟨pc, m, hj⟩, hnr⟩)
  have hZc : Z'.barriers c = Z.barriers c ++ [warpRecord L Z c w id count] :=
    withCtaHistory_barriers_self _ _ _
  have hmono : ∀ w', WarpRec L X Z c w' id G → WarpRec L X Z' c w' id G := by
    intro w' hW y hy hyw j pc m cnt hj hord
    rw [hZc, List.flatMap_append]
    exact List.mem_append_left _ (hW y hy hyw j pc m cnt hj hord)
  have hWrites : Z'.MemWrites = Z.MemWrites := by
    funext ref a bytes
    unfold Execution.MemWrites
    split <;> rfl
  refine ⟨Z', hZ', htr, hWrites, rfl, hmono, ?_⟩
  intro y hy hyw j pc m cnt hj hord
  obtain ⟨-, hl⟩ := hlast y hy hyw j pc m cnt hj hord
  rw [hZc, List.flatMap_append]
  refine List.mem_append_right _ ?_
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, warpRecord, Record.refs]
  refine List.mem_map.mpr ⟨(y, (c * L.block + y, (Z.tr (c * L.block + y)).length - 1)),
    mem_fullLanes.mpr ⟨hy, hyw, rfl⟩, ?_⟩
  simp only [htr]
  congr 1
  omega

theorem warp_step_preserving_writes
    (hA : Assumption.WfCtaHistory (L := L) (K := K) (mem0 := mem0) A)
    {count : Option Nat}
    {p : Finset Nat} {id c G : Nat} (hG : Shape L count p id) (hc : c < L.grid)
    (hlane : ∀ y, y < L.block → y / 32 ∈ p → ∃ j pc m,
      X.get (c * L.block + y, j) = some ⟨pc, .bar id count m⟩ ∧
      ((X.tr (c * L.block + y)).take j).countP (Execution.isBarId id) = G)
    {Z : Execution} (hZ : Maximal L K A mem0 Z) (htr : Z.tr = X.tr) {w : Nat} (hw : w ∈ p)
    (hf : WarpLastOrdinal L Z c w id G → ¬ WarpAppendFault L Z c w id count) :
    ∃ Z', Maximal L K A mem0 Z' ∧ Z'.tr = X.tr ∧ Z'.MemWrites = Z.MemWrites ∧
      (∀ w', WarpRec L X Z c w' id G → WarpRec L X Z' c w' id G) ∧
      WarpRec L X Z' c w id G := by
  obtain ⟨Z',hZ',hTr,hWrites,_,hKeep,hRecord⟩ :=
    warp_step_preserving_objects hA hG hc hlane hZ htr hw hf
  exact ⟨Z',hZ',hTr,hWrites,hKeep,hRecord⟩

/-- Record one warp using only the absence of faults for that particular append. -/
theorem warp_step_of_noLocalFault
    (hA : Assumption.WfCtaHistory (L := L) (K := K) (mem0 := mem0) A)
    {count : Option Nat}
    {p : Finset Nat} {id c G : Nat} (hG : Shape L count p id) (hc : c < L.grid)
    (hlane : ∀ y, y < L.block → y / 32 ∈ p → ∃ j pc m,
      X.get (c * L.block + y, j) = some ⟨pc, .bar id count m⟩ ∧
      ((X.tr (c * L.block + y)).take j).countP (Execution.isBarId id) = G)
    {Z : Execution} (hZ : Maximal L K A mem0 Z) (htr : Z.tr = X.tr) {w : Nat} (hw : w ∈ p)
    (hf : WarpLastOrdinal L Z c w id G → ¬ WarpAppendFault L Z c w id count) :
    ∃ Z', Maximal L K A mem0 Z' ∧ Z'.tr = X.tr ∧
      (∀ w', WarpRec L X Z c w' id G → WarpRec L X Z' c w' id G) ∧
      WarpRec L X Z' c w id G := by
  obtain ⟨Y, hY, hTr, _, hMono, hRecord⟩ :=
    warp_step_preserving_writes hA hG hc hlane hZ htr hw hf
  exact ⟨Y, hY, hTr, hMono, hRecord⟩

/-- **One participant warp's arrival of ordinal `G` gets recorded**, in an extension with the
same traces that keeps every recorded warp recorded. -/
theorem warp_step {sel : Nat → Bool} (hA : Assumption.WfStep sel L K mem0 A)
    (hf : ∀ Y, Consistent L K A mem0 Y → ¬ CtaBarFault L Y) {count : Option Nat}
    {p : Finset Nat} {id c G : Nat} (hG : Shape L count p id) (hc : c < L.grid)
    (hlane : ∀ y, y < L.block → y / 32 ∈ p → ∃ j pc m,
      X.get (c * L.block + y, j) = some ⟨pc, .bar id count m⟩ ∧
      ((X.tr (c * L.block + y)).take j).countP (Execution.isBarId id) = G)
    {Z : Execution} (hZ : Maximal L K A mem0 Z) (htr : Z.tr = X.tr) {w : Nat} (hw : w ∈ p) :
    ∃ Z', Maximal L K A mem0 Z' ∧ Z'.tr = X.tr ∧
      (∀ w', WarpRec L X Z c w' id G → WarpRec L X Z' c w' id G) ∧
      WarpRec L X Z' c w id G := by
  exact warp_step_of_noLocalFault hA.ctaHistory hG hc hlane hZ htr hw
    (fun _ h => hf Z hZ.1 (h.ctaBarFault hc))

/-- Record the participant warps using a local fault check that can use the write frame. -/
private theorem warps_record_preserving_objects {base : Execution}
    (hA : Assumption.WfCtaHistory (L := L) (K := K) (mem0 := mem0) A) {count : Option Nat}
    {p : Finset Nat} {id c G : Nat} (hG : Shape L count p id) (hc : c < L.grid)
    (hf : ∀ Z, Consistent L K A mem0 Z → Z.tr = X.tr → Z.MemWrites = base.MemWrites → ∀ w ∈ p,
      WarpLastOrdinal L Z c w id G → ¬ WarpAppendFault L Z c w id count)
    (hlane : ∀ y, y < L.block → y / 32 ∈ p → ∃ j pc m,
      X.get (c * L.block + y, j) = some ⟨pc, .bar id count m⟩ ∧
      ((X.tr (c * L.block + y)).take j).countP (Execution.isBarId id) = G) :
    ∀ (ws : List Nat), (∀ w ∈ ws, w ∈ p) → ∀ {Z : Execution}, Maximal L K A mem0 Z →
      Z.tr = X.tr → Z.MemWrites = base.MemWrites →
        ∃ Y, Maximal L K A mem0 Y ∧ Y.tr = X.tr ∧ Y.MemWrites = base.MemWrites ∧
        Y.objects = Z.objects ∧
        (∀ w', WarpRec L X Z c w' id G → WarpRec L X Y c w' id G) ∧
        ∀ w ∈ ws, WarpRec L X Y c w id G := by
  intro ws
  induction ws with
  | nil => exact fun _ Z hZ htr hWrites => ⟨Z, hZ, htr, hWrites, rfl, fun _ h => h, by simp⟩
  | cons w ws ih =>
    intro hws Z hZ htr hWrites
    obtain ⟨Z', hZ', htr', hWrites', hObjects', hmono, hw⟩ :=
      warp_step_preserving_objects hA hG hc hlane hZ htr (hws w List.mem_cons_self)
        (hf Z hZ.1 htr hWrites w (hws w List.mem_cons_self))
    obtain ⟨Y, hY, htrY, hWritesY, hObjectsY, hmono', hall⟩ :=
      ih (fun v hv => hws v (List.mem_cons_of_mem _ hv)) hZ' htr' (hWrites'.trans hWrites)
    refine ⟨Y, hY, htrY, hWritesY, hObjectsY.trans hObjects',
      fun v hv => hmono' v (hmono v hv), fun v hv => ?_⟩
    rcases List.mem_cons.mp hv with rfl | hv
    · exact hmono' v hw
    · exact hall v hv

theorem warps_record_preserving_writes {base : Execution}
    (hA : Assumption.WfCtaHistory (L := L) (K := K) (mem0 := mem0) A) {count : Option Nat}
    {p : Finset Nat} {id c G : Nat} (hG : Shape L count p id) (hc : c < L.grid)
    (hf : ∀ Z, Consistent L K A mem0 Z → Z.tr = X.tr → Z.MemWrites = base.MemWrites → ∀ w ∈ p,
      WarpLastOrdinal L Z c w id G → ¬ WarpAppendFault L Z c w id count)
    (hlane : ∀ y, y < L.block → y / 32 ∈ p → ∃ j pc m,
      X.get (c * L.block + y, j) = some ⟨pc, .bar id count m⟩ ∧
      ((X.tr (c * L.block + y)).take j).countP (Execution.isBarId id) = G) :
    ∀ (ws : List Nat), (∀ w ∈ ws, w ∈ p) → ∀ {Z : Execution}, Maximal L K A mem0 Z →
      Z.tr = X.tr → Z.MemWrites = base.MemWrites →
        ∃ Y, Maximal L K A mem0 Y ∧ Y.tr = X.tr ∧ Y.MemWrites = base.MemWrites ∧
        (∀ w', WarpRec L X Z c w' id G → WarpRec L X Y c w' id G) ∧
        ∀ w ∈ ws, WarpRec L X Y c w id G := by
  intro ws hWs Z hZ hTr hWrites
  obtain ⟨Y,hY,hTrY,hWritesY,_,hKeep,hRecord⟩ :=
    warps_record_preserving_objects hA hG hc hf hlane ws hWs hZ hTr hWrites
  exact ⟨Y,hY,hTrY,hWritesY,hKeep,hRecord⟩

/-- Record the participant warps using only the absence of faults for their appends. -/
theorem warps_record_of_noLocalFault
    (hA : Assumption.WfCtaHistory (L := L) (K := K) (mem0 := mem0) A)
    {count : Option Nat}
    {p : Finset Nat} {id c G : Nat} (hG : Shape L count p id) (hc : c < L.grid)
    (hf : ∀ Z, Consistent L K A mem0 Z → ∀ w ∈ p,
      WarpLastOrdinal L Z c w id G → ¬ WarpAppendFault L Z c w id count)
    (hlane : ∀ y, y < L.block → y / 32 ∈ p → ∃ j pc m,
      X.get (c * L.block + y, j) = some ⟨pc, .bar id count m⟩ ∧
      ((X.tr (c * L.block + y)).take j).countP (Execution.isBarId id) = G) :
    ∀ (ws : List Nat), (∀ w ∈ ws, w ∈ p) → ∀ {Z : Execution}, Maximal L K A mem0 Z →
      Z.tr = X.tr → ∃ Y, Maximal L K A mem0 Y ∧ Y.tr = X.tr ∧
        (∀ w', WarpRec L X Z c w' id G → WarpRec L X Y c w' id G) ∧
        ∀ w ∈ ws, WarpRec L X Y c w id G := by
  intro ws hWs Z hZ hTr
  obtain ⟨Y, hY, hTr', _, hMono, hRecord⟩ :=
    warps_record_preserving_writes (base := Z) hA hG hc
      (fun W hW _ _ => hf W hW) hlane ws hWs hZ hTr rfl
  exact ⟨Y, hY, hTr', hMono, hRecord⟩

/-- **Every participant warp's arrival of ordinal `G` gets recorded**, in an extension with the
same traces that keeps every recorded warp recorded. -/
theorem warps_record {sel : Nat → Bool} (hA : Assumption.WfStep sel L K mem0 A)
    (hf : ∀ Y, Consistent L K A mem0 Y → ¬ CtaBarFault L Y) {count : Option Nat}
    {p : Finset Nat} {id c G : Nat} (hG : Shape L count p id) (hc : c < L.grid)
    (hlane : ∀ y, y < L.block → y / 32 ∈ p → ∃ j pc m,
      X.get (c * L.block + y, j) = some ⟨pc, .bar id count m⟩ ∧
      ((X.tr (c * L.block + y)).take j).countP (Execution.isBarId id) = G) :
    ∀ (ws : List Nat), (∀ w ∈ ws, w ∈ p) → ∀ {Z : Execution}, Maximal L K A mem0 Z →
      Z.tr = X.tr → ∃ Y, Maximal L K A mem0 Y ∧ Y.tr = X.tr ∧
        (∀ w', WarpRec L X Z c w' id G → WarpRec L X Y c w' id G) ∧
        ∀ w ∈ ws, WarpRec L X Y c w id G := by
  exact warps_record_of_noLocalFault hA.ctaHistory hG hc
    (fun Y hY _ _ _ h => hf Y hY (h.ctaBarFault hc)) hlane

/-- Release a synchronization generation for all its waiting lanes in a common history.
The extension preserves traces, memory writes, and object histories. -/
theorem sync_generation_release_preserving_objects (hmax : Maximal L K A mem0 X)
    (hA : Assumption.WfCtaHistory (L := L) (K := K) (mem0 := mem0) A)
    (hf : ∀ Y, Consistent L K A mem0 Y → Y.tr = X.tr → Y.MemWrites = X.MemWrites →
      ¬ CtaBarFault L Y) {count : Option Nat}
    {p : Finset Nat} {id : Nat} (hG : Shape L count p id) (hS : Sources L X count p id)
    {c G : Nat} (hc : c < L.grid)
    (hlane : ∀ y, y < L.block → y / 32 ∈ p → ∃ j pc m,
      X.get (c * L.block + y, j) = some ⟨pc, .bar id count m⟩ ∧
      ((X.tr (c * L.block + y)).take j).countP (Execution.isBarId id) =
        G) :
    ∃ Y, Maximal L K A mem0 Y ∧ Y.tr = X.tr ∧ Y.MemWrites = X.MemWrites ∧
      Y.objects = X.objects ∧
      ∀ {peer site : Nat}, peer < L.threads → peer / L.block = c →
        X.get (peer,(X.tr peer).length-1) = some ⟨site,.bar id count .sync⟩ →
        ((X.tr peer).take ((X.tr peer).length-1)).countP (Execution.isBarId id) =
          G →
        Step.Released L Y peer := by
  have hb : 0 < L.block := by
    obtain ⟨w,hw⟩ := Finset.card_pos.mp hG.pos
    have hBound := hG.bound w hw
    omega
  obtain ⟨Y, hY, htr, hWrites, hObjects, -, hall⟩ :=
    warps_record_preserving_objects (base := X) hA hG hc
      (fun Z hZ hTr hWrites _ _ _ he => hf Z hZ hTr hWrites (he.ctaBarFault hc))
      hlane p.toList (fun w hw => Finset.mem_toList.mp hw) hmax rfl rfl
  have hYX := hY.1
  have hget : ∀ e, Y.get e = X.get e := fun e => by simp only [Execution.get, htr]
  have hSY : Sources L Y count p id := fun e pc cnt ⟨m, he⟩ hgt =>
    hS e pc cnt ⟨m, (hget e) ▸ he⟩ hgt
  have hid := hG.id_lt
  -- every participant warp has a record in generation `G`
  have hrun := (hYX.ctaBar.2 c hc).2.2
  obtain ⟨u, hu⟩ := hrun
  have hrel : Released L.block (Y.barriers c) id G := by
    refine released_of_all_arrived (hSY.protocol hYX hc) hG.pos hG.target rfl hG.bound hu ?_
    intro w hw
    have hwb := hG.bound w hw
    have h0w : w * 32 / 32 = w := Nat.mul_div_cancel _ (by decide)
    obtain ⟨j, pcj, mj, hj, hord⟩ := hlane (w * 32) (by omega) (by rw [h0w]; exact hw)
    have hrec := hall w (Finset.mem_toList.mpr hw) (w * 32) (by omega) h0w j pcj mj count hj hord
    obtain ⟨r, hr, href⟩ := List.mem_flatMap.mp hrec
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hr
    obtain ⟨s, t, hs, ht⟩ := run_at_record hu hi
    have hsrc := (hYX.ctaBar.2 c hc).2.1 r hr
    cases r with
    | exit x y =>
      obtain ⟨-, -, pcx, hgx⟩ := hsrc
      rw [← (List.mem_singleton.mp href), hget, hj] at hgx
      cases hgx
    | arrival id' w' cnt' lanes =>
      obtain ⟨q, hq, hqe⟩ := List.mem_map.mp href
      obtain ⟨-, hq2, pcq, mq, hqb⟩ := hsrc q hq
      rw [hqe, hget, hj] at hqb
      simp only [Option.some.injEq, Event.mk.injEq, Kind.bar.injEq] at hqb
      obtain ⟨-, rfl, rfl, -⟩ := hqb
      have hq1 : q.1 = w * 32 := by
        rw [hqe] at hq2
        simp only at hq2
        omega
      have hww : w = w' := by
        have := ((perform_arrival_lanes ht).2.1 q hq).2.1
        rw [hq1, h0w] at this
        exact this
      subst hww
      refine ⟨i, lanes, s, hi, hs, ?_⟩
      have hthr : c * L.block + w * 32 < L.threads := cta_thread_lt hc (by omega)
      have hdiv := (lane_cta (c := c) hb (show w * 32 < L.block by omega)).1
      have hk : CtaBarArrivalK L Y (c * L.block + w * 32, j) (id + 16 * (s.slots id).generation) :=
        CtaBarArrivalK.of_generation hYX.ctaBar hthr hid (by
          simp only [hdiv]
          exact ⟨i, s, w, count, lanes, q.1, hi, hs, by rw [← hqe]; exact hq, rfl, t, ht⟩)
      have hkey := hSY.arrival_key hYX hG (by rw [hget]; exact hj) hk
      simp only [htr, hord] at hkey
      omega
  refine ⟨Y,hY,htr,hWrites,hObjects,?_⟩
  intro peer site hPeer hCta hLast hOrdinal
  have hLastY : Y.get (peer,(X.tr peer).length-1) = some ⟨site,.bar id count .sync⟩ := by
    rw [hget]
    exact hLast
  have hReleased : Released L.block (Y.barriers (peer/L.block)) id
      (((Y.tr peer).take ((X.tr peer).length-1)).countP (Execution.isBarId id)) := by
    simpa only [htr,hOrdinal,hCta] using hrel
  have hk := hSY.key_of_released hYX hG hLastY hPeer hReleased
  simp only [htr,hOrdinal] at hk
  have hmod : (id + 16*G)%16 = id := by omega
  have hdivG : (id + 16*G)/16 = G := by omega
  have hKey : CtaBarK L Y (peer,(X.tr peer).length-1) (id+16*G) :=
    ⟨hk.1,⟨count,site,by rw [hmod]; exact hLastY⟩,hk.2.2⟩
  have hDone : CtaBarDone L Y (peer/L.block) (id+16*G) := by
    unfold CtaBarDone
    rw [hmod,hdivG,hCta]
    exact hrel
  exact released_of_key hYX.ctaBar htr hLast hKey hDone

theorem sync_release_preserving_writes (hmax : Maximal L K A mem0 X)
    (hA : Assumption.WfCtaHistory (L := L) (K := K) (mem0 := mem0) A)
    (hf : ∀ Y, Consistent L K A mem0 Y → Y.tr = X.tr → Y.MemWrites = X.MemWrites →
      ¬ CtaBarFault L Y) {count : Option Nat}
    {p : Finset Nat} {id : Nat} (hG : Shape L count p id) (hS : Sources L X count p id)
    {g pc : Nat} (hg : g < L.threads)
    (hlast : X.IsBarrier (g, (X.tr g).length - 1) id count pc)
    (hlane : ∀ y, y < L.block → y / 32 ∈ p → ∃ j pc m,
      X.get (g / L.block * L.block + y, j) = some ⟨pc, .bar id count m⟩ ∧
      ((X.tr (g / L.block * L.block + y)).take j).countP (Execution.isBarId id) =
        ((X.tr g).take ((X.tr g).length - 1)).countP (Execution.isBarId id)) :
    ∃ Y, Maximal L K A mem0 Y ∧ Y.tr = X.tr ∧ Y.MemWrites = X.MemWrites ∧ Step.Released L Y g := by
  obtain ⟨Y,hY,hTr,hWrites,_,hRelease⟩ :=
    sync_generation_release_preserving_objects hmax hA hf hG hS (cta_lt hg) hlane
  refine ⟨Y,hY,hTr,hWrites,hRelease hg rfl hlast ?_⟩
  rfl

/-- **A `bar.sync` whose participants have all arrived is released in an extension.** In a
maximal execution of a kernel whose consistent executions have no CTA barrier fault, let thread
`g`'s last event be its `bar.sync` on named barrier `id` (group `p`, sources `hS`), and let every
participant lane of its CTA have made its arrival of the same ordinal. Participants may have
exited. Then a maximal execution with the same traces releases `g`. -/
theorem sync_release_of_wf (hmax : Maximal L K A mem0 X)
    (hA : Assumption.WfCtaHistory (L := L) (K := K) (mem0 := mem0) A)
    (hf : ∀ Y, Consistent L K A mem0 Y → ¬ CtaBarFault L Y) {count : Option Nat}
    {p : Finset Nat} {id : Nat} (hG : Shape L count p id) (hS : Sources L X count p id)
    {g pc : Nat} (hg : g < L.threads)
    (hlast : X.IsBarrier (g, (X.tr g).length - 1) id count pc)
    (hlane : ∀ y, y < L.block → y / 32 ∈ p → ∃ j pc m,
      X.get (g / L.block * L.block + y, j) = some ⟨pc, .bar id count m⟩ ∧
      ((X.tr (g / L.block * L.block + y)).take j).countP (Execution.isBarId id) =
        ((X.tr g).take ((X.tr g).length - 1)).countP (Execution.isBarId id)) :
    ∃ Y, Maximal L K A mem0 Y ∧ Y.tr = X.tr ∧ Step.Released L Y g := by
  obtain ⟨Y, hY, hTr, _, hRelease⟩ :=
    sync_release_preserving_writes hmax hA (fun Y hY _ _ => hf Y hY) hG hS hg hlast hlane
  exact ⟨Y, hY, hTr, hRelease⟩

/-- The step well-formedness rule supports releasing all arrival participants. -/
theorem sync_release (hmax : Maximal L K A mem0 X) {sel : Nat → Bool}
    (hA : Assumption.WfStep sel L K mem0 A)
    (hf : ∀ Y, Consistent L K A mem0 Y → ¬ CtaBarFault L Y) {count : Option Nat}
    {p : Finset Nat} {id : Nat} (hG : Shape L count p id) (hS : Sources L X count p id)
    {g pc : Nat} (hg : g < L.threads)
    (hlast : X.IsBarrier (g, (X.tr g).length - 1) id count pc)
    (hlane : ∀ y, y < L.block → y / 32 ∈ p → ∃ j pc m,
      X.get (g / L.block * L.block + y, j) = some ⟨pc, .bar id count m⟩ ∧
      ((X.tr (g / L.block * L.block + y)).take j).countP (Execution.isBarId id) =
        ((X.tr g).take ((X.tr g).length - 1)).countP (Execution.isBarId id)) :
    ∃ Y, Maximal L K A mem0 Y ∧ Y.tr = X.tr ∧ Step.Released L Y g :=
  sync_release_of_wf hmax hA.ctaHistory hf hG hS hg hlast hlane

end

end PTX.NamedBar
