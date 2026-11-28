-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Kernel.Progress.BarPhased
public import Lemmas.Protocol.NamedBarGenLedger
public import Lemmas.Step.CtaBarAppendWarp

@[expose] public section

/-!
# The warps' arrivals of a barrier generation with per-warp source ordinals

`NamedBar.warp_step` and `NamedBar.warps_record` (`Lemmas/Step/CtaBarFinishExit.lean`) take one
source ordinal `G` for every participant lane. In the last generation of the kernel's named
barrier 0 the default warps' arrivals and the workers' have different source ordinals; these are
the same two lemmas with the ordinal a function `Gw` of the warp.
-/

namespace PTX.NamedBar
open PTX CtaBarrier PTX.NamedBar.GenLedger

noncomputable section

variable {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0} {X : Execution}

/-- **One participant warp's arrival of ordinal `G` gets recorded**, in an extension with the
same traces that keeps every recorded warp recorded. -/
theorem warp_step_gw {sel : Nat → Bool} (hA : Assumption.WfStep sel L K mem0 A)
    (hf : ∀ Y, Consistent L K A mem0 Y → ¬ CtaBarFault L Y) {count : Option Nat}
    {p : Finset Nat} {id c : Nat} {Gw : Nat → Nat} (hG : Shape L count p id) (hc : c < L.grid)
    (hlane : ∀ y, y < L.block → y / 32 ∈ p → ∃ j pc m,
      X.get (c * L.block + y, j) = some ⟨pc, .bar id count m⟩ ∧
      ((X.tr (c * L.block + y)).take j).countP (Execution.isBarId id) = Gw (y / 32))
    {Z : Execution} (hZ : Maximal L K A mem0 Z) (htr : Z.tr = X.tr) {w : Nat} (hw : w ∈ p) :
    ∃ Z', Maximal L K A mem0 Z' ∧ Z'.tr = X.tr ∧
      (∀ w', WarpRec L X Z c w' id (Gw w') → WarpRec L X Z' c w' id (Gw w')) ∧
      WarpRec L X Z' c w id (Gw w) := by
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
  rw [h0w] at ho0
  by_cases hrec0 : (c * L.block + w * 32, j0) ∈ (Z.barriers c).flatMap Record.refs
  · refine ⟨Z, hZ, htr, fun _ h => h, ?_⟩
    intro y hy hyw j pc m cnt hj hord
    rcases hrol y j pc m cnt hy hj with hr | ⟨-, hno⟩
    · exact hr
    · exact recorded_of_lane hZX hc hw32 hy (by omega) (by rw [hget]; exact hj0)
        (by rw [hget]; exact hj) (by rw [htr, ho0, hord]) hrec0
        (fun k pc' hk => hno k pc' (by rw [← hget]; exact hk))
  -- the warp's arrivals are all unrecorded last events: append the warp's record
  have hlast : ∀ y, y < L.block → y / 32 = w → ∀ j pc m cnt,
      X.get (c * L.block + y, j) = some ⟨pc, .bar id cnt m⟩ →
      ((X.tr (c * L.block + y)).take j).countP (Execution.isBarId id) = Gw w →
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
  obtain ⟨Z', hZ', htr', hZc, -⟩ := append_warp hZ hA (hf Z hZX) (w := w) (cnt := count) hc
    hw32 hG.id_lt hG.target (fun lt hlt hlw => by
      obtain ⟨j, pc, m, hj, hord⟩ := hlane lt hlt (hlw ▸ hw)
      rw [hlw] at hord
      obtain ⟨hnr, hl⟩ := hlast lt hlt hlw j pc m count hj hord
      have hj' : (Z.tr (c * L.block + lt)).length - 1 = j := by rw [htr]; omega
      rw [hj', hget]
      exact ⟨⟨pc, m, hj⟩, hnr⟩)
  have hmono : ∀ w', WarpRec L X Z c w' id (Gw w') → WarpRec L X Z' c w' id (Gw w') := by
    intro w' hW y hy hyw j pc m cnt hj hord
    rw [hZc, List.flatMap_append]
    exact List.mem_append_left _ (hW y hy hyw j pc m cnt hj hord)
  refine ⟨Z', hZ', htr'.trans htr, hmono, ?_⟩
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

/-- **Every participant warp's arrival of ordinal `G` gets recorded**, in an extension with the
same traces that keeps every recorded warp recorded. -/
theorem warps_record_gw {sel : Nat → Bool} (hA : Assumption.WfStep sel L K mem0 A)
    (hf : ∀ Y, Consistent L K A mem0 Y → ¬ CtaBarFault L Y) {count : Option Nat}
    {p : Finset Nat} {id c : Nat} {Gw : Nat → Nat} (hG : Shape L count p id) (hc : c < L.grid)
    (hlane : ∀ y, y < L.block → y / 32 ∈ p → ∃ j pc m,
      X.get (c * L.block + y, j) = some ⟨pc, .bar id count m⟩ ∧
      ((X.tr (c * L.block + y)).take j).countP (Execution.isBarId id) = Gw (y / 32)) :
    ∀ (ws : List Nat), (∀ w ∈ ws, w ∈ p) → ∀ {Z : Execution}, Maximal L K A mem0 Z →
      Z.tr = X.tr → ∃ Y, Maximal L K A mem0 Y ∧ Y.tr = X.tr ∧
        (∀ w', WarpRec L X Z c w' id (Gw w') → WarpRec L X Y c w' id (Gw w')) ∧
        ∀ w ∈ ws, WarpRec L X Y c w id (Gw w) := by
  intro ws
  induction ws with
  | nil => exact fun _ Z hZ htr => ⟨Z, hZ, htr, fun _ h => h, by simp⟩
  | cons w ws ih =>
    intro hws Z hZ htr
    obtain ⟨Z', hZ', htr', hmono, hw⟩ :=
      warp_step_gw hA hf hG hc hlane hZ htr (hws w List.mem_cons_self)
    obtain ⟨Y, hY, htrY, hmono', hall⟩ :=
      ih (fun v hv => hws v (List.mem_cons_of_mem _ hv)) hZ' htr'
    refine ⟨Y, hY, htrY, fun v hv => hmono' v (hmono v hv), fun v hv => ?_⟩
    rcases List.mem_cons.mp hv with rfl | hv
    · exact hmono' v hw
    · exact hall v hv

/-- **A recorded `bar.sync` event's record**: its index in its CTA's history, the state before
it, a lane that holds it, and the source ordinal it has (the number of its warp's earlier
records on the barrier). -/
theorem recorded_record (hX : Consistent L K A mem0 X) {id : Nat} {e : EvId} {pc : Nat}
    {cnt : Option Nat} {m : BarMode} (he : X.get e = some ⟨pc, .bar id cnt m⟩)
    (hge : e.1 < L.threads) (hrec : e ∈ (X.barriers (e.1 / L.block)).flatMap Record.refs) :
    ∃ i lanes s t q, (X.barriers (e.1 / L.block))[i]? =
        some (.arrival id ((e.1 % L.block) / 32) cnt lanes) ∧
      At L.block (X.barriers (e.1 / L.block)) i s ∧ (q, e) ∈ lanes ∧
      Record.perform L.block s (.arrival id ((e.1 % L.block) / 32) cnt lanes) = .ok t ∧
      idArrivals ((X.barriers (e.1 / L.block)).take i) id ((e.1 % L.block) / 32) =
        ((X.tr e.1).take e.2).countP (Execution.isBarId id) ∧
      ((X.tr e.1).take e.2).countP (Execution.isBarId id) ≤ (s.slots id).generation := by
  have hc := cta_lt hge
  obtain ⟨-, -, last, hlast⟩ := hX.ctaBar.2 (e.1 / L.block) hc
  obtain ⟨r, hr, href⟩ := List.mem_flatMap.mp hrec
  obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hr
  obtain ⟨s, t, hs, ht⟩ := run_at_record hlast hk
  have hsrc := (hX.ctaBar.2 (e.1 / L.block) hc).2.1 r hr
  cases r with
  | exit x y =>
    obtain ⟨-, -, pcx, hgx⟩ := hsrc
    have hy : y = e := (List.mem_singleton.mp href).symm
    rw [hy, he] at hgx
    cases hgx
  | arrival id' w' cnt' lanes =>
    obtain ⟨q, hq, hqe⟩ := List.mem_map.mp href
    obtain ⟨-, hq2, pcq, mq, hqb⟩ := hsrc q hq
    rw [hqe, he] at hqb
    simp only [Option.some.injEq, Event.mk.injEq, Kind.bar.injEq] at hqb
    obtain ⟨-, rfl, rfl, -⟩ := hqb
    obtain ⟨hql, -, hqw, -, hord, hle⟩ := record_ordinal hX hc hlast hk hs hq
    have hqe' : q.2.1 = e.1 := by rw [hqe]
    have hqe2 : q.2.2 = e.2 := by rw [hqe]
    have hmod : e.1 % L.block = q.1 := by
      have h1 := Nat.div_add_mod e.1 L.block
      rw [hqe'] at hq2
      rw [Nat.mul_comm] at h1
      omega
    have hw : (e.1 % L.block) / 32 = w' := by rw [hmod, hqw]
    rw [hqe', hqe2] at hord
    refine ⟨k, lanes, s, t, q.1, ?_, hs, ?_, ?_, ?_, ?_⟩
    · rw [hw]; exact hk
    · rw [← hqe]; exact hq
    · rw [hw]; exact ht
    · rw [hw]; exact hord
    · rw [← hord]; exact hle

section Final

variable {D : Finset Nat} {cD : Option Nat} {start nD id : Nat}
variable [hK : Fact K.NoBarArrive]

/-- **The last generation of a phased barrier whose arrivals have different source ordinals.**
Let thread `g`'s last event be its `bar.sync` on barrier `id` without a count, and let every lane
of its CTA have an arrival on `id` without a count whose source ordinal is `Gw` of its warp,
at least `start` (the last generation's arrivals: the loop warps' have the ordinal of the
number of their earlier arrivals, the other warps' fewer). If `g`'s lane has no other such
arrival (`hone`), then a maximal execution with the same traces releases `g`.

The generation of `g`'s record is `F`. If `F` is open at the end of the replayed history, it
expects the whole CTA and the arrived warps are fewer than the CTA: a warp `w'` not arrived has
its last-generation record in a generation `F' < F`; that generation is completed, so every live
warp, `g`'s among them, has a record in it (`completion_arrivals`), whose count is none
(`same_gen_target`), and whose source ordinal is at least `start`; `g`'s lane has two such
arrivals, against `hone`. -/
theorem sync_release_final {sel : Nat → Bool} (hmax : Maximal L K A mem0 X)
    (hA : Assumption.WfStep sel L K mem0 A)
    (hf : ∀ Y, Consistent L K A mem0 Y → ¬ CtaBarFault L Y)
    (hD : D ⊆ Finset.range (warps L.block)) (hcard : D.card = nD) (hnD : nD ≠ warps L.block)
    (hcD : target L.block cD = .ok nD) (hS : PhSources L X D cD start id)
    (hG : Shape L none (Finset.range (warps L.block)) id) {g pc : Nat} (hg : g < L.threads)
    (hlast : X.IsBarrier (g, (X.tr g).length - 1) id none pc) {Gw : Nat → Nat}
    (hGg : Gw (g % L.block / 32) =
      ((X.tr g).take ((X.tr g).length - 1)).countP (Execution.isBarId id))
    (hstart : ∀ w ∈ Finset.range (warps L.block), start ≤ Gw w)
    (hlane : ∀ y, y < L.block → ∃ j pc m,
      X.get (g / L.block * L.block + y, j) = some ⟨pc, .bar id none m⟩ ∧
      ((X.tr (g / L.block * L.block + y)).take j).countP (Execution.isBarId id) = Gw (y / 32))
    (hone : ∀ j pc m, X.get (g, j) = some ⟨pc, .bar id none m⟩ →
      start ≤ ((X.tr g).take j).countP (Execution.isBarId id) → j = (X.tr g).length - 1) :
    ∃ Y, Maximal L K A mem0 Y ∧ Y.tr = X.tr ∧ Step.Released L Y g := by
  have hc := cta_lt hg
  have hb := block_pos_of_thread_lt hg
  set c := g / L.block with hcdef
  obtain ⟨Y, hY, htr, -, hall⟩ := warps_record_gw hA hf hG hc (Gw := Gw)
    (fun y hy _ => hlane y hy) (Finset.range (warps L.block)).toList
    (fun w hw => Finset.mem_toList.mp hw) hmax rfl
  have hYX := hY.1
  have hget : ∀ e, Y.get e = X.get e := fun e => by simp only [Execution.get, htr]
  have hSY : PhSources L Y D cD start id := by
    intro e pc' cnt ⟨m, he⟩ hgt
    have := hS e pc' cnt ⟨m, by rw [← hget]; exact he⟩ hgt
    simpa only [htr] using this
  have hprot := hSY.protocol hYX hc
  obtain ⟨u, hu⟩ := (hYX.ctaBar.2 c hc).2.2
  have hl := phased_run hD hcard hnD hcD hprot hu
  have howners : ∀ i s, At L.block (Y.barriers c) i s →
      (s.slots id).arrived ⊆ Finset.range (warps L.block) := fun i s hs =>
    (phased_run hD hcard hnD hcD (hprot.take i) hs).owners
  have hAtU : At L.block (Y.barriers c) (Y.barriers c).length u := by
    unfold At
    rw [List.take_length]
    exact hu
  have hgl : g % L.block < L.block := Nat.mod_lt _ hb
  have hgeq : c * L.block + g % L.block = g := by
    rw [hcdef, Nat.mul_comm]; exact Nat.div_add_mod g L.block
  have hwarps : target L.block none = .ok (warps L.block) := by simp [target]
  -- the recorded last-generation arrival of every warp
  have hrw : ∀ w ∈ Finset.range (warps L.block), ∃ i lanes s t q j pc' m,
      Y.get (c * L.block + w * 32, j) = some ⟨pc', .bar id none m⟩ ∧
      (Y.barriers c)[i]? = some (.arrival id w none lanes) ∧ At L.block (Y.barriers c) i s ∧
      (q, (c * L.block + w * 32, j)) ∈ lanes ∧
      Record.perform L.block s (.arrival id w none lanes) = .ok t ∧
      idArrivals ((Y.barriers c).take i) id w = Gw w ∧
      Gw w ≤ (s.slots id).generation := by
    intro w hw
    have hwb := hG.bound w hw
    have h0w : w * 32 / 32 = w := Nat.mul_div_cancel _ (by decide)
    obtain ⟨j, pcj, mj, hj, hord⟩ := hlane (w * 32) (by omega)
    rw [h0w] at hord
    have hrec := hall w (Finset.mem_toList.mpr hw) (w * 32) (by omega) h0w j pcj mj none hj
      hord
    have hge : c * L.block + w * 32 < L.threads := cta_thread_lt hc (by omega)
    have hdiv : (c * L.block + w * 32) / L.block = c := (lane_cta (c := c) hb (by omega)).1
    have hmod : (c * L.block + w * 32) % L.block = w * 32 := (lane_cta (c := c) hb (by omega)).2
    have hrec' : (c * L.block + w * 32, j) ∈ (Y.barriers ((c * L.block + w * 32) / L.block)).flatMap
        Record.refs := by rw [hdiv]; exact hrec
    obtain ⟨i, lanes, s, t, q, hi, hs, hq, ht, hord', hle⟩ := recorded_record hYX
      (e := (c * L.block + w * 32, j)) (by rw [hget]; exact hj) hge hrec'
    simp only [hdiv, hmod, h0w, htr, hord] at hi hs hq ht hord' hle
    exact ⟨i, lanes, s, t, q, j, pcj, mj, by rw [hget]; exact hj, hi, hs, hq, ht, hord', hle⟩
  -- `g`'s own record
  have hwg : g % L.block / 32 ∈ Finset.range (warps L.block) :=
    Finset.mem_range.mpr (by unfold warps; omega)
  have hnoexit : ∀ j pc', X.get (g, j) ≠ some ⟨pc', .exit⟩ := by
    intro j pc' hj
    have hl := Execution.exit_last hmax.1 hg hj
    have hj' : j = (X.tr g).length - 1 := by omega
    rw [hj', hlast] at hj
    cases hj
  have hlastY : Y.get (g, (X.tr g).length - 1) = some ⟨pc, .bar id none .sync⟩ := by
    rw [hget]; exact hlast
  have hrecg : (g, (X.tr g).length - 1) ∈ (Y.barriers c).flatMap Record.refs := by
    have := hall (g % L.block / 32) (Finset.mem_toList.mpr hwg) (g % L.block) hgl rfl
      ((X.tr g).length - 1) pc .sync none (by rw [hgeq]; exact hlast) (by rw [hgeq]; exact hGg.symm)
    rw [hgeq] at this
    exact this
  obtain ⟨ig, lanesg, sg, tg, qg, hig, hsg, hqg, htg, hordg, hleg⟩ := recorded_record hYX
    (e := (g, (X.tr g).length - 1)) hlastY hg hrecg
  dsimp only at hig hsg hqg htg hordg hleg
  rw [← hcdef] at hig hsg hordg
  rw [htr] at hordg hleg
  have hrelF : Released L.block (Y.barriers c) id (sg.slots id).generation := by
    by_contra hnrel
    have hAtg : At L.block (Y.barriers c) (ig + 1) tg := at_succ hig hsg htg
    have hmono_u : (sg.slots id).generation ≤ (u.slots id).generation :=
      at_generation_mono hsg hu id
    have hle_u : (u.slots id).generation ≤ (sg.slots id).generation := by
      by_contra hlt
      exact hnrel (Step.CtaBar.released_of_generation_lt (phase := (sg.slots id).generation) hu
        (by omega))
    have hgtg : (tg.slots id).generation = (sg.slots id).generation := by
      have h1 := at_generation_mono hAtg hu id
      rcases CtaBarrier.perform_slot (id := id) htg with ⟨h2, -⟩ | h2 <;> omega
    have hperfg : arrive L.block sg id (g % L.block / 32) none = .ok tg := by
      simp only [Record.perform] at htg
      split_ifs at htg
      exact htg
    obtain ⟨hexg, hwgt⟩ := arrive_pending hperfg hwarps hgtg
    have higl := (List.getElem?_eq_some_iff.mp hig).1
    have hrest := run_between (by omega : ig + 1 ≤ (Y.barriers c).length) hAtg hAtU
    rw [List.take_length] at hrest
    have hexu : (u.slots id).expected = some (warps L.block) :=
      run_expected hrest (by omega) hexg
    have hcu := (hl.some_info _ hexu).2.1
    obtain ⟨w', hw', hna⟩ : ∃ w' ∈ Finset.range (warps L.block), w' ∉ (u.slots id).arrived := by
      by_contra hcon
      push Not at hcon
      have hsub : Finset.range (warps L.block) ⊆ (u.slots id).arrived := hcon
      have := Finset.card_le_card hsub
      simp only [Finset.card_range] at this
      omega
    obtain ⟨i', lanes', s', t', q', j', pc', m', hj', hi', hs', hq', ht', hord', hle'⟩ :=
      hrw w' hw'
    have hF'le : (s'.slots id).generation ≤ (sg.slots id).generation := by
      have := at_generation_mono hs' hu id
      omega
    by_cases hFF : (s'.slots id).generation = (sg.slots id).generation
    · apply hna
      have hAt' := at_succ hi' hs' ht'
      have hg' : (t'.slots id).generation = (sg.slots id).generation := by
        have h1 := at_generation_mono hAt' hu id
        rcases CtaBarrier.perform_slot (id := id) ht' with ⟨h2, -⟩ | h2 <;> omega
      have hperf' : arrive L.block s' id w' none = .ok t' := by
        simp only [Record.perform] at ht'
        split_ifs at ht'
        exact ht'
      obtain ⟨-, hw'a⟩ := arrive_pending hperf' hwarps (by omega)
      have hi'l := (List.getElem?_eq_some_iff.mp hi').1
      have hrest' := run_between (by omega : i' + 1 ≤ (Y.barriers c).length) hAt' hAtU
      rw [List.take_length] at hrest'
      exact (CtaBarrier.run_slot (id := id) hrest').2 (by omega) hw'a
    · have hFlt : (s'.slots id).generation < (sg.slots id).generation := by omega
      have hrel' : Released L.block (Y.barriers c) id (s'.slots id).generation :=
        Step.CtaBar.released_of_generation_lt (phase := (s'.slots id).generation) hu (by omega)
      obtain ⟨ic, t, hAtt, hall'⟩ := completion_arrivals hu howners hi' hs' rfl hwarps hrel'
      have hno : ∀ j pc'', Y.get (c * L.block + g % L.block, j) ≠ some ⟨pc'', .exit⟩ := by
        intro j pc'' hj
        rw [hgeq, hget] at hj
        exact hnoexit j pc'' hj
      have hnot : g % L.block ∉ t.exited := not_exited_of_noExit hYX hc
        (show CtaBarrier.run L.block {} ((Y.barriers c).take (ic + 1)) = .ok t from hAtt) hno
      obtain ⟨i'', cnt'', lanes'', s'', hi'', hs'', hg''⟩ :=
        hall' _ hwg (warpLive_of_lane hgl hnot)
      obtain ⟨s₅, t₅, hat₅, hp₅⟩ := run_at_record hu hi''
      have hss₅ : s₅ = s'' := Except.ok.inj ((show CtaBarrier.run L.block {}
        ((Y.barriers c).take i'') = .ok s₅ from hat₅).symm.trans hs'')
      subst hss₅
      have hperf₅ : arrive L.block s₅ id (g % L.block / 32) cnt'' = .ok t₅ := by
        have hp₅' := hp₅
        simp only [Record.perform] at hp₅'
        split_ifs at hp₅'
        exact hp₅'
      obtain ⟨-, -, -, -, n'', hn'', -⟩ := arrive_ok_info hperf₅
      have hnn : n'' = warps L.block :=
        same_gen_target hu hi'' hat₅ hg'' hi' hs' rfl hn'' hwarps
      have hcnt'' : cnt'' = none := by
        rcases hprot i'' (g % L.block / 32) cnt'' lanes'' hi'' with h | ⟨hc2, -, -⟩
        · exact h
        · exfalso
          rw [hc2] at hn''
          have h3 := Except.ok.inj (hn''.symm.trans hcD)
          exact hnD (h3 ▸ hnn)
      subst hcnt''
      -- `g`'s lane is in this record
      obtain ⟨hnum, -, hlanes⟩ := perform_arrival_lanes hp₅
      obtain ⟨q, hq, hq1⟩ := List.mem_map.mp (hlanes (g % L.block) hgl rfl
        (not_exited_of_noExit hYX hc hat₅ hno))
      obtain ⟨-, hq2, pcq, mq, hqb⟩ := (hYX.ctaBar.2 c hc).2.1 _ (List.mem_of_getElem? hi'') q hq
      obtain ⟨-, -, -, -, hord'', -⟩ := record_ordinal hYX hc hu hi'' hat₅ hq
      have hq2g : q.2.1 = g := by rw [hq2, hq1, hgeq]
      have hqe : q.2 = (g, q.2.2) := Prod.ext hq2g rfl
      rw [hqe] at hqb
      rw [hq2g, htr] at hord''
      have hlp := phased_run hD hcard hnD hcD (hprot.take i'') hat₅
      have hstartF : start ≤ (s₅.slots id).generation := by
        rw [hg'']
        have := hstart w' hw'
        omega
      have hso : start ≤ idArrivals ((Y.barriers c).take i'') id (g % L.block / 32) :=
        ((hlp.early _ hwg (warpLive_of_lane hgl (not_exited_of_noExit hYX hc hat₅ hno))).2
          hstartF)
      have hj'' := hone q.2.2 pcq mq (by rw [← hget]; exact hqb) (by rw [← hord'']; exact hso)
      rw [hj''] at hord''
      have hlt : i'' < ig := by
        by_contra hge
        have := at_gen_mono (id := id) (by omega : ig ≤ i'') hsg hat₅
        omega
      have h1 := idArrivals_take_succ hi''
      have h2 := idArrivals_take_mono (id := id) (w := g % L.block / 32) (h := Y.barriers c)
        (by omega : i'' + 1 ≤ ig)
      omega
  -- `g`'s arrival is in a released generation
  have hid := hG.id_lt
  have hk : CtaBarArrivalK L Y (g, (X.tr g).length - 1) (id + 16 * (sg.slots id).generation) := by
    refine CtaBarArrivalK.of_generation hYX.ctaBar hg hid ?_
    exact ⟨ig, sg, g % L.block / 32, none, lanesg, qg, hig, hsg, hqg, rfl, tg, htg⟩
  have hkey : CtaBarK L Y (g, (X.tr g).length - 1) (id + 16 * (sg.slots id).generation) :=
    hYX.ctaBarK_of_arrival hK.out hk
  have hmod : (id + 16 * (sg.slots id).generation) % 16 = id := by omega
  have hdivG : (id + 16 * (sg.slots id).generation) / 16 = (sg.slots id).generation := by omega
  have hdone : CtaBarDone L Y (g / L.block) (id + 16 * (sg.slots id).generation) := by
    unfold CtaBarDone
    rw [hmod, hdivG]
    exact hrelF
  exact ⟨Y, hY, htr, released_of_key hYX.ctaBar htr hlast hkey hdone⟩

end Final

end

end PTX.NamedBar
