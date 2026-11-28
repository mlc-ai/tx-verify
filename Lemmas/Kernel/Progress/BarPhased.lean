-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Protocol.NamedBarGenRelease
public import Lemmas.Protocol.NamedBarPhaseKeys
public import Lemmas.Step.CtaBarFinishExit

@[expose] public section

/-!
# Releasing a generation of a phased barrier from its arrivals

The library's `released_of_all_arrived` replays a history that follows one group's protocol
(`NamedBar.Protocol`). Named barrier 0 of the kernel has several groups in turn; its history
follows only the phased ledger of the resource (`NamedBar.Phased`, `NamedBarPhase.lean`), which
keeps, whatever the groups are, that an open generation with expected count `k` has fewer than
`k` arrived warps. That is enough for the release criterion:

* `perform_expected`, `run_expected` (not in the library): while the generation of a slot is
  unchanged, an open generation's `expected` count stays;
* `released_of_group`: if every warp of a set `P` of `n` warps has an arrival record with the
  count that targets `n` in generation `G`, then `G` is released.
-/

namespace PTX.NamedBar
open PTX CtaBarrier PTX.NamedBar.GenLedger

noncomputable section

variable {α : Type}

/-! ### The execution side: a phased barrier's `bar.sync` whose group has arrived -/

section Exec

variable {L : Launch} {X : Execution} {K : Kernel} {A : List Assumption} {mem0 : Mem0}
  {D : Finset Nat} {cD : Option Nat} {start nD id : Nat}

/-- **A recorded arrival's generation is its source ordinal** when its warp is a loop warp or its
ordinal is below `start`: the record, its state and the lane's event. -/
theorem recorded_generation (hX : Consistent L K A mem0 X) (hS : PhSources L X D cD start id)
    (hD : D ⊆ Finset.range (warps L.block)) (hcard : D.card = nD) (hnD : nD ≠ warps L.block)
    (hcD : target L.block cD = .ok nD) {e : EvId} {pc : Nat} {cnt : Option Nat} {m : BarMode}
    (he : X.get e = some ⟨pc, .bar id cnt m⟩) (hge : e.1 < L.threads)
    (hrec : e ∈ (X.barriers (e.1 / L.block)).flatMap Record.refs)
    (hgw : (e.1 % L.block) / 32 ∈ D ∨
      ((X.tr e.1).take e.2).countP (Execution.isBarId id) < start) :
    ∃ i lanes s t, (X.barriers (e.1 / L.block))[i]? =
        some (.arrival id ((e.1 % L.block) / 32) cnt lanes) ∧
      At L.block (X.barriers (e.1 / L.block)) i s ∧ (∃ q, (q, e) ∈ lanes) ∧
      (s.slots id).generation = ((X.tr e.1).take e.2).countP (Execution.isBarId id) ∧
      Record.perform L.block s (.arrival id ((e.1 % L.block) / 32) cnt lanes) = .ok t := by
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
    obtain ⟨hql, -, hqw, -, hord, -⟩ := record_ordinal hX hc hlast hk hs hq
    have hqe' : q.2.1 = e.1 := by rw [hqe]
    have hqe2 : q.2.2 = e.2 := by rw [hqe]
    have hmod : e.1 % L.block = q.1 := by
      have h1 := Nat.div_add_mod e.1 L.block
      rw [hqe'] at hq2
      rw [Nat.mul_comm] at h1
      omega
    rw [hqe', hqe2] at hord
    have hprot := hS.protocol hX hc
    have hw : (e.1 % L.block) / 32 = w' := by rw [hmod, hqw]
    have hgen := gen_of_record hD hcard hnD hcD hprot hs ht (by
      rw [hord, ← hw]
      exact hgw)
    refine ⟨k, lanes, s, t, ?_, hs, ⟨q.1, by rw [← hqe]; exact hq⟩, ?_, ?_⟩
    · rw [hw]; exact hk
    · rw [← hord, hgen]
    · rw [hw]; exact ht

variable [hK : Fact K.NoBarArrive]

/-- **A `bar.sync` of a phased barrier whose group has arrived is released in an extension.**
In a maximal execution with no CTA barrier fault, let thread `g`'s last event be its `bar.sync`
on barrier `id` with operand `count` of group `p` (`Shape`), whose arrivals follow `PhSources`
for the loop group `D`, and let every participant lane of its CTA have made its arrival with
that operand and `g`'s ordinal `G`. If the participants are loop warps or `G < start`, a maximal
execution with the same traces releases `g`: every participant's record is in generation `G`
(`recorded_generation`), which is therefore released (`released_of_group`). -/
theorem sync_release_phased {sel : Nat → Bool} (hmax : Maximal L K A mem0 X)
    (hA : Assumption.WfStep sel L K mem0 A)
    (hf : ∀ Y, Consistent L K A mem0 Y → ¬ CtaBarFault L Y)
    (hD : D ⊆ Finset.range (warps L.block)) (hcard : D.card = nD) (hnD : nD ≠ warps L.block)
    (hcD : target L.block cD = .ok nD) (hS : PhSources L X D cD start id)
    {count : Option Nat} {p : Finset Nat} (hG : Shape L count p id) {g pc : Nat}
    (hg : g < L.threads) (hgp : g % L.block / 32 ∈ p)
    (hlast : X.IsBarrier (g, (X.tr g).length - 1) id count pc)
    (hgw : ∀ w ∈ p, w ∈ D ∨
      ((X.tr g).take ((X.tr g).length - 1)).countP (Execution.isBarId id) < start)
    (hlane : ∀ y, y < L.block → y / 32 ∈ p → ∃ j pc m,
      X.get (g / L.block * L.block + y, j) = some ⟨pc, .bar id count m⟩ ∧
      ((X.tr (g / L.block * L.block + y)).take j).countP (Execution.isBarId id) =
        ((X.tr g).take ((X.tr g).length - 1)).countP (Execution.isBarId id)) :
    ∃ Y, Maximal L K A mem0 Y ∧ Y.tr = X.tr ∧ Step.Released L Y g := by
  have hc := cta_lt hg
  have hb := block_pos_of_thread_lt hg
  set c := g / L.block with hcdef
  set G := ((X.tr g).take ((X.tr g).length - 1)).countP (Execution.isBarId id) with hGdef
  obtain ⟨Y, hY, htr, -, hall⟩ := warps_record hA hf hG hc hlane p.toList
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
  -- the record of a lane's arrival of ordinal `G`: its generation is `G`
  have hrecgen : ∀ y, y < L.block → ∀ j pc' m, y / 32 ∈ p →
      X.get (c * L.block + y, j) = some ⟨pc', .bar id count m⟩ →
      ((X.tr (c * L.block + y)).take j).countP (Execution.isBarId id) = G →
      ∃ i lanes s t, (Y.barriers c)[i]? = some (.arrival id (y / 32) count lanes) ∧
        At L.block (Y.barriers c) i s ∧ (∃ q, (q, (c * L.block + y, j)) ∈ lanes) ∧
        (s.slots id).generation = G ∧
        Record.perform L.block s (.arrival id (y / 32) count lanes) = .ok t := by
    intro y hy j pc' m hyp hj hord
    have hyg : c * L.block + y < L.threads := cta_thread_lt hc hy
    have hdiv : (c * L.block + y) / L.block = c := (lane_cta (c := c) hb hy).1
    have hmod : (c * L.block + y) % L.block = y := (lane_cta (c := c) hb hy).2
    have hrec := hall (y / 32) (Finset.mem_toList.mpr hyp) y hy rfl j pc' m count
      hj hord
    have hrec' : (c * L.block + y, j) ∈ (Y.barriers ((c * L.block + y) / L.block)).flatMap
        Record.refs := by rw [hdiv]; exact hrec
    obtain ⟨i, lanes, s, t, hi, hs, hq, hgen, ht⟩ := recorded_generation hYX hSY hD hcard hnD
      hcD
      (e := (c * L.block + y, j)) (by rw [hget]; exact hj) hyg hrec'
      (by
        rcases hgw (y / 32) hyp with h | h
        · exact .inl (by rw [hmod]; exact h)
        · exact .inr (by simp only [htr, hord]; exact h))
    simp only [hdiv, hmod, htr, hord] at hi hs hq hgen ht
    exact ⟨i, lanes, s, t, hi, hs, hq, hgen, ht⟩
  -- every participant warp has a record in generation `G`: `G` is released
  have hrel : Released L.block (Y.barriers c) id G := by
    refine released_of_group hu hl hG.target rfl hG.pos ?_
    intro w hw
    have hwb := hG.bound w hw
    have h0w : w * 32 / 32 = w := Nat.mul_div_cancel _ (by decide)
    obtain ⟨j, pcj, mj, hj, hord⟩ := hlane (w * 32) (by omega) (by rw [h0w]; exact hw)
    obtain ⟨i, lanes, s, t, hi, hs, -, hgen, -⟩ := hrecgen (w * 32) (by omega) j pcj mj
      (by rw [h0w]; exact hw) hj hord
    rw [h0w] at hi
    exact ⟨i, lanes, s, hi, hs, hgen⟩
  -- `g`'s arrival is in generation `G`
  have hgl : g % L.block < L.block := Nat.mod_lt _ hb
  have hgeq : c * L.block + g % L.block = g := by
    rw [hcdef, Nat.mul_comm]; exact Nat.div_add_mod g L.block
  have hlastg : X.get (c * L.block + g % L.block, (X.tr g).length - 1) =
      some ⟨pc, .bar id count .sync⟩ := by rw [hgeq]; exact hlast
  obtain ⟨i, lanes, s, t, hi, hs, hq, hgen, ht⟩ := hrecgen (g % L.block) hgl
    ((X.tr g).length - 1) pc .sync hgp hlastg (by rw [hgeq])
  have hid := hG.id_lt
  have hk : CtaBarArrivalK L Y (g, (X.tr g).length - 1) (id + 16 * G) := by
    refine CtaBarArrivalK.of_generation hYX.ctaBar hg hid ?_
    rw [hgeq] at hq
    obtain ⟨q, hq⟩ := hq
    exact ⟨i, s, g % L.block / 32, count, lanes, q, hi, hs, hq, hgen, t, ht⟩
  have hkey : CtaBarK L Y (g, (X.tr g).length - 1) (id + 16 * G) := hYX.ctaBarK_of_arrival hK.out hk
  have hmod : (id + 16 * G) % 16 = id := by omega
  have hdivG : (id + 16 * G) / 16 = G := by omega
  have hdone : CtaBarDone L Y (g / L.block) (id + 16 * G) := by
    unfold CtaBarDone
    rw [hmod, hdivG]
    exact hrel
  have hlastY : X.get (g, (X.tr g).length - 1) = some ⟨pc, .bar id count .sync⟩ := hlast
  exact ⟨Y, hY, htr, released_of_key hYX.ctaBar htr hlastY hkey hdone⟩

end Exec

end

end PTX.NamedBar
