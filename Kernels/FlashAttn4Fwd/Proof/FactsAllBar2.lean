-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.FactsAllCross
public import Kernels.FlashAttn4Fwd.Proof.SafeFacts
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsBar2
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsMmaBase
public import Kernels.FlashAttn4Fwd.Proof.Thread.MmaCountsSite
public import Lemmas.Protocol.NamedBarArrive

@[expose] public section

/-! # Barrier 2's sites and generations

The field `bar2ArriveLast` of `ThreadInputs`.

* **The events** (`bar2_event`). An event on barrier 2 is a thread's of warps 0-12
  (`Cross.bar_warp13`). The MMA warp's are its `bar.sync 2, 416` at its sites `bar0` (PTX 544, no
  earlier event on barrier 2) and `bar1` (PTX 1117, one earlier; `Mma.bar2_site`,
  `Mma.Counts.bar2`). A softmax or correction thread's are its `bar.sync 2, 416` at its site
  `bar0` (PTX 1207 or 3755, none earlier) and its `bar.arrive 2, 416` at its site `barEnd` (PTX
  3749 or 4895, one earlier; its `Ev`, with the counts `bar2Sync`, `bar2Arrive`).
* **Last arrival** (`bar2ArriveLast`). A later event of the thread on barrier 2 would have at least
  two earlier ones (`Stats.barOrd_lt`), which no barrier-2 event has. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Flow PTX.Proof

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

namespace Bar2

section
variable (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
include hpre hX

/-- A softmax or correction thread's event that does not end it fires at a role state, with the
role's counts, the event of its site and the site's position. -/
theorem sc_event {g k : Nat} {e : Event} (hw : warpOf L g < 12)
    (he : X.get (g, k) = some e) (hend : ¬ Ends e) :
    ((∀ x ∈ (X.tr g).take k, Prologue.ProKind x.kind) ∧ Prologue.ProKind e.kind) ∨
    (∃ d, Softmax.Counts L g d ((X.tr g).take k) ∧ Softmax.Ev L g d e ∧ e.pc = d.site.pc) ∨
    (∃ d, Correction.Counts L g d ((X.tr g).take k) ∧ Correction.Ev L g d e ∧
      e.pc = d.site.pc) := by
  have hg := Frame.lt_of_get hX he
  obtain ⟨d, t, ins, u, hσ, hJ, hat, hi, hc, hf⟩ :=
    Cross.event_cont hpre hX (tracked hpre hX) (fun g hg => roleJ_run hpre hg) he hend
  have hpc := fires_pc hf
  rcases d with p | r
  · have hat' : At t p.site.pc (Prologue.facts L g p) :=
      ⟨hat.1, hat.2.1, hat.2.2.1, hat.2.2.2.1, hat.2.2.2.2⟩
    rcases Prologue.event_cases hpre hat' hc hf with h | ⟨⟨f, hf'⟩, -⟩
    · exact .inl ⟨hJ.1, h.proKind⟩
    · exact absurd (.inl ⟨f, hf'⟩) hend
  have hk := Cross.role_of_state hpre hX hg hσ
  cases r with
  | softmax s => exact .inr (.inl ⟨s, hJ, Softmax.site_event hpre hg hi hat hc hf, hpc⟩)
  | corr c => exact .inr (.inr ⟨c, hJ, Correction.site_event hpre hg hi hat hc hf, hpc⟩)
  | _ => simp only [Role.kind, RoleKind.Warp] at hk; omega

/-- **An event on barrier 2**: a first `bar.sync` at PTX 544, 1207 or 3755, the MMA warp's second
`bar.sync` at PTX 1117, or a second-event `bar.arrive` at PTX 3749 or 4895. -/
theorem bar2_event {g k pc : Nat} {cnt : Option Nat} {m : BarMode}
    (he : X.get (g, k) = some ⟨pc, .bar 2 cnt m⟩) :
    (m = .sync ∧ pc ∈ [544, 1207, 3755] ∧ barOrd X g k 2 = 0) ∨
    (m = .sync ∧ pc = 1117 ∧ barOrd X g k 2 = 1) ∨
    (m = .arrive ∧ pc ∈ [3749, 4895] ∧ barOrd X g k 2 = 1) := by
  have ht := tracked hpre hX
  have hlen : k < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  have hend : ¬ Ends ⟨pc, .bar 2 cnt m⟩ := by rintro (⟨f, hf⟩ | hf) <;> cases hf
  have h13 := Cross.bar_warp13 hpre hX ht he
  by_cases h12 : warpOf L g = 12
  · obtain ⟨d, t, ins, u, -, hJ, -, -, -, -, hc, hf⟩ :=
      mma_state_cont hpre hX ht he h12 (by simp [Prologue.ProKind]) hend
    obtain ⟨hb, hk⟩ := Mma.bar2_site hpre hc hf
    have hid : Execution.isBarId 2 ⟨pc, .bar 2 cnt m⟩ = true := by simp [Execution.isBarId]
    have hkind := hk hid
    simp only [Kind.bar.injEq] at hkind
    obtain ⟨-, rfl, rfl⟩ := hkind
    have hpc := fires_pc hf
    have hord : barOrd X g k 2 = Mma.bar2A d.site := hJ.bar2
    rw [hid] at hb
    simp only at hpc
    obtain ⟨site, i, tt, base, pro⟩ := d
    cases site <;> simp [Mma.bar2Ev] at hb
    · exact .inl ⟨rfl, by rw [hpc]; exact (by decide : Mma.Site.bar0.pc ∈ [544, 1207, 3755]),
        by rw [hord]; rfl⟩
    · exact .inr (.inl ⟨rfl, by rw [hpc]; rfl, by rw [hord]; rfl⟩)
  have hw : warpOf L g < 12 := by omega
  have hsplit := Cross.barOrd_split hpre hX ht hw hlen
  rcases sc_event hpre hX hw he hend with ⟨-, hp⟩ | ⟨d, hJ, hev, hpc⟩ | ⟨d, hJ, hev, hpc⟩
  · simp [Prologue.ProKind] at hp
  · have hb := hJ.bar2
    simp only at hpc
    unfold Softmax.Ev at hev
    have hne : Softmax.kOf L g + 3 + 4 * Softmax.stOf L g ≠ 2 := by omega
    cases hs : d.site <;> simp only [hs] at hev hpc <;>
      simp only [Softmax.bar2Sync, Softmax.bar2Arrive, hs] at hb <;>
      simp only [Kind.bar.injEq, reduceCtorEq, exists_false] at hev
    case bar0 =>
      obtain ⟨-, -, rfl⟩ := hev
      exact .inl ⟨rfl, by rw [hpc]; decide, by omega⟩
    case gen => exact absurd hev.1.symm hne
    case barEnd =>
      obtain ⟨-, -, rfl⟩ := hev
      exact .inr (.inr ⟨rfl, by rw [hpc]; decide, by omega⟩)
  · have hb := hJ.bar2
    simp only at hpc
    obtain ⟨-, hev⟩ := hev
    have hne : ∀ st : Fin 2, Correction.kOf L g + 3 + 4 * st.val ≠ 2 := fun _ => by omega
    cases hs : d.site <;> simp only [hs] at hev hpc <;>
      simp only [Correction.bar2Sync, Correction.bar2Arrive, hs] at hb <;>
      simp only [Kind.bar.injEq, reduceCtorEq, false_and, exists_false] at hev
    case bar0 =>
      obtain ⟨-, -, rfl⟩ := hev
      exact .inl ⟨rfl, by rw [hpc]; decide, by omega⟩
    case sync st _ => exact absurd hev.1.symm (hne st)
    case barEnd =>
      obtain ⟨-, -, rfl⟩ := hev
      exact .inr (.inr ⟨rfl, by rw [hpc]; decide, by omega⟩)

/-- **Barrier 2's `bar.arrive` is its thread's last event on barrier 2.** -/
theorem bar2ArriveLast : Stats.Bar2ArriveLast X := by
  intro g i j pc cnt ev hi hij hj
  by_contra hb
  rw [Bool.not_eq_false] at hb
  obtain ⟨evpc, evk⟩ := ev
  obtain ⟨c', m', rfl⟩ : ∃ c' m', evk = .bar 2 c' m' := by
    cases evk <;> simp_all [Execution.isBarId]
  have hlt := Stats.barOrd_lt hi hij
  rcases bar2_event hpre hX hi with ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, -, h1⟩
  · cases h
  · cases h
  rcases bar2_event hpre hX hj with ⟨-, -, h2⟩ | ⟨-, -, h2⟩ | ⟨-, -, h2⟩ <;> omega

end

end Bar2

end
end PTX.Kernels.FlashAttn4Fwd.Proof
