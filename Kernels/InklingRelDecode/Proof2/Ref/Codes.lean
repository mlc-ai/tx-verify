-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof2.ProA.Ref
public import Kernels.InklingRelDecode.Proof.Thread.ScFence
public import Kernels.InklingRelDecode.Proof.Thread.EvDFires
public import Lemmas.Protocol.NamedBarSources
public import Lemmas.Flow.NotClc
public import Lemmas.Flow.NotBulk

@[expose] public section

/-! # Code facts for the first stage: barrier events, barrier 1's group, the prologue's order

* `bar_event_static`, `bar_one_static`: a barrier event of the kernel is `bar.sync b` without a
  count (`b < 16`) or `bar.sync 0, 128`; an event on barrier 1 is `barrier.sync 1` without a
  count. Read off the instruction at the event's position (the first tree's
  `Interface/BarStatic.lean`, needing no machine).
* `bar1_sources`, `bar1_shape`: barrier 1 has one group, the CTA's eight warps without a count,
  so the library's single-group lemmas (`Handoff.of_bar_upTo`) apply to it.
* `cross_fnc0`, `exit_from_bar18`: no step of the prologue goes from a site at or before its proxy
  fence (`fnc0`, pc 179) to one after it except the fence's own step, and only the last barrier
  (`bar18`, pc 573) steps to the prologue's exit (from the flat machine's `next_cross_fnc0`). -/

namespace PTX.Kernels.InklingRelDecode.Proof2
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.InklingRelDecode

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- The forms a named-barrier instruction of the kernel takes. -/
def barForm : Op → Bool
  | .barSync (.imm i) _ => decide (0 ≤ i ∧ i < 16)
  | .barSyncN (.imm 0) (.imm 128) _ => true
  | .barSync .. | .barSyncN .. | .barArrive .. => false
  | _ => true

theorem kernel_barForm : kernel.code.all (fun ins => barForm ins.op) = true := by
  decide +kernel

/-- **A barrier event is `bar.sync b` without a count (`b < 16`) or `bar.sync 0, 128`.** -/
theorem bar_event_static (hX : Consistent L kernel Assumptions.all m X) (hb : L.block ≠ 128)
    {i : EvId} {pc id : Nat} {cnt : Option Nat} {md : BarMode}
    (he : X.get i = some ⟨pc, .bar id cnt md⟩) :
    md = .sync ∧ ((cnt = none ∧ id < 16) ∨ (id = 0 ∧ cnt = some 128)) := by
  rcases get_source hX he with ⟨f, hf⟩ | ⟨t, ins, o, -, hc, hf⟩
  · cases hf
  · simp only at hc hf
    have hop := fires_bar_op hf (show (⟨pc, .bar id cnt md⟩ : Event).kind = .bar id cnt md from rfl)
    have hall := List.all_eq_true.mp kernel_barForm ins (List.mem_of_getElem? hc)
    cases hins : ins.op with
    | barSync b al =>
      rw [hins] at hf hall
      cases b with
      | imm v =>
        simp only [barForm, decide_eq_true_eq] at hall
        obtain ⟨n, rfl⟩ : ∃ n : Nat, v = n := ⟨v.toNat, (Int.toNat_of_nonneg hall.1).symm⟩
        have := Proof.EvD.fires_barSync_imm (by omega) hf
        simp only [Event.mk.injEq, Kind.bar.injEq, true_and] at this
        obtain ⟨rfl, rfl, rfl⟩ := this
        exact ⟨rfl, .inl ⟨rfl, by omega⟩⟩
      | _ => simp [barForm] at hall
    | barSyncN b c al =>
      rw [hins] at hf hall
      cases b with
      | imm v =>
        cases c with
        | imm w =>
          by_cases h0 : v = 0
          · by_cases h1 : w = 128
            · subst h0 h1
              have := Proof.EvD.fires_barSyncN_128 hb hf
              simp only [Event.mk.injEq, Kind.bar.injEq, true_and] at this
              obtain ⟨rfl, rfl, rfl⟩ := this
              exact ⟨rfl, .inr ⟨rfl, rfl⟩⟩
            · simp [barForm, h0, h1] at hall
          · simp [barForm, h0] at hall
        | _ => simp [barForm] at hall
      | _ => simp [barForm] at hall
    | barArrive b c al =>
      rw [hins] at hall
      simp [barForm] at hall
    | _ =>
      rw [hins] at hop
      simp [barOp] at hop

/-- **Every arrival on barrier 1 is a lane of a warp of the CTA passing no count.** -/
theorem bar1_sources (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X) :
    NamedBar.Sources L X none (Finset.range (CtaBarrier.warps L.block)) 1 := by
  intro e pc cnt ⟨md, he⟩ hg
  have hb : L.block = 256 := hp.block
  obtain ⟨-, h | ⟨h, -⟩⟩ := bar_event_static hX (by omega) he
  · refine ⟨?_, h.1⟩
    have : e.1 % L.block < 256 := by
      have := Nat.mod_lt e.1 (show L.block > 0 by omega)
      omega
    simp only [Finset.mem_range, CtaBarrier.warps, hb]
    omega
  · cases h

/-- **The group of barrier 1**: the eight warps without a count. -/
theorem bar1_shape (hp : Pre Q L m) :
    NamedBar.Shape L none (Finset.range (CtaBarrier.warps L.block)) 1 := by
  have hb : L.block = 256 := hp.block
  refine ⟨by simp [CtaBarrier.warps, hb], ?_, ?_, by decide⟩
  · rw [Finset.card_range]; rfl
  · intro w hw
    simp only [Finset.mem_range, CtaBarrier.warps, hb] at hw ⊢
    omega

/-- The third request word's load steps to the first election. -/
theorem ld2_succ {dt : Proof.ProA.Dat} {e : Event} {d' : ProA.D}
    (h : ProA.next0 L g ⟨.ld 2, dt⟩ e = some (some d')) : d'.site = .el 0 := by
  simp only [ProA.next0] at h
  split at h
  · split at h
    · split at h
      · split at h
        · simp only [Option.some.injEq] at h
          subst h
          rfl
        · cases h
      · cases h
    · cases h
  · cases h

/-- **Only the prologue's last barrier steps to its exit.** -/
theorem exit_from_bar18 {d d' : ProA.D} {e : Event} (h : ProA.next L g d e = some (some d'))
    (hx : d'.site = .exit) : d.site = .bar18 := by
  obtain ⟨s, dt⟩ := d
  by_cases hk : ProA.kill ⟨s, dt⟩ e = true
  · simp [ProA.next, hk] at h
  have h' : ProA.next0 L g ⟨s, dt⟩ e = some (some d') := by simpa [ProA.next, hk] using h
  by_contra hne
  simp only at hne
  by_cases h2 : s = .exit
  · subst h2; simp [ProA.next0] at h'
  by_cases h3 : s = .ld 2
  · subst h3
    rw [ld2_succ h'] at hx
    cases hx
  have key : ProA.next0 L g ⟨s, dt⟩ e = (Proof.ProA.next L g ⟨s.old, dt⟩ e).map
      (Option.map fun d'' => ⟨ProA.Site.ofOld d''.site, d''.dt⟩) := by
    cases s with
    | ld k => fin_cases k <;> first | rfl | exact absurd rfl h3
    | _ => first | rfl | exact absurd rfl hne | exact absurd rfl h2
  rw [key] at h'
  cases hn : Proof.ProA.next L g ⟨s.old, dt⟩ e with
  | none => rw [hn] at h'; cases h'
  | some o =>
    cases o with
    | none => rw [hn] at h'; cases h'
    | some d'' =>
      rw [hn] at h'
      simp only [Option.map_some, Option.some.injEq] at h'
      subst h'
      exact ProA.ofOld_ne_exit _ hx

/-- **No step of the prologue goes past its proxy fence except the fence's own.** -/
theorem cross_fnc0 {d d' : ProA.D} {e : Event} (h : ProA.next L g d e = some (some d'))
    (hs : d.site.pc ≤ 179) (hd : 179 < d'.site.pc) : d.site = .fnc0 := by
  obtain ⟨s, dt⟩ := d
  simp only at hs ⊢
  by_cases hk : ProA.kill ⟨s, dt⟩ e = true
  · simp [ProA.next, hk] at h
  have h' : ProA.next0 L g ⟨s, dt⟩ e = some (some d') := by simpa [ProA.next, hk] using h
  by_cases h1 : s = .bar18
  · subst h1; exact absurd hs (by decide)
  by_cases h2 : s = .exit
  · subst h2; simp [ProA.next0] at h'
  by_cases h3 : s = .ld 2
  · subst h3
    rw [ld2_succ h'] at hd
    exact absurd hd (by decide)
  have hf := ProA.next0_flat h1 h2 h3 h'
  have hx' : d'.site ≠ .exit := fun hx => h1 (exit_from_bar18 h hx)
  have hf' : Proof.ProA.next L g ⟨s.old, dt⟩ e = some (some (ProA.D.old d')) := hf
  have hc := Proof.ProA.next_cross_fnc0 hf' (by rw [← ProA.pc_old s h2]; exact hs)
    (by show Proof.ProA.Site.fnc0.pc < d'.site.old.pc; rw [← ProA.pc_old _ hx']; exact hd)
  rw [← ProA.ofOld_old s h2, hc]
  rfl

end
end PTX.Kernels.InklingRelDecode.Proof2
