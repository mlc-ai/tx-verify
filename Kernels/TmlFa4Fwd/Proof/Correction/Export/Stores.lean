-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.CorrWarp.ReadPayloads
public import Kernels.TmlFa4Fwd.Proof.Common.DataState
import Kernels.TmlFa4Fwd.Proof.Common.DataSound
public import Kernels.TmlFa4Fwd.Proof.CorrWarp.NoUb
public import Kernels.TmlFa4Fwd.Proof.Correction.Export.Tmem
import Kernels.TmlFa4Fwd.Proof.Correction.StoreValsR

@[expose] public section

/-! # A correction lane's data machine from the reads before a position

A lane whose statistics reads and Tensor Memory loads before a position `K` returned what the data
machine follows is at a data state up to `K` (`corr_alive`). Its rescale stores are then numbers
(`corr_st_f32`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Correction
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- The sites of the statistics reads. -/
def Site.stat : Site → Bool
  | .rscale _ | .fsum _ | .fmax _ => true
  | _ => false

/-- **The statistics reads of a lane before a position** returned the payloads the data machine
follows. -/
def StatTo (X : Execution) (g K : Nat) : Prop :=
  ∀ i < K, ∀ (s : Site) e, X.get (g, i) = some e → e.pc = s.pc → s.stat = true →
    CorrWarp.ReadPayload s e.kind

/-- **The Tensor Memory loads of a lane before a position** returned numbers. -/
def LoadTo (X : Execution) (g K : Nat) : Prop :=
  ∀ i < K, ∀ a vals, X.TLd (g, i) a vals .s32x32b → ∀ v ∈ vals, ∃ x : ℝ, v = .float .f32 x

theorem flN_some {n : Nat} {vals : List Value} (hl : vals.length = n)
    (h : ∀ v ∈ vals, ∃ x : ℝ, v = .float .f32 x) : (flN n vals).isSome := by
  unfold flN
  rw [ite_eq_left]
  · rfl
  rw [List.all_eq_true]
  intro i hi
  have hi : i < vals.length := by rw [hl]; exact List.mem_range.mp hi
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
  obtain ⟨x, hx⟩ := h _ (List.getElem_mem hi)
  rw [hx]
  rfl

/-- A data state over a correction control state. -/
theorem data_of_control (hp : Pre p L m) {k : Nat} {σ : (threadD p L g).D} {dc : Control.D}
    {n : Cls → Nat} (hs : Frame.stateAt (threadD p L) X g k = some (some σ))
    (hc : Frame.stateAt (thread p L) X g k = some (some (CorrWarp.cinj p L g dc n))) :
    ∃ d, σ = (.inr ⟨.correction, d⟩, n) ∧ Control.erase d = dc := by
  have h := control_of_data hp hs
  rw [hc] at h
  simp only [Option.some.injEq] at h
  obtain ⟨s, n'⟩ := σ
  obtain ⟨h1, rfl⟩ := Prod.ext_iff.mp h
  cases s with
  | inl s => cases h1
  | inr a =>
    obtain ⟨i, d⟩ := a
    have hi : Role.correction = i := by
      have := congrArg (fun x => Sum.elim (fun _ => none) (fun y => some y.1) x) h1
      simpa [CorrWarp.cinj, eraseThread, eraseDispatch] using this
    subst hi
    refine ⟨d, rfl, ?_⟩
    simp only [eraseThread, eraseDispatch, Sum.inr.injEq, Sigma.mk.injEq, heq_eq_eq,
      true_and] at h1
    exact h1.symm

variable (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow p L X)
  (hw : 8 ≤ Prologue.warpIndex L g) (hw1 : Prologue.warpIndex L g ≤ 11)
include hp hX hFw hw hw1

/-- **The data reads before a position**, from the statistics reads and the loads. -/
theorem data_to {K : Nat} (hS : StatTo X g K) (hL : LoadTo X g K) :
    CorrWarp.DataTo p L X g K := by
  intro i hi d n e he hs _ hd
  have hpc : e.pc = d.site.pc := Frame.event_pc (fun g hg => threadD_sound hp hg) hX he hs
  have hload : ∀ a vals sh, e.kind = .tc (.ld a vals sh) →
      (∀ v ∈ vals, ∃ x : ℝ, v = .float .f32 x) ∧
      ((∃ st c, d.site = .rld st c ∧ vals.length = 16) ∨
        ∃ st c, d.site = .fld st c ∧ vals.length = 8) := by
    intro a vals sh hk
    have hl : X.TLd (g, i) a vals sh := ⟨e.pc, by rw [← hk]; exact he⟩
    obtain ⟨dc, nc, r, ℓ, hσ, -, rfl, st, hst⟩ := corr_ld_state hp hX hFw hw hw1 hl
    refine ⟨hL i hi a vals hl, ?_⟩
    obtain ⟨d', hd', rfl⟩ := data_of_control hp hs hσ
    cases hd'
    rcases hst with ⟨c, h, -, hn⟩ | ⟨c, h, -, hn⟩
    · exact .inl ⟨st, c, h, hn⟩
    · exact .inr ⟨st, c, h, hn⟩
  have hr := hS i hi d.site e he hpc
  obtain ⟨s, v, k⟩ := d
  cases s
  case rscale | fsum | fmax =>
    intro a bs hk
    have := hr rfl
    simpa only [hk, CorrWarp.ReadPayload] using this
  case rld st c =>
    intro a vals sh hk
    obtain ⟨hv, ⟨_, _, _, hn⟩ | ⟨_, _, h, _⟩⟩ := hload a vals sh hk
    · exact flN_some hn hv
    · cases h
  case fld st c =>
    intro a vals sh hk
    obtain ⟨hv, ⟨_, _, h, _⟩ | ⟨_, _, _, hn⟩⟩ := hload a vals sh hk
    · cases h
    · exact flN_some hn hv
  all_goals cases hd

/-- **The data state of a correction lane** over its control state, with its invariant. -/
theorem corr_alive {k : Nat} (hS : StatTo X g k) (hL : LoadTo X g k) {dc : Control.D}
    {n : Cls → Nat} {e : Event} (he : X.get (g, k) = some e)
    (hc : Frame.stateAt (thread p L) X g k = some (some (CorrWarp.cinj p L g dc n))) :
    ∃ d : D, Frame.stateAt (threadD p L) X g k = some (some (.inr ⟨.correction, d⟩, n)) ∧
      Control.erase d = dc ∧ Ref p L g (d, CorrWarp.rc n) := by
  have hlen : k < (X.tr g).length := by
    obtain ⟨h, _⟩ := List.getElem?_eq_some_iff.mp (show (X.tr g)[k]? = some e from he)
    exact h
  obtain ⟨σ, hs, hR⟩ := CorrWarp.alive hp hX ⟨hw, hw1⟩ (Frame.lt_of_get hX he) rfl
    (data_to hp hX hFw hw hw1 hS hL) k le_rfl hlen
  obtain ⟨d, rfl, hd⟩ := data_of_control hp hs hc
  exact ⟨d, hs, hd, hR d n rfl⟩

/-- **A rescale store writes numbers**, once the reads before it returned numbers. -/
theorem corr_st_f32 {k a : Nat} {vals : List Value} {sh : TcShape} (hS : StatTo X g k)
    (hL : LoadTo X g k) (ht : X.TSt (g, k) a vals sh) : ∀ v ∈ vals, ∃ x : ℝ, v = .float .f32 x := by
  obtain ⟨dc, n, -, -, hσ, -, -, st, c, hsite, -, -⟩ := corr_st_state hp hX hFw hw hw1 ht
  obtain ⟨pc, he⟩ := ht
  obtain ⟨d, hs, rfl, -⟩ := corr_alive hp hX hFw hw hw1 hS hL he hσ
  obtain ⟨t, ins, o, hat, -, hc, hf⟩ :=
    Frame.fired_site (fun g hg => threadD_sound hp hg) hX he hs
  obtain ⟨s, v, j⟩ := d
  change s = _ at hsite
  subst hsite
  rw [rst_val hat hc hf rfl]
  intro v hv
  obtain ⟨i, -, rfl⟩ := List.mem_map.mp hv
  exact ⟨_, rfl⟩

end
end PTX.Kernels.TmlFa4Fwd.Proof.Correction
