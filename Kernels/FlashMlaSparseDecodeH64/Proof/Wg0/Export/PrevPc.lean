-- SPDX-License-Identifier: Apache-2.0
-- domain: valid-rows
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.W0Value
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MbarRows.Base
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.UbBefore
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Control.SuccPc
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.StepInto
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.RegTime
import Lemmas.Kernel.UbLast
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.SuccRst
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.OkSite

@[expose] public section

/-! # The event before an event of a block's body

The pcs of the sites between the score loads (pc 278) and the vote (pc 578): a lane's event at
such a pc is preceded by an event at one of the pcs of `w0Prev` (the chain's step relation `succOk`
of the data machine, read off by a table over the sites). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow MbarRow

noncomputable section

/-- The pcs of the sites of a block's body: from the score loads to the closing arrival. -/
def w0BodyPcs : List Nat :=
  [278, 280, 283, 285, 286, 287, 289, 403, 413, 423, 433, 443, 453, 463, 473, 475,
    477, 482, 487, 492, 497, 502, 507, 512, 566, 569, 571, 572, 578, 704, 705, 706, 707, 711,
    716, 717, 814, 815, 817, 818, 915, 916, 918, 919, 1016, 1017, 1019, 1020, 1117, 1118,
    1119, 1120, 1122]

/-- Whether `p` is a pc of the body. -/
def w0Body (p : Nat) : Bool := p ∈ w0BodyPcs

/-- **The lane's events up to `N` are no undefined behaviour** (an alive prefix). -/
def LaneAlive (X : Execution) (g N : Nat) : Prop :=
  ∀ j f, X.get (g, j) = some f → j ≤ N → ∀ x, f.kind ≠ .ub x

theorem LaneAlive.of_noUb {X : Execution} (h : ¬ HasUb X) (g N : Nat) : LaneAlive X g N :=
  fun _ _ hf _ => noUb_kind h hf

/-- The events up to an event, itself included, are no undefined behaviour. -/
theorem LaneAlive.of_get {X : Execution} {g k : Nat} {e : Event} (hal : LaneUbFree X g k)
    (he : X.get (g, k) = some e) (hub : ∀ u, e.kind ≠ .ub u) : LaneAlive X g k :=
  fun j f hf hj x => by
    rcases Nat.lt_or_eq_of_le hj with h | rfl
    · exact hal.ne h hf x
    · obtain rfl := Option.some.inj (hf.symm.trans he)
      exact hub x

/-- The pcs of the events that can come right before an event of the body at pc `p`. -/
def w0Prev (p : Nat) : List Nat :=
  if p = 278 ∨ p = 283 then [275]
  else if p = 280 then [278] else if p = 285 then [283]
  else if p = 286 then [280, 285] else if p = 287 then [286] else if p = 289 then [287]
  else if p = 403 then [289]
  else if 413 ≤ p ∧ p ≤ 473 then [p - 10]
  else if p = 475 then [473] else if p = 477 then [475, 477]
  else if 482 ≤ p ∧ p ≤ 512 then [p - 5, p]
  else if p = 566 then [512] else if p = 569 then [566] else if p = 571 then [569]
  else if p = 572 then [571] else if p = 578 then [572]
  else if 704 ≤ p ∧ p ≤ 707 then [if p = 704 then 578 else p - 1, p]
  else if p = 711 then [707] else if p = 716 then [711] else if p = 717 then [716]
  else if p = 814 then [717] else if p = 815 then [814] else if p = 817 then [815]
  else if p = 818 then [817] else if p = 915 then [818] else if p = 916 then [915]
  else if p = 918 then [916] else if p = 919 then [918] else if p = 1016 then [919]
  else if p = 1017 then [1016] else if p = 1019 then [1017] else if p = 1020 then [1019]
  else if p = 1117 then [1020] else if p = 1118 then [1117] else if p = 1119 then [1118]
  else if p = 1120 then [1119, 707] else if p = 1122 then [1120] else []

namespace Wg0
open Wg0.Data

set_option maxRecDepth 100000 in
private theorem prev_tbl : ∀ s ∈ allSites, ∀ s' ∈ allSites, ∀ el ∈ [0, 1, 4],
    succOk {site := s, el := el} {site := s'} = true → w0Body s'.pc = true →
      s.pc ∈ w0Prev s'.pc := by decide +kernel

private theorem body_site : ∀ p ∈ w0BodyPcs,
    ∃ s ∈ allSites, s.pc = p := by decide +kernel

private theorem body_inner : ∀ s ∈ allSites, w0Body s.pc = true → innerSite s = true := by
  decide +kernel

private theorem body_not_start : ∀ s ∈ allSites, w0Body s.pc = true →
    s ≠ .bar0 ∧ s ≠ .ebar0 := by decide +kernel

private theorem succOk_norm (c c' : Control.D) :
    succOk c c' = succOk {site := c.site, el := if c.el = 0 then 0 else if c.el + 1 < 4 then 1
      else 4} {site := c'.site} := by
  unfold succOk
  cases c.site <;> simp only [] <;> (split_ifs <;> simp_all)

private theorem from_arrS {P : Params} {L : Launch} {g : Nat} {c c' : Control.D} {f : Event}
    (h : Control.succ P L g (warpW L g) c f = some (some c')) (hc : c.site = .arrS)
    (hn : c'.site ≠ .bar0 ∧ c'.site ≠ .ebar0) : False := by
  simp only [Control.succ, hc] at h
  split at h <;> cases h <;> simp_all

private theorem prev_ok {c c' : Control.D} (h : succOk c c' = true)
    (hb : w0Body c'.site.pc = true) :
    c.site.pc ∈ w0Prev c'.site.pc := by
  rw [succOk_norm] at h
  refine prev_tbl _ (mem_allSites _) _ (mem_allSites _) _ ?_ h hb
  split_ifs <;> simp

end Wg0

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- **The event before an event of the body**: the event at index `j` of a lane of warpgroup 0
has a pc of `w0Prev` of the pc of the event after it (the prefix up to it is valid). -/
theorem w0_prev_pc (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hw : warp L g < 4) {j : Nat} {e' : Event}
    (he' : X.get (g, j + 1) = some e') (hub : ∀ f, e'.kind ≠ .ub f) (hb : w0Body e'.pc = true)
    (hv : W0Valid P.scale ((X.tr g).take (j + 1))) :
    ∃ f, X.get (g, j) = some f ∧ f.pc ∈ w0Prev e'.pc := by
  obtain ⟨s, -, hsp⟩ := Wg0.body_site e'.pc (by simpa [w0Body] using hb)
  have hs : ∀ s' : Wg0.Site, s'.pc = e'.pc → s' = s := fun s' h =>
    Wg0.site_pc_inj (h.trans hsp.symm)
  have hbs : w0Body s.pc = true := by rw [hsp]; exact hb
  have hge : 103 ≤ e'.pc := by
    simp only [w0Body, w0BodyPcs, List.mem_cons, List.not_mem_nil, or_false,
      decide_eq_true_eq] at hb
    omega
  obtain ⟨f, c, d, hf, hpcf, hds, hsucc, hc⟩ := Wg0.w0_step_into_hub hp hX hFw hw he' hub hge hv hs
    (Wg0.body_inner s (Wg0.mem_allSites s) hbs)
  refine ⟨f, hf, ?_⟩
  rcases hc with hc | hc
  · refine (Wg0.from_arrS hsucc hc ?_).elim
    rw [hds]
    exact Wg0.body_not_start s (Wg0.mem_allSites s) hbs
  · have := Wg0.prev_ok hc (by rw [hds]; exact hbs)
    rw [← hpcf, hds, hsp] at *
    simpa [hsp] using this

end

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
