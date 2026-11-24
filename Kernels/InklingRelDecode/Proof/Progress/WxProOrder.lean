-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.Lk5BAlign
public import Kernels.InklingRelDecode.Proof.Interface.ClassCopyPage

@[expose] public section

/-!
# The prologue's barrier-0 count orders its sites

The prologue is straight-line code: its sites are in program order (`ProA.Site.ctorIdx`), and its
time is `100 + ctorIdx` (`Wt.proT`). The number of its `bar.sync 0, 128` before a site is
`proOff` (`Lk5B.proOff_next`): 0 up to the partition's `bar2`, `1 + 5 j + o` in block `j`, and
`1 + 5 nb` after the blocks, where `nb` is the number of blocks the thread runs (`nbOf`). A site of
block `j` is reached only when `j < nb` (`ProA.Gate`).

* `off_eq`, `inc_eq`: `proOff` and `proInc` as functions of the constructor index;
* `gate_blk`: the gate bounds the block of a block site;
* `pro_lt`, `pro_le`: of two gated sites with one block count, the second a barrier-0 site, a
  count (plus the first site's own barrier-0 event) at most the second's is an earlier site.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Progress.Wx
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof
open PTX.Kernels.InklingRelDecode.Proof.Lk5B

noncomputable section
set_option maxRecDepth 100000

/-- The offset of a site within its block, by its index in the block. -/
def bo (r : Nat) : Nat :=
  if r = 0 then 0 else if r ≤ 3 then 1 else if r ≤ 7 then 2 else if r ≤ 11 then 3
  else if r ≤ 14 then 4 else 5

/-- `proOff` by the constructor index `n` and the block count `N`. -/
def off (n N : Nat) : Nat :=
  if n ≤ 29 then 0 else if n < 81 then 1 + 5 * ((n - 30) / 17) + bo ((n - 30) % 17)
  else 1 + 5 * N

/-- The barrier sites of a block, by their index in the block. -/
def bbar (r : Nat) : Bool := r == 0 || r == 3 || r == 7 || r == 11 || r == 14

/-- `proInc` by the constructor index. -/
def binc (n : Nat) : Nat :=
  if n = 29 then 1 else if 30 ≤ n ∧ n < 81 ∧ bbar ((n - 30) % 17) = true then 1 else 0

theorem off_eq (L : Launch) (g : Nat) (d : ProA.D) :
    proOff L g d = off d.site.ctorIdx (nbOf L g d.dt) := by
  obtain ⟨s, dt⟩ := d
  cases s <;> simp only [proOff, blkOff] <;> simp (config := { decide := true }) [off, bo]

theorem inc_eq (s : ProA.Site) : proInc s = binc s.ctorIdx := by
  cases s <;> rfl

/-- **A site of block `j` is reached only when the thread runs block `j`.** -/
theorem gate_blk {L : Launch} {g : Nat} {s : ProA.Site} {dt : ProA.Dat}
    (hG : ProA.Gate L g s dt) (h1 : 30 ≤ s.ctorIdx) (h2 : s.ctorIdx < 81) :
    (s.ctorIdx - 30) / 17 < nbOf L g dt := by
  obtain ⟨g0, g1, g2⟩ := hG
  cases s <;> (try exact absurd h1 (by decide)) <;> (try exact absurd h2 (by decide)) <;>
    simp_all (config := { decide := true }) [nbOf] <;> split_ifs <;> simp_all
  all_goals decide

theorem bo_lt : ∀ r < 17, ∀ rb < 17, bbar rb = true →
    bo r + (if bbar r = true then 1 else 0) ≤ bo rb → r < rb := by
  decide

theorem bo_le : ∀ r < 17, ∀ rb < 17, bbar rb = true → bo r ≤ bo rb → r ≤ rb := by
  decide

theorem bo_bar : ∀ rb < 17, bbar rb = true → bo rb ≤ 4 := by
  decide

theorem bo_five (r : Nat) : bo r ≤ 5 := by
  unfold bo; split_ifs <;> omega

/-- The arithmetic of `pro_lt` and `pro_le`, with `c` the first site's own event (or `0`). -/
theorem off_cmp {n nb N c : Nat} (hn : 30 ≤ n → n < 81 → (n - 30) / 17 < N)
    (hnb : 30 ≤ nb → nb < 81 → (nb - 30) / 17 < N) (hb : binc nb = 1)
    (hc : c = binc n ∨ c = 0) (h : off n N + c ≤ off nb N) :
    n ≤ nb ∧ (c = binc n → n < nb) := by
  have hbo := bo_five ((n - 30) % 17)
  by_cases h29 : nb = 29
  · subst h29
    simp only [off, binc] at h hc ⊢
    split_ifs at h hc ⊢ <;> omega
  have hnb1 : 30 ≤ nb ∧ nb < 81 ∧ bbar ((nb - 30) % 17) = true := by
    unfold binc at hb; split_ifs at hb; omega
  obtain ⟨hb1, hb2, hb3⟩ := hnb1
  have hq := hnb hb1 hb2
  have hob := bo_bar _ (Nat.mod_lt _ (by omega)) hb3
  have hoffb : off nb N = 1 + 5 * ((nb - 30) / 17) + bo ((nb - 30) % 17) := by
    simp only [off]; split_ifs <;> omega
  rw [hoffb] at h
  by_cases hlo : n ≤ 29
  · omega
  by_cases hhi : 81 ≤ n
  · simp only [off, show ¬ n ≤ 29 from hlo, show ¬ n < 81 by omega, ↓reduceIte] at h
    have : (nb - 30) / 17 + 1 ≤ N := hq
    omega
  have hq' := hn (by omega) (by omega)
  have hoff : off n N = 1 + 5 * ((n - 30) / 17) + bo ((n - 30) % 17) := by
    simp only [off]; split_ifs <;> omega
  rw [hoff] at h
  have hn' : n = 30 + 17 * ((n - 30) / 17) + (n - 30) % 17 := by omega
  have hnb' : nb = 30 + 17 * ((nb - 30) / 17) + (nb - 30) % 17 := by omega
  have hr := Nat.mod_lt (n - 30) (show 17 > 0 by omega)
  have hrb := Nat.mod_lt (nb - 30) (show 17 > 0 by omega)
  have hbinc : binc n = if bbar ((n - 30) % 17) = true then 1 else 0 := by
    unfold binc
    have h29 : ¬ n = 29 := by omega
    have h30 : 30 ≤ n ∧ n < 81 := ⟨by omega, by omega⟩
    by_cases hbb : bbar ((n - 30) % 17) = true <;> simp [h29, h30, hbb]
  rcases lt_trichotomy ((n - 30) / 17) ((nb - 30) / 17) with hl | he | hg
  · constructor
    · omega
    · intro _; omega
  · rw [he] at h hn'
    have h1 : (n - 30) % 17 ≤ (nb - 30) % 17 := by
      refine bo_le _ hr _ hrb hb3 ?_
      omega
    refine ⟨by omega, fun hc' => ?_⟩
    have := bo_lt _ hr _ hrb hb3 (by rw [← hbinc, ← hc']; omega)
    omega
  · omega

/-- The arithmetic of `pro_lt`. -/
theorem off_lt {n nb N : Nat} (hn : 30 ≤ n → n < 81 → (n - 30) / 17 < N)
    (hnb : 30 ≤ nb → nb < 81 → (nb - 30) / 17 < N) (hb : binc nb = 1)
    (h : off n N + binc n ≤ off nb N) : n < nb :=
  (off_cmp hn hnb hb (.inl rfl) h).2 rfl

/-- The arithmetic of `pro_le`. -/
theorem off_le {n nb N : Nat} (hn : 30 ≤ n → n < 81 → (n - 30) / 17 < N)
    (hnb : 30 ≤ nb → nb < 81 → (nb - 30) / 17 < N) (hb : binc nb = 1)
    (h : off n N ≤ off nb N) : n ≤ nb :=
  (off_cmp (c := 0) hn hnb hb (.inr rfl) (by omega)).1

/-- **Prologue sites in count order are in program order (strict).** -/
theorem pro_lt {L : Launch} {g g' : Nat} {d1 d : ProA.D} (hG1 : ProA.Gate L g d1.site d1.dt)
    (hG : ProA.Gate L g' d.site d.dt) (hN : nbOf L g d1.dt = nbOf L g' d.dt)
    (hb : proB0 d.site = 2) (h : proOff L g d1 + proInc d1.site ≤ proOff L g' d) :
    d1.site.ctorIdx < d.site.ctorIdx := by
  rw [off_eq, off_eq, inc_eq, hN] at h
  have hb' : binc d.site.ctorIdx = 1 := by rw [← inc_eq]; simp [proInc, hb]
  exact off_lt (fun a b => hN ▸ gate_blk hG1 a b) (fun a b => gate_blk hG a b) hb' h

/-- **Prologue sites in count order are in program order.** -/
theorem pro_le {L : Launch} {g g' : Nat} {d1 d : ProA.D} (hG1 : ProA.Gate L g d1.site d1.dt)
    (hG : ProA.Gate L g' d.site d.dt) (hN : nbOf L g d1.dt = nbOf L g' d.dt)
    (hb : proB0 d.site = 2) (h : proOff L g d1 ≤ proOff L g' d) :
    d1.site.ctorIdx ≤ d.site.ctorIdx := by
  rw [off_eq, off_eq, hN] at h
  have hb' : binc d.site.ctorIdx = 1 := by rw [← inc_eq]; simp [proInc, hb]
  exact off_le (fun a b => hN ▸ gate_blk hG1 a b) (fun a b => gate_blk hG a b) hb' h

/-- The sites before the third load are before the partition's barrier. -/
theorem early_idx {s : ProA.Site} (h : s.afterSk = false) : s.ctorIdx ≤ 3 := by
  cases s <;> simp_all [ProA.Site.afterSk] <;> decide

/-- A barrier-0 site of the prologue is at the partition's barrier or later. -/
theorem bar_idx {s : ProA.Site} (h : proB0 s = 2) : 29 ≤ s.ctorIdx := by
  cases s <;> simp_all [proB0] <;> decide

end
end PTX.Kernels.InklingRelDecode.Proof.Progress.Wx
