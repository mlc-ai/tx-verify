-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Common.ScriptFacts
public import Kernels.InklingRelDecode.Proof.Common.EndTime
public import Kernels.InklingRelDecode.Proof.Common.Table
public import Kernels.InklingRelDecode.Proof.Common.WorkerBalance

@[expose] public section

/-! # The collectives of the loader warp

The startup's shuffle, then nine collectives for each block of the loop: the ring barrier and the
four elections each with the barrier before it. `loaderCn lo hi n` is the pc of the `n`-th,
`loaderSlot lo hi n` its time. -/

namespace PTX.Kernels.InklingRelDecode.Proof
open PTX PTX.Flow

/-- The loader's collective sites of a block in order. -/
def loaderSites : List Loader.Site :=
  [.readyBar, .warpBar 0, .elect 0, .warpBar 1, .elect 1, .warpBar 2, .elect 2, .warpBar 3,
    .elect 3]

def loaderCn (lo hi n : Nat) : Option Nat :=
  if n = 0 then some 17 else if (n - 1) / 9 < hi - lo then
    some ((loaderSites[(n - 1) % 9]?.getD .dec).pc) else none

def loaderSlot (lo n : Nat) : Nat :=
  if n = 0 then 24 else
    Loader.slotTime (lo + (n - 1) / 9) + (loaderSites[(n - 1) % 9]?.getD .dec).position

theorem loaderCn_at {lo hi b q : Nat} (hq : q < 9) (hb : b < hi - lo) :
    loaderCn lo hi (1 + 9 * b + q) = some ((loaderSites[q]?.getD .dec).pc) := by
  have h1 : (1 + 9 * b + q - 1) / 9 = b := by omega
  have h2 : (1 + 9 * b + q - 1) % 9 = q := by omega
  simp [loaderCn, h1, h2, hb]

theorem loaderSlot_at {lo b q : Nat} (hq : q < 9) :
    loaderSlot lo (1 + 9 * b + q) =
      Loader.slotTime (lo + b) + (loaderSites[q]?.getD .dec).position := by
  have h1 : (1 + 9 * b + q - 1) / 9 = b := by omega
  have h2 : (1 + 9 * b + q - 1) % 9 = q := by omega
  simp [loaderSlot, h1, h2]

/-- The script position inside a block of a site of the loop. -/
def loopIdx (s : Loader.Site) : Nat := if s = .poll then 0 else 9 - Loader.remain s

/-- The static facts of a site of the loop against the block's nine collectives. -/
def loopCheck (s : Loader.Site) : Bool :=
  (!s.coll || (decide (loopIdx s < 9) && loaderSites[loopIdx s]? == some s)) &&
  (s.coll || ((loaderSites[loopIdx s % 9]?.getD .dec).pc != s.pc &&
    (List.range 9).all fun q => decide (q < loopIdx s) ||
      decide (s.position < (loaderSites[q]?.getD .dec).position))) && decide (loopIdx s ≤ 9)

theorem loopCheck_all (s : Loader.Site) : loopCheck s = true := by
  cases s <;> first | decide +kernel | (rename_i p; revert p; decide +kernel) |
    (rename_i p b; revert p b; decide +kernel)

private theorem cn_some {lo hi b q x : Nat} (hq : q ≤ 9) (hb : b < hi - lo)
    (h : loaderCn lo hi (1 + 9 * b + q) = some x) : x = (loaderSites[q % 9]?.getD .dec).pc := by
  by_cases q9 : q < 9
  · rw [loaderCn_at q9 hb] at h
    rw [Nat.mod_eq_of_lt q9]
    exact (Option.some.inj h).symm
  · obtain rfl : q = 9 := by omega
    have e1 : 1 + 9 * b + 9 = 1 + 9 * (b + 1) + 0 := by omega
    rw [e1] at h
    by_cases hb1 : b + 1 < hi - lo
    · rw [loaderCn_at (by omega) hb1] at h
      exact (Option.some.inj h).symm
    · simp [loaderCn, hb1] at h

/-- **A site of the loop** at block `b` is at the script position of its collectives done. -/
theorem loop_facts {lo hi b : Nat} (hb : b < hi - lo) (s : Loader.Site) :
    ScriptFacts (loaderCn lo hi) (loaderSlot lo) (1 + 9 * b + loopIdx s) s.pc
      (Loader.slotTime (lo + b) + s.position) := by
  have chk := loopCheck_all s
  have wc := loader_coll s
  have pb := Loader.position_bound s
  simp only [loopCheck, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq,
    beq_iff_eq, bne_iff_ne, ne_eq, List.all_eq_true, List.mem_range] at chk
  obtain ⟨⟨c1, c2⟩, c3⟩ := chk
  by_cases hc : s.coll = true
  · obtain ⟨hq, hsite⟩ := c1.resolve_left (by simp [hc])
    rw [hc] at wc
    have hsite' : loaderSites[loopIdx s]?.getD .dec = s := by simp [hsite]
    refine ⟨?_, fun _ => ?_, fun h => absurd h (by simp [wc])⟩
    · rw [loaderCn_at hq hb, hsite']
      simp [wc]
    · rw [loaderSlot_at hq, hsite']
  · have hf : s.coll = false := by simpa using hc
    rw [hf] at wc
    obtain ⟨hne, hlt⟩ := c2.resolve_left (by simp [hf])
    refine ⟨?_, fun h => absurd h (by simp [wc]), fun _ n hn hle => ?_⟩
    · simp only [wc, Bool.false_eq_true, false_iff]
      intro h
      exact hne (cn_some c3 hb h).symm
    · have hn' : loaderCn lo hi n ≠ none := Option.isSome_iff_ne_none.mp hn
      have n1 : 1 ≤ n := by
        by_contra n0
        obtain rfl : n = 0 := by omega
        omega
      have hlt' : (n - 1) / 9 < hi - lo := by
        by_contra hge
        apply hn'
        simp [loaderCn, show ¬ n = 0 by omega, hge]
      have e : loaderSlot lo n = Loader.slotTime (lo + (n - 1) / 9) +
          (loaderSites[(n - 1) % 9]?.getD .dec).position := by
        simp [loaderSlot, show ¬ n = 0 by omega]
      rw [e]
      simp only [Loader.slotTime, Lib.Slots.frame, Lib.Slots.stride] at pb ⊢
      by_cases hsame : (n - 1) / 9 = b
      · have hq' : (n - 1) % 9 < 9 := Nat.mod_lt _ (by omega)
        have := hlt ((n - 1) % 9) hq'
        rw [hsame] at e ⊢
        have h2 : loopIdx s ≤ (n - 1) % 9 := by omega
        have := (hlt _ hq').resolve_left (by omega)
        omega
      · have : b + 1 ≤ (n - 1) / 9 := by omega
        have : 400 * (lo + b + 1) ≤ 400 * (lo + (n - 1) / 9) := by omega
        omega

theorem loader_remain_le (s : Loader.Site) : Loader.remain s ≤ 9 := by
  cases s <;> first | decide +kernel | (rename_i p; revert p; decide +kernel) |
    (rename_i p b; revert p b; decide +kernel)

theorem loaderSlot_big (lo : Nat) {n : Nat} (h : 1 ≤ n) : 1000 ≤ loaderSlot lo n := by
  have := Loader.position_bound (loaderSites[(n - 1) % 9]?.getD .dec)
  simp only [loaderSlot, show ¬ n = 0 by omega, ↓reduceIte, Loader.slotTime, Lib.Slots.frame]
  omega

theorem loaderCn_lt {lo hi n : Nat} (h : (loaderCn lo hi n).isSome = true) (h0 : n ≠ 0) :
    (n - 1) / 9 < hi - lo := by
  by_contra hge
  simp [loaderCn, h0, hge] at h

theorem loaderCn_one (lo hi : Nat) : ∀ x, loaderCn lo hi 1 = some x → x = 2377 := by
  intro x h
  by_cases hh : 0 < hi - lo
  · simpa [loaderCn, loaderSites, Loader.Site.pc, hh] using h.symm
  · simp [loaderCn, hh] at h

private theorem loop_time (d : Loader.D) (h : d.site.inLoop = true) :
    Loader.time d = Loader.slotTime (Loader.bits d.counter).toNat + d.site.position := by
  obtain ⟨s, i, n, a, b⟩ := d
  cases s <;> first | rfl | cases h

/-- A state outside the loop is at no collective and early, or past the script's end. -/
private theorem off_loop {lo hi c pc clk : Nat} (hpc : isWarpAt pc = false)
    (hne : ∀ x, loaderCn lo hi c = some x → x ≠ pc)
    (hlt : ∀ n, (loaderCn lo hi n).isSome = true → c ≤ n → clk < loaderSlot lo n) :
    ScriptFacts (loaderCn lo hi) (loaderSlot lo) c pc clk := by
  refine ⟨by simp only [hpc, Bool.false_eq_true, false_iff]; intro h; exact hne _ h rfl,
    fun h => by simp [hpc] at h, fun _ => hlt⟩

private theorem early_facts {lo hi : Nat} {n : Cls → Nat} (pc clk : Nat)
    (hpc : isWarpAt pc = false) (ne : pc ≠ 2377) (hc : clk < 1000) (e1 : n .coll = 1) :
    ScriptFacts (loaderCn lo hi) (loaderSlot lo) (n .coll) pc clk := by
  rw [e1]
  exact off_loop hpc (fun x h => by rw [loaderCn_one lo hi x h]; exact fun h => ne h.symm)
    (fun m _ le => by have := loaderSlot_big lo le; omega)

private theorem late_facts {lo hi : Nat} {n : Cls → Nat} (pc clk : Nat)
    (hpc : isWarpAt pc = false) (e1 : n .coll = 1 + 9 * (hi - lo)) :
    ScriptFacts (loaderCn lo hi) (loaderSlot lo) (n .coll) pc clk := by
  rw [e1]
  refine off_loop hpc (fun x h => ?_) (fun m hm le => ?_)
  · have := loaderCn_lt (n := 1 + 9 * (hi - lo)) (by rw [h]; rfl) (by omega)
    omega
  · have := loaderCn_lt hm (by omega)
    omega

/-- **A state of the loader's loops** against its script: the polls and the ledger give the
position, the reference the block. -/
theorem loader_site_facts {lo hi : Nat} {d : Loader.D} {n : Cls → Nat} (hh : hi < 2 ^ 31)
    (ref : Loader.Ref lo hi d) (poll : n (.poll 2374) = Loader.polls lo hi d)
    (cnt : n .coll + Loader.remain d.site = 1 + 9 * n (.poll 2374)) :
    ScriptFacts (loaderCn lo hi) (loaderSlot lo) (n .coll) d.site.pc (Loader.time d) := by
  have rl := loader_remain_le d.site
  by_cases hl : d.site.inLoop = true
  · obtain ⟨j, hlo, hjh, hc, -⟩ := Loader.ref_loop ref hl
    have hb : (Loader.bits d.counter).toNat = j := by
      rw [hc, Loader.bits_b32 (by omega), BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have := loop_facts (lo := lo) (hi := hi) (b := j - lo) (by omega) d.site
    rw [loop_time d hl, hb]
    have e : lo + (j - lo) = j := by omega
    rw [e] at this
    have hp : Loader.polls lo hi d = (if d.site = .poll then 0 else 1) + (j - lo) := by
      obtain ⟨s, i, nn, a, b⟩ := d
      cases s <;> first | (simp [Loader.polls, hb]; done) | (simp [Loader.polls, hb]; omega) |
        exact absurd hl (by simp [Loader.Site.inLoop])
    have c2 : n .coll = 1 + 9 * (j - lo) + loopIdx d.site := by
      rw [poll, hp] at cnt
      by_cases hs : d.site = .poll
      · simp only [loopIdx, hs, ite_true] at cnt ⊢
        simp [Loader.remain, Loader.owed] at cnt
        omega
      · simp only [loopIdx, hs, ite_false] at cnt ⊢
        omega
    rw [c2]
    exact this
  · have early := early_facts (lo := lo) (hi := hi) (n := n)
    have late := late_facts (lo := lo) (hi := hi) (n := n)
    have wf : isWarpAt d.site.pc = false := by
      rw [loader_coll]
      cases h : d.site <;> first | rfl |
        (rw [h] at hl; exact absurd hl (by simp [Loader.Site.inLoop]))
    obtain ⟨s, i, nn, a, b⟩ := d
    cases s <;> try simp only [Loader.polls, Loader.remain, Loader.owed] at poll cnt
    all_goals first
      | exact early _ _ wf (by simp [Loader.Site.pc])
          (by simp [Loader.time, Lib.Slots.enter, Lib.Slots.reuse])
          (by omega)
      | exact late _ _ wf (by omega)
      | exact absurd hl (by simp [Loader.Site.inLoop])

/-- **A dispatch state of the loader's warp** against its script. -/
theorem loader_dispatch_facts {lo hi : Nat} {dd : Dispatch.D} {n : Cls → Nat} {clk : Nat}
    (ref : DispatchRef 6 lo hi dd n) (cnt : n .coll = 1 + 9 * n (.poll 2374))
    (hclk : dd.round = 0 → clk < 300) :
    ScriptFacts (loaderCn lo hi) (loaderSlot lo) (n .coll) dd.site.pc clk ∧
      (dd.site.pc = 2855 → ∀ j, (loaderCn lo hi j).isSome = true → j < n .coll) := by
  have ok : ∀ s : Dispatch.Site, isWarpAt s.pc = false ∧ s.pc ≠ 2377 := fun s => by
    cases s <;> decide +kernel
  obtain ⟨al, -, r0, r1⟩ := ref
  refine ⟨?_, fun h j hj => ?_⟩
  · by_cases h : dd.round = 0
    · exact early_facts _ _ (ok _).1 (ok _).2 (by have := hclk h; omega)
        (by rw [cnt, (r0 h).1])
    · exact late_facts _ _ (ok _).1 (by rw [cnt, (r1 h).1 rfl])
  · rw [cnt, (r1 (dispatch_ret_round al h)).1 rfl]
    by_cases j0 : j = 0
    · omega
    · have := loaderCn_lt hj j0; omega

private theorem sites_mono : ∀ q < 9, ∀ q' < 9, q < q' →
    (loaderSites[q]?.getD .dec).position < (loaderSites[q']?.getD .dec).position := by
  decide +kernel

/-- The slots of the script rise. -/
theorem loaderSlot_mono (lo : Nat) {a b : Nat} (hab : a < b) :
    loaderSlot lo a < loaderSlot lo b := by
  have pb := Loader.position_bound (loaderSites[(b - 1) % 9]?.getD .dec)
  have pa := Loader.position_bound (loaderSites[(a - 1) % 9]?.getD .dec)
  by_cases a0 : a = 0
  · subst a0
    have := loaderSlot_big lo (show 1 ≤ b by omega)
    rw [show loaderSlot lo 0 = 24 by simp [loaderSlot]]
    omega
  · simp only [loaderSlot, a0, show ¬ b = 0 by omega, ↓reduceIte, Loader.slotTime,
      Lib.Slots.frame, Lib.Slots.stride]
    by_cases hs : (a - 1) / 9 = (b - 1) / 9
    · rw [hs]
      have := sites_mono ((a - 1) % 9) (Nat.mod_lt _ (by omega)) ((b - 1) % 9)
        (Nat.mod_lt _ (by omega)) (by omega)
      omega
    · have : (a - 1) / 9 + 1 ≤ (b - 1) / 9 := by omega
      have : 400 * (lo + ((a - 1) / 9 + 1)) ≤ 400 * (lo + (b - 1) / 9) := by omega
      omega

theorem loader_pc_ne (s : Loader.Site) : s.pc ≠ 2855 := by
  cases s <;> first | decide +kernel | (rename_i p; revert p; decide +kernel) |
    (rename_i p b; revert p b; decide +kernel)

end PTX.Kernels.InklingRelDecode.Proof
