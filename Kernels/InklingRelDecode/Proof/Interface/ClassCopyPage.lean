-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Protocol.MbarWords
public import Kernels.InklingRelDecode.Proof.Interface.ShapeBox
public import Kernels.InklingRelDecode.Proof.Thread.ClassBtAddr

@[expose] public section

/-!
# The prologue's copies copy pages that exist (`ProCopyPage`)

`ProCopyPage` is the premise of `Interface.boxInBounds` on the prologue's twelve K/V copies: at a
copy site of block `i / 4` the block is below `num_iters` and the loaded block-table word of the
copy's slab is the page `Q.page` of that slab. The proof has two invariants along the thread's
states (`PgSo`) and one event fact:

* the gate: a state in the sites of block `j` has passed the branch that tests the number of
  blocks to preload (`ProA.Gate`, kept by every successor: `ProA.gate_next`), and the number is
  at most `num_iters` (`ProA.gate_iters`), so the block exists;
* the load (`load_lb`): the event at the load of block-table word `k` reads four input bytes at
  `block_table + 4 (stride_bt * req + 2 (split + (k / 2) * num_splits) + k % 2)`
  (`ProA.lb_addr`, the index fits because the block exists), which is the word of
  `Pre.btInput`, so the word the machine stores is `Q.page req (2 (split + (k / 2) num_splits) +
  k % 2)`;
* the word is kept to the copies: a step keeps the six words unless it is a load (`ProA.btW_next`,
  `ProA.next_lb`), and a step into a site after the load of word `k` is from such a site or from
  the load (`ProA.lbAfter_next`).

The request words the gate needs are `Mbar.wordsSo_all`.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.InklingRelDecode.Proof.Mbar
  (WordsSo wordsSo_all loaded_word next_map_some next_sm_not_pro next_epi_not_pro)

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

theorem reads_bt {r s : Nat} (hr : r < Q.b) (hs : s < 2 * Q.blocks r) {k : Nat} (hk : k < 4) :
    Q.reads (Q.btBase + 4 * (r * Q.strideBt + s) + k) :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨r, hr, s, hs, k, hk, rfl⟩))))

/-- **A block below `num_iters` is inside the request's blocks and the 32-bit index fits.** -/
theorem blk_index (hpre : Pre Q L mem0) {g : Nat} (hg : g < L.threads) {j : Nat}
    (hj : j < Q.numIters (ProA.cta L g .z) (ProA.cta L g .x)) :
    ProA.cta L g .x + j * Q.splits < Q.blocks (ProA.cta L g .z) ∧
      Q.blocks (ProA.cta L g .z) ≤ 2 ^ 24 := by
  obtain ⟨hx, hy, hz⟩ := ProA.cta_lt hpre hg
  refine ⟨Result.Mma.blk_lt hpre.splitsPos hj, ?_⟩
  have := hpre.seqRange _ hz
  unfold Params.blocks
  omega

/-- **The load of block-table word `k` loads the page of its slab**, where the block exists
(`j < num_iters`, here from the gate). -/
theorem load_lb (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) {g k0 k : Nat} (hk : k < 6) {dt : ProA.Dat} {d' : ProA.D}
    {e : Event} (hg : g < L.threads) (he : X.get (g, k0) = some e)
    (hσ : St Q L X g k0 = some (some (.d (.pro ⟨ProA.lbSite k, dt⟩))))
    (hn : ProA.next L g ⟨ProA.lbSite k, dt⟩ e = some (some d'))
    (hj : k / 2 < Q.numIters (ProA.cta L g .z) (ProA.cta L g .x)) :
    ProA.btW d'.dt k =
      Q.page (ProA.cta L g .z) (2 * (ProA.cta L g .x + k / 2 * Q.splits) + k % 2) := by
  obtain ⟨u, hF⟩ := fired_cont hX hf hg he hσ (by simp [ExitState])
  have hsite : ProA.lbSite k ∈ ProA.wordLoadSites := by interval_cases k <;> decide
  obtain ⟨bs, hlen, hev⟩ := ProA.shape_ld32 (fired_pro hF) hsite
  obtain ⟨a', bs', v, x, hk', hrb, hw, hbt, -, -⟩ := ProA.next_lb hk hn
  obtain ⟨-, tm, htm, hpro⟩ := hf.reach hg hσ
  obtain ⟨hx, hy, hz⟩ := ProA.cta_lt hpre hg
  have hdef : IsDefault L g := by
    have := hf.reach hg hσ
    exact this.1
  have ha : ProA.ArgsOk L g dt.pro := by
    rw [hpro]
    exact DStart.argsOk_inh hpre hg hdef tm
  have hspl := hpre.splitsRange
  have hbR := hpre.bRange
  have hsc := hpre.scalarsRange
  obtain ⟨hI1, hI2⟩ := blk_index hpre hg hj
  have hS : dt.pro.w67 = Q.strideBt := by
    rw [hpro]; exact Nat.mod_eq_of_lt (by omega)
  have hN : dt.pro.w71 = Q.splits := by
    rw [hpro]; exact Nat.mod_eq_of_lt (by omega)
  have hB : dt.pro.btB = Q.btBase := by rw [hpro]; rfl
  have hs2 : 2 * (ProA.cta L g .x + k / 2 * Q.splits) + k % 2 < 2 * Q.blocks (ProA.cta L g .z) := by
    omega
  have hbt' := hpre.btIndexRange _ hz _ hs2
  have hrr0 := hpre.readsRange (Q.btBase + 4 * (ProA.cta L g .z * Q.strideBt +
    (2 * (ProA.cta L g .x + k / 2 * Q.splits) + k % 2)) + 3) (reads_bt hz hs2 (by omega))
  have haddr := ProA.lb_addr L g dt hk (by omega)
    (by rw [hS, hN]; rw [Nat.mul_comm] at hbt'; omega) (by rw [hN]; omega)
  rw [hS, hN, hB] at haddr
  have hA : ProA.loadAddr L g dt (ProA.lbSite k) = Q.btBase + 4 * (ProA.cta L g .z * Q.strideBt +
      (2 * (ProA.cta L g .x + k / 2 * Q.splits) + k % 2)) := by
    rw [haddr, Nat.mod_eq_of_lt (by rw [Nat.mul_comm Q.strideBt]; omega)]
    rw [Nat.mul_comm Q.strideBt]
    congr 1
    omega
  have hpg : Q.page (ProA.cta L g .z) (2 * (ProA.cta L g .x + k / 2 * Q.splits) + k % 2) <
      2 ^ 32 := by
    have h1 := hpre.slabInside _ hz _ hs2 0 (by unfold kvHeads; omega)
    have h2 := hpre.rowsRange
    have h3 := hpre.pageRowsPos
    have h4 : Q.page (ProA.cta L g .z) (2 * (ProA.cta L g .x + k / 2 * Q.splits) + k % 2) ≤
        Q.page (ProA.cta L g .z) (2 * (ProA.cta L g .x + k / 2 * Q.splits) + k % 2) *
          Q.pageRows := Nat.le_mul_of_pos_right _ h3
    omega
  subst hev
  dsimp only at he hk'
  rw [hA] at he hk'
  rw [hbt]
  exact loaded_word hpre hX hf he hpg
    (fun j hj => ⟨reads_bt hz hs2 hj, hpre.btInput _ hz _ hs2 j hj⟩) hk' hrb hw

/-! ### The invariant along a thread -/

/-- **What a prologue state knows about its block-table words**: its sites are entered only where
the block is preloaded (`ProA.Gate`), and the words after their loads are the pages of their
slabs. -/
def PgSo (Q : Params) (L : Launch) (g : Nat) : TSt → Prop
  | .d (.pro d) => ProA.Gate L g d.site d.dt ∧
      ∀ k < 6, d.site ∈ ProA.lbAfter k → ProA.btW d.dt k =
        Q.page (ProA.cta L g .z) (2 * (ProA.cta L g .x + k / 2 * Q.splits) + k % 2)
  | _ => True

/-- **A prologue state at a site of block `j` has a block `j` that exists.** -/
theorem block_exists (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) {g k0 : Nat} {d : ProA.D} (hσ : St Q L X g k0 = some (some
      (.d (.pro d)))) (hk : d.site.afterSk = true) (hG : ProA.Gate L g d.site d.dt) {j : Nat}
    (hjb : d.site ∈ ProA.blkSites j) (hg : g < L.threads) :
    j < Q.numIters (ProA.cta L g .z) (ProA.cta L g .x) := by
  obtain ⟨hdef, tm, htm, hpro⟩ := hf.reach hg hσ
  have ha : ProA.ArgsOk L g d.dt.pro := by
    rw [hpro]
    exact DStart.argsOk_inh hpre hg hdef tm
  have hs : d.dt.pro.w71 = Q.splits := by
    have := hpre.splitsRange
    rw [hpro]; exact Nat.mod_eq_of_lt (by omega)
  obtain ⟨h0, h1, h2⟩ := wordsSo_all hpre hX hf k0 _ hσ
  have hne : d.site ≠ .sMax ∧ d.site ≠ .ldCu0 := by
    constructor <;> (rintro h; rw [h] at hk; simp [ProA.Site.afterSk] at hk)
  have hm : ProA.WordsMatch Q (ProA.cta L g .z) d.dt :=
    ⟨h0 hne.1 hne.2, h1 (Or.inl hk), h2 hk⟩
  obtain ⟨c0, c1, c2⟩ := ProA.gate_iters hpre hg ha hs hm
  obtain ⟨g0, g1, g2⟩ := hG
  match j, hjb with
  | 0, hjb => exact c0 (g0 hjb)
  | 1, hjb => exact c1 (g1 hjb).1 (g1 hjb).2
  | 2, hjb => exact c2 (g2 hjb).1 (g2 hjb).2.1 (g2 hjb).2.2
  | j + 3, hjb => simp [ProA.blkSites] at hjb

theorem lbSite_of_mem {s : ProA.Site} (h : s ∈ ProA.lbSites) : ∃ k < 6, s = ProA.lbSite k := by
  simp only [ProA.lbSites, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨0, by norm_num, rfl⟩
  · exact ⟨1, by norm_num, rfl⟩
  · exact ⟨2, by norm_num, rfl⟩
  · exact ⟨3, by norm_num, rfl⟩
  · exact ⟨4, by norm_num, rfl⟩
  · exact ⟨5, by norm_num, rfl⟩

theorem lbSite_blk {k : Nat} (hk : k < 6) : ProA.lbSite k ∈ ProA.blkSites (k / 2) := by
  interval_cases k <;> decide

theorem lbSite_afterSk {k : Nat} (hk : k < 6) : (ProA.lbSite k).afterSk = true := by
  interval_cases k <;> decide

theorem early_notAfter {s : ProA.Site}
    (h : s = .sMax ∨ s = .ldCu0 ∨ s = .ldCu1 ∨ s = .ldSk ∨ s = .el0) :
    (∀ k, s ∉ ProA.lbAfter k) ∧ ∀ j, s ∉ ProA.blkSites j := by
  refine ⟨fun k => ?_, fun j => ?_⟩
  · rcases h with rfl | rfl | rfl | rfl | rfl <;>
      (match k with
        | 0 | 1 | 2 | 3 | 4 | 5 => decide
        | k + 6 => simp [ProA.lbAfter])
  · rcases h with rfl | rfl | rfl | rfl | rfl <;>
      (match j with
        | 0 | 1 | 2 => decide
        | j + 3 => simp [ProA.blkSites])

theorem hearly {g : Nat} (d : ProA.D)
    (hd : d.site = .sMax ∨ d.site = .ldCu0 ∨ d.site = .ldCu1 ∨ d.site = .ldSk ∨ d.site = .el0) :
    PgSo Q L g (.d (.pro d)) := by
  obtain ⟨h1, h2⟩ := early_notAfter hd
  exact ⟨⟨fun hm => absurd hm (h2 0), fun hm => absurd hm (h2 1),
    fun hm => absurd hm (h2 2)⟩, fun k _ hm => absurd hm (h1 k)⟩

/-- **One prologue step keeps `PgSo`.** -/
theorem pgSo_step (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) {g k0 : Nat} {d0 d1 : ProA.D} {e : Event} (hg : g < L.threads)
    (he : X.get (g, k0) = some e) (hσ : St Q L X g k0 = some (some (.d (.pro d0))))
    (hI : PgSo Q L g (.d (.pro d0))) (hn : ProA.next L g d0 e = some (some d1)) :
    PgSo Q L g (.d (.pro d1)) := by
  obtain ⟨s, dt⟩ := d0
  obtain ⟨hG, hB⟩ := hI
  by_cases hk : s.afterSk = true
  · have hG' := ProA.gate_next hn hG hk
    refine ⟨hG', fun k hk6 hm => ?_⟩
    rcases ProA.lbAfter_next hn k hk6 hm with hs | hs
    · -- from a site after the load of word `k`
      have hb := hB k hk6 hs
      by_cases hlb : s ∈ ProA.lbSites
      · obtain ⟨k', hk'6, rfl⟩ := lbSite_of_mem hlb
        obtain ⟨_, _, _, _, -, -, -, -, -, hkeep⟩ := ProA.next_lb hk'6 hn
        have hne : k ≠ k' := by
          rintro rfl
          revert hs
          interval_cases k <;> decide
        rw [hkeep k hk6 hne]
        exact hb
      · rw [ProA.btW_next hn hlb k]
        exact hb
    · -- the load of word `k`
      subst hs
      refine load_lb hpre hX hf hk6 hg he hσ hn ?_
      exact block_exists hpre hX hf hσ hk hG (lbSite_blk hk6) hg
  · have hs4 : s = .sMax ∨ s = .ldCu0 ∨ s = .ldCu1 ∨ s = .ldSk := by
      cases s <;> simp_all [ProA.Site.afterSk]
    rcases hs4 with rfl | rfl | rfl | rfl
    · rw [ProA.next_sMax hn]
      exact hearly (Q := Q) (L := L) _ (Or.inr (Or.inl rfl))
    · obtain ⟨a, bs, v, x, -, -, -, rfl⟩ := ProA.next_ldCu0 hn
      exact hearly (Q := Q) (L := L) _ (Or.inr (Or.inr (Or.inl rfl)))
    · obtain ⟨a, bs, v, x, -, -, -, rfl⟩ := ProA.next_ldCu1 hn
      exact hearly (Q := Q) (L := L) _ (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
    · obtain ⟨a, bs, v, x, -, -, -, rfl⟩ := ProA.next_ldSk hn
      exact hearly (Q := Q) (L := L) _ (Or.inr (Or.inr (Or.inr (Or.inr rfl))))

theorem pgSo_start (g : Nat) (P : ProA.Inh) : PgSo Q L g (.d (.pro (ProA.D.start P))) :=
  hearly _ (Or.inl rfl)

/-- **The block-table words of every prologue state of a thread are the pages.** -/
theorem pgSo_all (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) {g : Nat} :
    ∀ k s, St Q L X g k = some (some s) → PgSo Q L g s := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro s hσ
  by_cases hinit : s = (code L Q g).init
  · subst hinit
    show PgSo Q L g (if g % L.block < 128 then .d (DComp.code L g Q).init
      else .w (WComp.code L g Q).init)
    split <;> exact trivial
  · obtain ⟨k0, e, s0, hlt, he', hs0, hn⟩ := stateAt_pred hσ hinit
    have he : X.get (g, k0) = some e := he'
    have hg : g < L.threads := Frame.lt_of_get hX he
    have hI := ih k0 hlt s0 hs0
    cases s0 with
    | w w0 =>
      rw [next_w] at hn
      obtain ⟨a, -, rfl⟩ := next_map_some hn
      exact trivial
    | d d0 =>
      rw [next_d] at hn
      obtain ⟨s1, hn1, rfl⟩ := next_map_some hn
      cases s1 with
      | dstart d1 => exact trivial
      | sm d1 => exact trivial
      | epi d1 => exact trivial
      | pro d1 =>
        cases d0 with
        | dstart ds =>
          have h' : DComp.dstartNext L g Q ds e = some (some (.pro d1)) := hn1
          unfold DComp.dstartNext at h'
          obtain ⟨d2, -, h2⟩ := next_map_some h'
          split_ifs at h2
          cases h2
          exact pgSo_start g _
        | sm ds => exact absurd hn1 (next_sm_not_pro g Q ds e d1)
        | epi ds => exact absurd hn1 (next_epi_not_pro g Q ds e d1)
        | pro dp =>
          have h' : DComp.proNext L g Q dp e = some (some (.pro d1)) := hn1
          unfold DComp.proNext at h'
          by_cases hb : dp.site = ProA.Site.bar18
          · simp only [hb, ↓reduceIte] at h'
            split_ifs at h' <;> cases h'
          · simp only [hb, ↓reduceIte] at h'
            obtain ⟨d3, hd3, h3⟩ := next_map_some h'
            cases h3
            exact pgSo_step hpre hX hf hg he hs0 hI hd3

/-! ### The premise of `boxInBounds` on the prologue's copies -/

/-- **The prologue's copies copy pages that exist** (`ProCopyPage`, the premise of
`boxInBounds`). -/
theorem proCopyPage (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) : ProCopyPage Q L X := by
  intro g k d i hσ hi hs
  have hg : g < L.threads := by
    obtain ⟨k0, e, s0, -, he, -, -⟩ := stateAt_pred hσ (by
      intro h
      have : (TSt.d (DComp.St.pro d)) = (code L Q g).init := h
      simp only at this
      split at this <;> cases this)
    exact Frame.lt_of_get hX he
  obtain ⟨hG, hB⟩ := pgSo_all hpre hX hf k _ hσ
  have hmem : ∀ i < 12, ProA.ptcSite i ∈ ProA.blkSites (i / 4) ∧
      ProA.ptcSite i ∈ ProA.lbAfter (2 * (i / 4) + i % 4 / 2) ∧
      (ProA.ptcSite i).afterSk = true := by
    intro i hi
    interval_cases i <;> decide
  obtain ⟨hb1, hb2, hb3⟩ := hmem i hi
  refine ⟨?_, ?_⟩
  · exact block_exists hpre hX hf (d := d) hσ (by rw [hs]; exact hb3) hG
      (j := i / 4) (by rw [hs]; exact hb1) hg
  · have := hB (2 * (i / 4) + i % 4 / 2) (by omega) (by rw [hs]; exact hb2)
    have e1 : (2 * (i / 4) + i % 4 / 2) / 2 = i / 4 := by omega
    have e2 : (2 * (i / 4) + i % 4 / 2) % 2 = i % 4 / 2 := by omega
    rw [e1, e2] at this
    exact this

end
end PTX.Kernels.InklingRelDecode.Proof.Interface
