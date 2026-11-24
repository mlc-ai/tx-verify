-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.PrefixPro
public import Kernels.InklingRelDecode.Proof.Interface.ClassCopyPage

@[expose] public section

/-!
# The prologue's block-table loads, in prefix form

At the load of block-table word `k` (`ProA.lbSite k`, `k < 6`) the prologue machine follows a
loaded 32-bit word and leaves its run (`some none`) otherwise. The proof that it follows is
`ClassCopyPage.load_lb` without the tracking of other threads:

* the gate (`ProA.Gate`, kept by every step: `ProA.gate_next`) holds at every prologue state the
  machine reaches (`gateSo_all`); it is a fact about the machine's own steps;
* with the thread's own request words (`wordsSo_all_at`, from `Good` at its earlier events) the
  gate says the block exists (`block_exists_at`, as `block_exists`);
* so the load reads the four input bytes of the block-table word (`ProA.lb_addr`), and the event's
  own `LaunchRead` gives the launch's word, which is below `2 ^ 32`.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.InklingRelDecode.Proof.Mbar (next_map_some next_sm_not_pro next_epi_not_pro)

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- The gate of a prologue state (`ProA.Gate`); other states carry nothing. -/
def GateSo (L : Launch) (g : Nat) : TSt → Prop
  | .d (.pro d) => ProA.Gate L g d.site d.dt
  | _ => True

/-- The early sites carry the gate: they are in no block. -/
theorem gate_early {g : Nat} {d : ProA.D}
    (hd : d.site = .sMax ∨ d.site = .ldCu0 ∨ d.site = .ldCu1 ∨ d.site = .ldSk ∨ d.site = .el0) :
    GateSo L g (.d (.pro d)) := by
  have h2 := (early_notAfter hd).2
  exact ⟨fun hm => absurd hm (h2 0), fun hm => absurd hm (h2 1), fun hm => absurd hm (h2 2)⟩

/-- **One prologue step keeps the gate.** -/
theorem gateSo_step {g : Nat} {d0 d1 : ProA.D} {e : Event} (hI : GateSo L g (.d (.pro d0)))
    (hn : ProA.next L g d0 e = some (some d1)) : GateSo L g (.d (.pro d1)) := by
  obtain ⟨s, dt⟩ := d0
  by_cases hk : s.afterSk = true
  · exact ProA.gate_next hn hI hk
  · have hs4 : s = .sMax ∨ s = .ldCu0 ∨ s = .ldCu1 ∨ s = .ldSk := by
      cases s <;> simp_all [ProA.Site.afterSk]
    rcases hs4 with rfl | rfl | rfl | rfl
    · rw [ProA.next_sMax hn]
      exact gate_early (Or.inr (Or.inl rfl))
    · obtain ⟨a, bs, v, x, -, -, -, rfl⟩ := ProA.next_ldCu0 hn
      exact gate_early (Or.inr (Or.inr (Or.inl rfl)))
    · obtain ⟨a, bs, v, x, -, -, -, rfl⟩ := ProA.next_ldCu1 hn
      exact gate_early (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
    · obtain ⟨a, bs, v, x, -, -, -, rfl⟩ := ProA.next_ldSk hn
      exact gate_early (Or.inr (Or.inr (Or.inr (Or.inr rfl))))

/-- **Every state the machine reaches carries the gate.** -/
theorem gateSo_all {g : Nat} :
    ∀ k s, St Q L X g k = some (some s) → GateSo L g s := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro s hσ
  by_cases hinit : s = (code L Q g).init
  · subst hinit
    show GateSo L g (if g % L.block < 128 then .d (DComp.code L g Q).init
      else .w (WComp.code L g Q).init)
    split <;> exact trivial
  · obtain ⟨k0, e, s0, hlt, he', hs0, hn⟩ := stateAt_pred hσ hinit
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
          exact (pgSo_start (Q := Q) (L := L) g _).1
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
            exact gateSo_step hI hd3

/-- **A prologue state at a site of block `j` has a block `j` that exists** (`block_exists`, with
the thread's own request words). -/
theorem block_exists_at (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hS : ∀ g < L.threads, (threadCode L g Q).Sound)
    (hT : ∀ g < L.threads, (threadCode L g Q).TmplOk) {g k0 : Nat} {d : ProA.D}
    (hσ : St Q L X g k0 = some (some (.d (.pro d))))
    (hgood : ∀ j < k0, Good Q L mem0 X (g, j)) (hk : d.site.afterSk = true)
    (hG : ProA.Gate L g d.site d.dt) {j : Nat} (hjb : d.site ∈ ProA.blkSites j)
    (hg : g < L.threads) : j < Q.numIters (ProA.cta L g .z) (ProA.cta L g .x) := by
  obtain ⟨hdef, tm, htm, hpro⟩ := treach_stateAt hpre hg hσ
  have ha : ProA.ArgsOk L g d.dt.pro := by
    rw [hpro]
    exact DStart.argsOk_inh hpre hg hdef tm
  have hs : d.dt.pro.w71 = Q.splits := by
    have := hpre.splitsRange
    rw [hpro]; exact Nat.mod_eq_of_lt (by omega)
  obtain ⟨h0, h1, h2⟩ := wordsSo_all_at hpre hX hS hT k0 _ hσ hgood
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

/-- **A block-table load that returned a 32-bit word continues.** -/
theorem next_lb_some {g k : Nat} (hk : k < 6) {dt : ProA.Dat} {e : Event} {a : Acc}
    {bs : List (Option Byte)} {x : Nat} (he : e.kind = .rd a bs)
    (hrb : rebuild 3 bs = .ok (b32 x)) (hx : x < 2 ^ 32) :
    ∃ d', ProA.next L g ⟨ProA.lbSite k, dt⟩ e = some (some d') := by
  have hw := ProA.word32_b32 hx
  interval_cases k
  all_goals
    simp only [ProA.lbSite, ProA.lbSites, List.getD_cons_zero, List.getD_cons_succ]
    simp only [ProA.next, he, hrb, hw]
    exact ⟨_, rfl⟩

/-- **A block-table load does not leave the run.** -/
theorem pro_lb_next_ne (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hS : ∀ g < L.threads, (threadCode L g Q).Sound)
    (hT : ∀ g < L.threads, (threadCode L g Q).TmplOk) {g k0 k : Nat} (hk : k < 6)
    {dt : ProA.Dat} {e : Event} (hg : g < L.threads) (he : X.get (g, k0) = some e)
    (hσ : St Q L X g k0 = some (some (.d (.pro ⟨ProA.lbSite k, dt⟩))))
    (hgood : ∀ j < k0, Good Q L mem0 X (g, j)) (hL : LaunchRead Q mem0 X (g, k0)) :
    (threadCode L g Q).next (.d (.pro ⟨ProA.lbSite k, dt⟩)) e ≠ some none := by
  obtain ⟨u, hF⟩ := fired_cont_at hX hS hT hg he hσ (by simp [ExitState])
  have hsite : ProA.lbSite k ∈ ProA.wordLoadSites := by interval_cases k <;> decide
  obtain ⟨bs, hlen, hev⟩ := ProA.shape_ld32 (fired_pro hF) hsite
  have hG : ProA.Gate L g (ProA.lbSite k) dt := gateSo_all (Q := Q) (X := X) k0 _ hσ
  have hj := block_exists_at hpre hX hS hT hσ hgood (lbSite_afterSk hk) hG (lbSite_blk hk) hg
  obtain ⟨hdef, tm, htm, hpro⟩ := treach_stateAt hpre hg hσ
  obtain ⟨hx, hy, hz⟩ := ProA.cta_lt hpre hg
  have ha : ProA.ArgsOk L g dt.pro := by
    rw [hpro]
    exact DStart.argsOk_inh hpre hg hdef tm
  have hspl := hpre.splitsRange
  have hbR := hpre.bRange
  have hsc := hpre.scalarsRange
  obtain ⟨hI1, hI2⟩ := blk_index hpre hg hj
  have hSt : dt.pro.w67 = Q.strideBt := by
    rw [hpro]; exact Nat.mod_eq_of_lt (by omega)
  have hN : dt.pro.w71 = Q.splits := by
    rw [hpro]; exact Nat.mod_eq_of_lt (by omega)
  have hB : dt.pro.btB = Q.btBase := by rw [hpro]; rfl
  have hs2 : 2 * (ProA.cta L g .x + k / 2 * Q.splits) + k % 2 <
      2 * Q.blocks (ProA.cta L g .z) := by
    omega
  have hbt' := hpre.btIndexRange _ hz _ hs2
  have hrr0 := hpre.readsRange (Q.btBase + 4 * (ProA.cta L g .z * Q.strideBt +
    (2 * (ProA.cta L g .x + k / 2 * Q.splits) + k % 2)) + 3) (reads_bt hz hs2 (by omega))
  have haddr := ProA.lb_addr L g dt hk (by omega)
    (by rw [hSt, hN]; rw [Nat.mul_comm] at hbt'; omega) (by rw [hN]; omega)
  rw [hSt, hN, hB] at haddr
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
  have he2 := he
  rw [hev] at he2
  dsimp only at he2
  rw [hA] at he2
  set x := Q.page (ProA.cta L g .z) (2 * (ProA.cta L g .x + k / 2 * Q.splits) + k % 2) with hxd
  have hbs := input_word_of_launch hX hL he2 rfl rfl x
    (fun j hj => ⟨reads_bt hz hs2 hj, hpre.btInput _ hz _ hs2 j hj⟩)
  have hrb : rebuild 3 bs = .ok (b32 x) := by rw [hbs]; exact rebuild_b32 x
  have hkind : e.kind = .rd (EvD.wordAcc ⟨.global, 0, ProA.loadAddr L g dt (ProA.lbSite k)⟩) bs :=
    by rw [hev]
  obtain ⟨d', hn⟩ := next_lb_some (L := L) (g := g) (dt := dt) hk hkind hrb hpg
  refine next_pro_ne_of ?_ (by rw [hn]; simp)
  show ProA.lbSite k ≠ ProA.Site.bar18
  interval_cases k <;> decide

end
end PTX.Kernels.InklingRelDecode.Proof.Interface
