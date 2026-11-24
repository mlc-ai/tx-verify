-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Result.LpCopy
public import Kernels.InklingRelDecode.Proof.Interface.LpProReach
public import Kernels.InklingRelDecode.Proof.Interface.PshWarp

@[expose] public section

/-!
# The prologue's half of `KvCopies`, and `KvCopies`

For a block `i < num_pre` of a CTA and a box `(isV, slab, hh)`, the copy is the prologue's copy
`j = 4 i + 2 slab + isV` by the thread of warp `hh` that led its elections (`Lp.exists_lead`):
that thread exited, so it reached the copy site (`Interface.pro_reaches_ptc`); the event is the
copy (`ProA.ptc_event`) whose spec is the box's (`Interface.ptc_kvspec`, the block-table word
being the page by `Interface.proCopyPage`), and the complete execution has its observation.
With the loader's half (`loader_copy_exists`) this is `KvCopies` (`kvCopies_of`).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Lp
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof
open PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX.Kernels.InklingRelDecode.Proof.Result.Mma
open PTX.Kernels.InklingRelDecode.Proof.EvW (kvCopySpec kvReady)

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **The event of a prologue state at a copy site, and its observation.** -/
theorem pro_copy_obs (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hc : Complete L X) {h k : Nat} {d : ProA.D}
    (hk : k < (X.tr h).length) (hσ : St Q L X h k = some (some (.d (.pro d)))) {j : Nat}
    (hj : j < 12) (hs : d.site = ProA.ptcSite j) :
    ∃ (o : TensorCopy.Observation) (bar : Loc), X.TensorIssue (h, k) Q.kvMap o.spec ∧
      X.tensor (h, k) = some o ∧
      o.spec = kvCopySpec Q (h / L.block)
        (ProA.cta L h .y * Q.headCols + 128 * (j % 2) + 64 * (ProA.tidOf L h / 32 % 2))
        (Q.page (ProA.cta L h .z) (2 * (ProA.cta L h .x + j / 4 * Q.splits) + j % 4 / 2) *
          Q.pageRows + ProA.cta L h .y * Q.headRows)
        (L.sharedBase + 32768 * (j / 4) + 98304 * (j % 2) + 8192 * (j % 4 / 2) +
          16384 * (ProA.tidOf L h / 32 % 2)) bar := by
  obtain ⟨e, he⟩ : ∃ e, X.get (h, k) = some e := ⟨_, List.getElem?_eq_getElem hk⟩
  have hg : h < L.threads := Frame.lt_of_get hX he
  obtain ⟨u, hF⟩ := fired_cont hX hf hg he hσ (by simp [ExitState])
  obtain ⟨-, tm, -, hpro⟩ := hf.reach hg hσ
  have hev := ProA.ptc_event hpre hj hpro (fired_pro hF) hs
  have hpage := (proCopyPage hpre hX hf hσ hj hs).2
  have hspec := ptc_kvspec hpre (by rw [hpro]; exact ⟨rfl, rfl, rfl⟩) hj
    ((EvD.kvReadyOf (j / 4)).loc L (h / L.block)) hpage
  rw [pro_half hpre hX hf hσ hj hs] at hspec
  have hti : X.TensorIssue (h, k) Q.kvMap (EvW.kvCopySpec Q (h / L.block)
      (ProA.copyX L h d.dt j) (ProA.copyY L h d.dt j) (ProA.copyDst L h d.dt j)
      ((EvD.kvReadyOf (j / 4)).loc L (h / L.block))) := ⟨_, by rw [he, hev]⟩
  obtain ⟨o, ho, -⟩ := ((asyncDrained_iff X).mp hc.2.1).2.2.2.2.1 _ _ _ hti
  obtain ⟨⟨a', ha'⟩, -⟩ := hX.tensor _ o ho
  obtain ⟨pc', hpc'⟩ := ha'
  rw [he, hev] at hpc'
  simp only [Option.some.injEq, Event.mk.injEq, Kind.tensorIssue.injEq] at hpc'
  obtain ⟨-, -, hsp⟩ := hpc'
  refine ⟨o, (EvD.kvReadyOf (j / 4)).loc L (h / L.block), ?_, ho, ?_⟩
  · rw [← hsp]; exact hti
  · rw [← hsp, hspec]

/-- **The prologue's half of `KvCopies`.** For a block `i < num_pre` of the CTA of a launched
thread `g` and a box `(isV, slab, hh)`, a copy of the box exists, by a prologue thread of the CTA
at the copy site of block `i`, with the spec of the box. -/
theorem pro_copy_exists (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hc : Complete L X) {g i : Nat} (isV slab hh : Nat)
    (hg : g < L.threads) (h1 : i < ProA.numPre Q (reqOf L g) (splitOf L g))
    (hV : isV ≤ 1) (hS : slab ≤ 1) (hH : hh ≤ 1) :
    ∃ (c : EvId) (o : TensorCopy.Observation) (a : Nat) (bar : Loc),
      c.1 < L.threads ∧ c.1 / L.block = g / L.block ∧ X.TensorIssue c a o.spec ∧
      X.tensor c = some o ∧ CopyBlock Q L X c i ∧
      o.spec = kvCopySpec Q (g / L.block) (kvhOf L g * Q.headCols + 128 * isV + 64 * hh)
        (Q.page (reqOf L g) (2 * blkOf Q L g i + slab) * Q.pageRows + kvhOf L g * Q.headRows)
        (L.sharedBase + 32768 * (i % 3) + 98304 * isV + 8192 * slab + 16384 * hh) bar := by
  have hb := hpre.block
  have hth : L.threads = L.grid * L.block := rfl
  have hg0 : g / L.block * L.block + 32 * hh < L.threads := by
    rw [hth, hb] at hg ⊢; omega
  obtain ⟨h, hw, hlead⟩ := exists_lead hX hb hg0
  obtain ⟨⟨-, hh1, hcta⟩, hwarp⟩ := hw
  have hch : h / L.block = g / L.block := by rw [hb] at hcta ⊢; omega
  have htid : ProA.tidOf L h / 32 = hh := by
    unfold ProA.tidOf; rw [hb] at hwarp ⊢; omega
  have hz := cta_eq hch .z
  have hx := cta_eq hch .x
  have hy := cta_eq hch .y
  have hnp : ProA.numPre Q (ProA.cta L g .z) (ProA.cta L g .x) ≤ 3 := by
    unfold ProA.numPre; exact Nat.min_le_right _ _
  have hi3 : i < 3 := by
    have : i < ProA.numPre Q (ProA.cta L g .z) (ProA.cta L g .x) := h1
    omega
  have hj : 4 * i + 2 * slab + isV < 12 := by omega
  have e1 : (4 * i + 2 * slab + isV) / 4 = i := by omega
  have e2 : (4 * i + 2 * slab + isV) % 2 = isV := by omega
  have e3 : (4 * i + 2 * slab + isV) % 4 / 2 = slab := by omega
  obtain ⟨k, d, hk, hσ, hs⟩ := pro_reaches_ptc hpre hX hf hh1 (by omega) (exit_last hX hc hh1)
    hlead hj (by rw [e1, hz, hx]; exact h1)
  obtain ⟨o, bar, hti, ho, hsp⟩ := pro_copy_obs hpre hX hf hc hk hσ hj hs
  refine ⟨(h, k), o, Q.kvMap, bar, hh1, hch, hti, ho,
    .inr ⟨d, _, hσ, hj, hs, e1⟩, ?_⟩
  rw [hsp, e1, e2, e3, htid, hch, Nat.mod_eq_of_lt hi3, Nat.mod_eq_of_lt (by omega : hh < 2)]
  unfold kvhOf reqOf blkOf splitOf
  rw [hz, hx, hy]

/-- **`KvCopies`**: the prologue's copies of the blocks below `num_pre` and the loader's of the
others. -/
theorem kvCopies_of (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hR : RoleReads L X) (hp : NumPreRead Q L X)
    (hn : NumWordRead Q L X) (hc : Complete L X) : KvCopies Q L X where
  exists_copy := by
    intro g i isV slab hh hg hi hV hS hH
    by_cases hl : i < ProA.numPre Q (reqOf L g) (splitOf L g)
    · exact pro_copy_exists hpre hX hf hc isV slab hh hg hl hV hS hH
    · exact loader_copy_exists hpre hX hf hR hp hn hc isV slab hh hg (by omega) hi hV hS hH

end
end PTX.Kernels.InklingRelDecode.Proof.Lp
