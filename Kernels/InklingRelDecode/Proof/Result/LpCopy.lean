-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.LpAll
public import Kernels.InklingRelDecode.Proof.Result.MmaPremises
public import Kernels.InklingRelDecode.Proof2.Lib.KvBox

@[expose] public section

/-!
# The loader's half of `KvCopies`

For a block `num_pre ≤ i < num_iters` of a CTA and a box `(isV, slab, hh)`, the copy exists: warp
6 of the CTA has a thread `h` that led its elections (`Lp.exists_lead`), it exited (the execution
is complete), so it has a state at the copy site of the box in iteration `i`
(`Lp.loader_reaches`); the event there is the box's copy (`Ring.ldShape_cp`), whose spec is
`kvCopySpec` at `Spec`'s origin and destination (`loader_copy_spec`, with the block-table word of
the state the page of the slab, `Interface.loader_copy_page`), and the complete execution has its
observation (`AsyncDrained`).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Lp
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof
open PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX.Kernels.InklingRelDecode.Proof.Result.Mma
open PTX.Kernels.InklingRelDecode.Proof.EvW (kvCopySpec kvReady)

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- The copy site of box `(isV, slab, hh)`. -/
def cpSite (isV slab hh : Nat) : Loader.Site :=
  if slab = 0 then
    (if isV = 0 then (if hh = 0 then .cp0a else .cp0b) else (if hh = 0 then .cp1a else .cp1b))
  else
    (if isV = 0 then (if hh = 0 then .cp2a else .cp2b) else (if hh = 0 then .cp3a else .cp3b))

theorem cpSite_box {isV slab hh : Nat} (hV : isV ≤ 1) (hS : slab ≤ 1) (hH : hh ≤ 1) :
    EvW.ldBox (cpSite isV slab hh) = some (decide (isV = 1), slab, hh) ∧
      3 ≤ pos (cpSite isV slab hh) ∧ Ring.Ld.isCp (cpSite isV slab hh) = true := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hV with rfl | rfl <;>
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hS with rfl | rfl <;>
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hH with rfl | rfl <;> decide

/-- The CTA coordinates of two threads of one CTA agree. -/
theorem cta_eq {g h : Nat} (hc : h / L.block = g / L.block) (d : Dim) :
    ProA.cta L h d = ProA.cta L g d := by
  unfold ProA.cta
  rw [hc]

/-- The lane-0 thread of warp 6 of the CTA of `g`. -/
theorem warp6_thread (hb : L.block = 256) {g : Nat} (hg : g < L.threads) :
    g / L.block * L.block + 192 < L.threads ∧
      (g / L.block * L.block + 192) / L.block = g / L.block ∧
      (g / L.block * L.block + 192) % L.block = 192 := by
  have hth : L.threads = L.grid * L.block := rfl
  rw [hth, hb] at hg ⊢
  refine ⟨by omega, by omega, by omega⟩

/-- **A launched thread of a complete execution has its exit as its last event.** -/
theorem exit_last (hX : Consistent L kernel asms mem0 X) (hc : Complete L X) {h : Nat}
    (hh : h < L.threads) : ∃ pc, (X.tr h).getLast? = some ⟨pc, .exit⟩ := by
  rcases hc.1 h hh with hcan | hl
  · exact absurd hcan (no_canceled hX h hh)
  · exact hl

/-- **The event of a loader state at a copy site, and its observation.** -/
theorem loader_copy_obs (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hn : NumWordRead Q L X) (hc : Complete L X) {h k : Nat}
    {d : Loader.D} {P : Loader.Pro} (hk : k < (X.tr h).length)
    (hσ : St Q L X h k = some (some (.w (.loader d P)))) {isV slab hh : Nat}
    (hV : isV ≤ 1) (hS : slab ≤ 1) (hH : hh ≤ 1) (hs : d.site = cpSite isV slab hh) :
    ∃ (o : TensorCopy.Observation), X.TensorIssue (h, k) Q.kvMap o.spec ∧
      X.tensor (h, k) = some o ∧
      o.spec = kvCopySpec Q (h / L.block) (kvhOf L h * Q.headCols + 128 * isV + 64 * hh)
        (Q.page (reqOf L h) (2 * blkOf Q L h d.i + slab) * Q.pageRows + kvhOf L h * Q.headRows)
        (L.sharedBase + 32768 * (d.i % 3) + 98304 * isV + 8192 * slab + 16384 * hh)
        (kvReady L (h / L.block) (d.i % 3)) := by
  obtain ⟨e, he⟩ : ∃ e, X.get (h, k) = some e := ⟨_, List.getElem?_eq_getElem hk⟩
  have hg : h < L.threads := Frame.lt_of_get hX he
  obtain ⟨u, hF⟩ := fired_cont hX hf hg he hσ (by simp [ExitState])
  obtain ⟨t, hgd, hfire⟩ := hF
  have hr := hf.reach hg hσ
  have hsh := EvW.loader_shape hpre hr.2 (hf.ldRng hg hσ) (g := h) (d := d) (P := P) (u := u)
    ⟨t, ⟨hgd.1, hgd.2.2⟩, hfire⟩
  have hm : EvW.Words Q P := hr.1
  obtain ⟨t', ins, o', -, hinv, -, -⟩ := Frame.fired_site hf.sound hX he hσ
  have hI : Loader.Inv L h d ∧ Loader.ProEq L h P d ∧ Worker.Rest L h P ∧
      4 ≤ WComp.warpOf L h ∧ h % L.block < 256 := hinv.2
  obtain ⟨hbox, -, hcp⟩ := cpSite_box hV hS hH
  rw [← hs] at hbox hcp
  obtain ⟨b, hb, hev⟩ := Ring.ldShape_cp hsh hcp
  rw [hbox] at hb
  cases hb
  have hpage := loader_copy_page hpre hX hf hn hσ hbox
  have hspec := loader_copy_spec (g := h) hm hI.2.1 hV (slab := slab) (hh := hh) hpage
  have hti : X.TensorIssue (h, k) Q.kvMap (EvW.ldCopy Q L h d (decide (isV = 1), slab, hh)) :=
    ⟨_, by rw [he, hev]⟩
  obtain ⟨o, ho, -⟩ := ((asyncDrained_iff X).mp hc.2.1).2.2.2.2.1 _ _ _ hti
  obtain ⟨⟨a', ha'⟩, -⟩ := hX.tensor _ o ho
  obtain ⟨pc', hpc'⟩ := ha'
  rw [he, hev] at hpc'
  simp only [Option.some.injEq, Event.mk.injEq, Kind.tensorIssue.injEq] at hpc'
  obtain ⟨-, -, hsp⟩ := hpc'
  refine ⟨o, ?_, ho, ?_⟩
  · rw [← hsp]; exact hti
  · rw [← hsp, hspec]

/-- **The loader's half of `KvCopies`.** For a block `num_pre ≤ i < num_iters` of the CTA of a
launched thread `g` and a box `(isV, slab, hh)`, a copy of the box exists, by a loader thread of
the CTA in iteration `i`, with the spec of the box. -/
theorem loader_copy_exists (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hR : RoleReads L X) (hp : NumPreRead Q L X)
    (hn : NumWordRead Q L X) (hc : Complete L X) {g i : Nat} (isV slab hh : Nat)
    (hg : g < L.threads) (h1 : ProA.numPre Q (reqOf L g) (splitOf L g) ≤ i)
    (h2 : i < Q.numIters (reqOf L g) (splitOf L g)) (hV : isV ≤ 1) (hS : slab ≤ 1)
    (hH : hh ≤ 1) :
    ∃ (c : EvId) (o : TensorCopy.Observation) (a : Nat) (bar : Loc),
      c.1 < L.threads ∧ c.1 / L.block = g / L.block ∧ X.TensorIssue c a o.spec ∧
      X.tensor c = some o ∧ CopyBlock Q L X c i ∧
      o.spec = kvCopySpec Q (g / L.block) (kvhOf L g * Q.headCols + 128 * isV + 64 * hh)
        (Q.page (reqOf L g) (2 * blkOf Q L g i + slab) * Q.pageRows + kvhOf L g * Q.headRows)
        (L.sharedBase + 32768 * (i % 3) + 98304 * isV + 8192 * slab + 16384 * hh) bar := by
  obtain ⟨hg0, hc0, hl0⟩ := warp6_thread hpre.block hg
  obtain ⟨h, hw, hlead⟩ := exists_lead hX hpre.block hg0
  obtain ⟨⟨-, hh1, hcta⟩, hwarp⟩ := hw
  have hch : h / L.block = g / L.block := by omega
  have hw6 : h % L.block / 32 = 6 := by omega
  have hz := cta_eq hch .z
  have hx := cta_eq hch .x
  have hy := cta_eq hch .y
  obtain ⟨-, hbox, -⟩ := cpSite_box hV hS hH
  obtain ⟨k, d, P, hk, hσ, hs, hi⟩ := loader_reaches hpre hX hf hR hp hn hw6
    (exit_last hX hc hh1) hlead (i0 := i) (by rw [hz, hx]; exact h1) (by rw [hz, hx]; exact h2)
    hbox
  obtain ⟨o, hti, ho, hsp⟩ := loader_copy_obs hpre hX hf hn hc hk hσ hV hS hH hs
  refine ⟨(h, k), o, Q.kvMap, kvReady L (h / L.block) (d.i % 3), hh1, hch, hti, ho,
    .inl ⟨d, P, hσ, hi⟩, ?_⟩
  rw [hsp, hch, hi]
  unfold kvhOf reqOf blkOf splitOf
  rw [hz, hx, hy]

end
end PTX.Kernels.InklingRelDecode.Proof.Lp
