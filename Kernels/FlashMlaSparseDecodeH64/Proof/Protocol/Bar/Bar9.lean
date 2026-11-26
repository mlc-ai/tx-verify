-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Bar.Ord
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MemRows.Wg0
public import Lemmas.Protocol.NamedBarSources
public import Lemmas.Protocol.CountNth
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.NoBarArrive
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Rounds
public import Lemmas.TensorStore.TensorStoreCompleteConsistentReadSource

@[expose] public section

/-! # Barrier 9 publishes the output staging tiles

-- domain: consistent

Output chunk `c`'s tile of warp `w < 2` is read by the tensor store of the elected lane of warp
`w` (`MemRow.wg0OutOff`); its byte `y` of element `el` of chunk `k ^^^ h % 8` of row `h` is the
staging store `k`, element `el` of thread `t = 64 w + h` of the CTA (`MemRow.Wg0Stage`). That
thread made the store, then a `fence.proxy.async.shared::cta`, then its barrier-9 arrival of
ordinal `2 R + 2 + c` (`R` the CTA's block count); the issuer passed its own barrier-9 event of
that ordinal before the store. The member's arrival exists (`Sources.member_arrival`; an exiting
lane made all its barrier-9 arrivals), the two arrivals synchronize
(`Sources.same_ordinal_baseCausality`), so the store is `ProxyBefore` the read: the read of the
byte has the staging write as a cause (`out_pub`, the class `Prog.StorePub`).

Barrier 9 is warpgroup 0's (`bar9_sources`, from the barrier rows: four warps, 128 threads).

**Input (`OutRows`, warpgroup 0's trace facts, not exports yet)**: `issue` (a tensor store is
chunk `c`'s of a lane of warps 0 and 1, after a barrier-9 event of ordinal `2 R + 2 + c`, reading
the slots of its tile); `stage` (before a barrier-9 event of ordinal `2 R + 2 + c` a lane of
warpgroup 0 made a proxy fence and before it its 32 staging stores of chunk `c`); `exit` (an
exiting lane of warpgroup 0 made at least `2 R + 6` barrier-9 events). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow MbarRow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- The barrier-9 ordinal of output chunk `c`'s barrier in a CTA of `R` blocks. -/
def outOrd (R c : Nat) : Nat := 2 * R + 2 + c

/-- **Warpgroup 0's output trace facts** (proposed exports; see the header). -/
structure OutRows (P : Params) (L : Launch) (X : Execution) : Prop where
  issue : ∀ {g k a : Nat} {s : TensorStore.Spec}, X.TensorStoreIssue (g, k) a s →
    warp L g < 2 ∧ ∃ c < 4, (∀ slot, ∃ h < 64, ∃ k < 8, ∃ el < 4, ∃ y < 4,
      s.sharedLoc slot = wsLoc L (g / L.block) (65536 + 16384 * warp L g + MemRow.wg0OutOff c +
        (128 * h + 16 * (k ^^^ h % 8) + 4 * el + y))) ∧
      ∃ j pc, j < k ∧ X.get (g, j) = some ⟨pc, .bar 9 (some 128) .sync⟩ ∧
        ((X.tr g).take j).countP (Execution.isBarId 9) = outOrd (blocksOf P L (g / L.block)) c
  stage : ∀ {y j pc c : Nat}, y < L.threads → warp L y < 4 → c < 4 →
    X.get (y, j) = some ⟨pc, .bar 9 (some 128) .sync⟩ →
    ((X.tr y).take j).countP (Execution.isBarId 9) = outOrd (blocksOf P L (y / L.block)) c →
    ∃ f < j, X.IsProxyFence (y, f) (.async (some (.shared .cta))) none ∧
      ∀ k < 8, ∀ el < 4, ∃ i < f, ∃ a bs, X.Writes (y, i) a bs ∧ a.size = 4 ∧
        a.loc = wsLoc L (y / L.block) (65536 + 16384 * ((L.tidOf y).x / 64) +
          128 * ((L.tidOf y).x % 64) + 16 * (k ^^^ (L.tidOf y).x % 8) + MemRow.wg0OutOff c +
          4 * el)
  exit : ∀ {y j pcx : Nat}, warp L y < 4 → X.get (y, j) = some ⟨pcx, .exit⟩ →
    outOrd (blocksOf P L (y / L.block)) 4 ≤ (X.tr y).countP (Execution.isBarId 9)

/-- The four warps of warpgroup 0. -/
def wg0Warps : Finset Nat := Finset.range 4

/-- **Barrier 9 is warpgroup 0's**, of 128 threads. -/
theorem bar9_sources (hp : Pre P L m) (hR : BarRows P L X) :
    NamedBar.Sources L X (some 128) wg0Warps 9 := by
  rintro ⟨g, k⟩ pc cnt ⟨md, he⟩ hg
  have hc := bar_cnt hR hg he
  refine ⟨?_, hc⟩
  rcases bar_cls (bar_use hR hg he rfl) with ⟨-, h⟩ | ⟨⟨hw, -⟩, -⟩ | ⟨-, -, h⟩
  · simp only [BarRow.Cta, Kind.bar.injEq] at h
    omega
  · simp only [wg0Warps, Finset.mem_range]
    simp only [warp, tidOf_x_eq hp] at hw
    rw [hp.block]
    exact hw
  · simp only [Kind.bar.injEq] at h
    omega

/-- Barrier 9's shape: four warps, 128 threads. -/
theorem bar9_shape (hp : Pre P L m) : NamedBar.Shape L (some 128) wg0Warps 9 :=
  { pos := by decide
    target := by rw [hp.block]; rfl
    bound := fun w hw => by
      rw [hp.block]
      exact (Finset.mem_range.mp hw).trans_le (by decide)
    id_lt := by decide }

/-- A store's slot read reads the slot's shared byte. -/
theorem store_readLoc (s : TensorStore.Spec) (slot : TensorTransfer.Slot s.descriptor) :
    TensorStore.readLoc s slot.1.val slot.2.1.val slot.2.2.val = some (s.sharedLoc slot) := by
  have hslotAt : TensorTransfer.slotAt s.descriptor slot.1.val slot.2.1.val slot.2.2.val =
      some slot := by
    simp only [TensorTransfer.slotAt, dite_eq_left slot.1.isLt, dite_eq_left slot.2.1.isLt,
      dite_eq_left slot.2.2.isLt]
  simp only [TensorStore.readLoc, hslotAt, Option.map_some]

/-- **The writer of an output byte**: the staging store, made by a thread of warpgroup 0 (warp
below 4), ordered before the tensor store's read of the byte. -/
theorem out_pub_stage (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hR : BarRows P L X) (hO : OutRows P L X) {i : EvId} {a : Nat} {s : TensorStore.Spec}
    (hi : X.TensorStoreIssue i a s) (slot : TensorTransfer.Slot s.descriptor) :
    ∃ yw iw b bs, X.Writes (yw, iw) b bs ∧ warp L yw < 4 ∧ b.Covers (s.sharedLoc slot) ∧
      ByteCausality L X (s.sharedLoc slot) (.thread (yw, iw)) (storeSlotReadRef i slot) := by
  obtain ⟨g, k⟩ := i
  obtain ⟨pci, hgi⟩ := hi
  have hg : g < L.threads := Frame.lt_of_get hX hgi
  have hkl : k < (X.tr g).length := (List.getElem?_eq_some_iff.mp hgi).1
  obtain ⟨hw2, c, hc, hslot, j, pcj, hjk, hj, hjo⟩ := hO.issue ⟨pci, hgi⟩
  obtain ⟨h, hh, kk, hkk, el, hel, y, hy, hl⟩ := hslot slot
  have hb := hp.block
  -- the writer: thread `64 w + h` of the CTA
  set t := 64 * warp L g + h with ht
  have hwg : warp L g = (L.tidOf g).x / 32 := rfl
  have htx : (L.tidOf g).x = g % 384 := tidOf_x_eq hp g
  have ht128 : t < 128 := by omega
  set yw := g / L.block * L.block + t with hyw
  have hyc : yw / L.block = g / L.block := by rw [hyw, hb]; omega
  have hyt : yw < L.threads := by
    have h1 : g / L.block < L.grid := by
      have : g < L.grid * L.block := hg
      exact (Nat.div_lt_iff_lt_mul (by rw [hb]; omega)).mpr this
    show yw < L.grid * L.block
    rw [hyw, hb] at *
    have : g / 384 + 1 ≤ L.grid := h1
    nlinarith
  have hym : yw % L.block = t := by rw [hyw, hb]; omega
  have hyx : (L.tidOf yw).x = t := by rw [tidOf_x_eq hp, ← hb, hym]
  have hyw4 : warp L yw < 4 := by simp only [warp, hyx]; omega
  have hcta : SameCta L yw g := ⟨hyt, hg, hyc⟩
  -- the writer's arrival of the issuer's ordinal
  have hS := bar9_sources hp hR
  have hG := bar9_shape hp
  have hmem : (yw % L.block) / 32 ∈ wg0Warps := by
    simp only [wg0Warps, Finset.mem_range, hym]
    omega
  obtain ⟨jw, pcw, hjw, hjwo⟩ := hS.member_arrival hX hG (f := (g, j)) hj (by simp only; omega)
    hyc hmem fun ⟨jx, pcx, hx⟩ => by
      have h6 := hO.exit hyw4 hx
      rw [hyc] at h6
      obtain ⟨n, ev, hn, hbn, hcn⟩ := MbarRing.Slot.exists_nth_countP (Execution.isBarId 9)
        (show outOrd (blocksOf P L (g / L.block)) c + 1 ≤ (X.tr yw).countP (Execution.isBarId 9)
          by simp only [outOrd] at h6 ⊢; omega)
      obtain ⟨pce, kd⟩ := ev
      cases kd <;> simp only [Execution.isBarId, Bool.false_eq_true] at hbn
      rename_i id cnt md
      simp only [beq_iff_eq] at hbn
      subst hbn
      have hget : X.get (yw, n) = some ⟨pce, .bar 9 cnt md⟩ := hn
      have hcn' := bar_cnt hR hyt hget
      have hmd := bar_sync hR hyt hget
      subst hcn' hmd
      exact ⟨n, pce, hget, by rw [hcn, hjo]⟩
  obtain ⟨f, hfj, hfence, hst⟩ := hO.stage hyt hyw4 hc hjw (by rw [hjwo, hjo, hyc])
  obtain ⟨iw, hif, aw, bsw, hwr, hsz, hloc⟩ := hst kk hkk el hel
  have hl0 : s.sharedLoc slot = ⟨.shared, g / L.block, aw.loc.addr + y⟩ := by
    rw [hl, hloc]
    simp only [wsLoc, hyx, hyc, Loc.mk.injEq, true_and]
    have h1 : t / 64 = warp L g := by omega
    have h2 : t % 64 = h := by omega
    have h3 : t % 8 = h % 8 := by omega
    rw [h1, h2, h3]
    omega
  have hcov : aw.Covers (s.sharedLoc slot) := by
    rw [hl0]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hloc]; rfl
    · rw [hloc]; simp only [wsLoc, hyc]
    · simp only
      omega
    · simp only
      omega
  have hfb : baseCausality L X (yw, iw) (yw, f) := by
    obtain ⟨pcf, hf⟩ := hfence
    have hlen : f < (X.tr yw).length := (List.getElem?_eq_some_iff.mp hf).1
    exact .single (.inl ⟨rfl, hif, hlen, by simp [SameAccess, hf, Event.acc]⟩)
  have hsync := hS.same_ordinal_baseCausality hX hG hcta hjw (show X.IsBarrier (g, j) 9 _ pcj
    from hj) (by omega) hjwo hfj hjk hkl
  have hproxy : ProxyBefore L X (yw, iw) (g, k) (s.sharedLoc slot) :=
    ⟨(yw, f), some (.shared .cta), none, hfence, hyt, ⟨by rw [hl0], by rw [hl0, hyc]⟩,
      ⟨hyt, hg, congrArg L.clusterOfCta hyc⟩, hfb, hsync⟩
  refine ⟨yw, iw, aw, bsw, hwr, hyw4, hcov, .direct ⟨?_, .inl hproxy⟩⟩
  refine ⟨⟨s.sharedLoc slot, 1, false, false, .cta, 0, false⟩, false,
    ⟨rfl, s, a, ⟨pci, hgi⟩, store_readLoc s slot, rfl⟩, rfl, rfl, Nat.le_refl _, ?_⟩
  change (s.sharedLoc slot).addr < (s.sharedLoc slot).addr + 1
  omega

/-- **The output stores' publication**: every byte an output tensor store reads has a staging
write ordered before the read (`Prog.StorePub`). -/
theorem out_pub (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hR : BarRows P L X) (hO : OutRows P L X) {i : EvId} {a : Nat} {s : TensorStore.Spec}
    (hi : X.TensorStoreIssue i a s) (slot : TensorTransfer.Slot s.descriptor) :
    ∃ w b bs, X.MemWrites w b bs ∧ b.Covers (s.sharedLoc slot) ∧
      ByteCausality L X (s.sharedLoc slot) w (storeSlotReadRef i slot) := by
  obtain ⟨yw, iw, b, bs, hw, -, hc, hb⟩ := out_pub_stage hp hX hR hO hi slot
  exact ⟨.thread (yw, iw), b, bs, .inl hw, hc, hb⟩

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
