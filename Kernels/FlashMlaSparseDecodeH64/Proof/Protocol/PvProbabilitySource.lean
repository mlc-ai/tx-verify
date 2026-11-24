-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.GemmScoreRing
public import Kernels.FlashMlaSparseDecodeH64.Proof.Result.GemmProbabilityValues
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.MmaDataTrace
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0ProbabilityRelease
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.FollowedPrefix
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0Sound

@[expose] public section

/-! # The shared probability bytes consumed by an actual PV issue -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.PvProbabilitySource

open PTX PTX.Flow AsyncCopy PTX.MbarRing GemmRing MmaDataTrace

set_option maxRecDepth 4096

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

private theorem same_scope {g h : Nat} (hh : SameCta L g h) (sc : MbarScope) :
    MbarScopeIncludes L sc g h := by
  cases sc
  · exact hh
  · exact ⟨hh.1, hh.2.1, congrArg L.clusterOfCta hh.2.2⟩
  · exact ⟨hh.1, hh.2.1⟩
  · exact ⟨hh.1, hh.2.1⟩

/-- The successful PV acquire observes the selected softmax lane's actual publication of
this block, and orders the publication before the PV issue. -/
theorem actual_publication_before_pv {g i : Nat} {d : Wg1Mma.D} {issue : Fin 8} {e : Event}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ t < L.threads, (Machine.code P L t).Sound)
    (he : X.get (g, i) = some e)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.mma d)))
    (hsite : d.site = .pvMma issue) (lane : Fin 128) :
    let h := softmax L (ctaOf L g) lane
    ∃ a tag,
      X.get (h, a) = some
        ⟨tag, .arrive (GemmRing.score L (ctaOf L g) (rawSlot d.i)) 0 1 true .cta⟩ ∧
      arrivals (GemmRing.score L (ctaOf L g) (rawSlot d.i)) ((X.tr h).take a) = d.i / 2 ∧
      baseCausality L X (h, a) (g, i) := by
  let cta := ctaOf L g
  let slot := rawSlot d.i
  let h := softmax L cta lane
  let m := GemmRing.score L cta slot
  have hg := Frame.lt_of_get hX he
  have hp := Wg1MmaGemmTrace.composed_count_here hpre hg .score
    ((hs g hg).machine.produces (hX.thr g hg)) hd (show d.i % 2 = slot.val from rfl)
  simp only [hsite, Wg1MmaGemmTrace.completed, ↓reduceIte] at hp
  change okPolls m ((X.tr g).take i) = d.i / 2 + 1 at hp
  obtain ⟨w, wt, parity, acq, scope, hw, hew, hcount⟩ := Poll.exists_nth hp.ge
  obtain ⟨q, hQ⟩ := FollowedPrefix.state_at hd hw.le
  obtain ⟨_, rfl⟩ := poll_at_followed (obj := .soReady) hpre hX (hs g hg).machine
    (by rw [hQ]; simp) hew rfl
  obtain ⟨issuer, hmma, hWarp⟩ := exists_issuer_in_warp (cta := cta) hpre hX hs
  have hgIssuer := hmma g i d rfl hd (by rw [hsite]; simp)
  subst issuer
  let R := actualScoreRing (slot := slot) hpre hX hs hmma hWarp
  have hnth : Poll.nth X m g (d.i / 2) = w := by rw [← hcount, Poll.nth_eq hew]
  have hPresent : X.RefPresent (.thread (R.wE 0 (d.i / 2 + 1))) := by
    change X.RefPresent (.thread (g, Poll.nth X m g (d.i / 2 + 1 - 1)))
    rw [Nat.add_sub_cancel, hnth]
    exact ⟨_, hew⟩
  obtain ⟨hItem, hWitness⟩ := R.observes_empty hX.depAcyclic hPresent lane
  let E := actual_score_history (slot := slot) (cta := cta) hpre hX hs
  obtain ⟨_, ⟨tag, sc, hea⟩, hOrdinal⟩ := E.S_rec hItem
  let a := (Unit.it X m (softmax L cta) lane (d.i / 2)).2
  have hh := Frame.lt_of_get hX hea
  obtain ⟨hc, _, _, _, rfl, _⟩ := MachineTracking.actual_gemm_arrival
    (obj := .soReady) hpre hX hs hea rfl
  change Witness L X (.thread (h, a)) (g, Poll.nth X m g (d.i / 2 + 1 - 1)) at hWitness
  rw [Nat.add_sub_cancel, hnth] at hWitness
  have hsync : MSync L X (h, a) (g, i) :=
    ⟨(h, a), (g, w), m, .cta, scope, ⟨0, 1, tag, hea⟩, (hWitness.waitObserves hew).2,
      ⟨⟨hh, hg, hc⟩, same_scope ⟨hg, hh, hc.symm⟩ scope⟩,
      rfl, hw, PTX.len_of_get he, rfl, le_rfl⟩
  exact ⟨a, tag, hea, hOrdinal, .single (.inr (.inr (.inl hsync)))⟩

theorem publication_before_pv_of_followed {g i : Nat} {d : Wg1Mma.D} {issue : Fin 8} {e : Event}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ t < L.threads, (Machine.machine P L t).Sound)
    (he : X.get (g, i) = some e)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.mma d)))
    (hsite : d.site = .pvMma issue) (lane : Fin 128)
    (hFollow : ∀ {a tag}, let h := softmax L (ctaOf L g) lane
      let m := GemmRing.score L (ctaOf L g) (rawSlot d.i)
      X.get (h, a) = some ⟨tag, .arrive m 0 1 true .cta⟩ →
      arrivals m ((X.tr h).take a) = d.i / 2 →
      Frame.stateAt (Machine.code P L) X h a ≠ some none) :
    let h := softmax L (ctaOf L g) lane
    ∃ a q tag,
      X.get (h, a) = some
        ⟨tag, .arrive (GemmRing.score L (ctaOf L g) (rawSlot d.i)) 0 1 true .cta⟩ ∧
      Frame.stateAt (Machine.code P L) X h a = some (some (.wg0 q)) ∧
      q.site = .soReady ∧ q.block = d.i ∧ baseCausality L X (h, a) (g, i) := by
  let h := softmax L (ctaOf L g) lane
  let hs' (t : Nat) (ht : t < L.threads) := Machine.code_sound hpre ht
  obtain ⟨a, tag, ha, hOrdinal, hbase⟩ :=
    actual_publication_before_pv hpre hX hs' he hd hsite lane
  have hh := Frame.lt_of_get hX ha
  obtain ⟨⟨hc, q, hSlot, hqSite, hq⟩, _, _, _, _⟩ :=
    arrival_at_followed (obj := .soReady) hpre hX (hs h hh) (hFollow ha hOrdinal) ha rfl
  obtain ⟨hArrivals, _⟩ := Wg0GemmTrace.composed_score_counts hpre
    ((hs h hh).produces (hX.thr h hh)) hq hqSite
  rw [hc, hSlot] at hArrivals
  let m := GemmRing.score L (ctaOf L g) (rawSlot d.i)
  change arrivals m ((X.tr h).take a) = d.i / 2 at hOrdinal
  change arrivals m ((X.tr h).take a) = q.block / 2 at hArrivals
  change q.block % 2 = d.i % 2 at hSlot
  have hBlock : q.block = d.i := by omega
  exact ⟨a, q, tag, ha, hq, hqSite, hBlock, hbase⟩

theorem publication_before_pv {g i : Nat} {d : Wg1Mma.D} {issue : Fin 8} {e : Event}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ t < L.threads, (Machine.machine P L t).Sound)
    (ht : Frame.Tracked (Machine.code P L) X)
    (he : X.get (g, i) = some e)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.mma d)))
    (hsite : d.site = .pvMma issue) (lane : Fin 128) :
    let h := softmax L (ctaOf L g) lane
    ∃ a q tag,
      X.get (h, a) = some
        ⟨tag, .arrive (GemmRing.score L (ctaOf L g) (rawSlot d.i)) 0 1 true .cta⟩ ∧
      Frame.stateAt (Machine.code P L) X h a = some (some (.wg0 q)) ∧
      q.site = .soReady ∧ q.block = d.i ∧ baseCausality L X (h, a) (g, i) :=
  publication_before_pv_of_followed hpre hX hs he hd hsite lane
    (fun ha _ => ht _ _ (Frame.lt_of_get hX ha))

open Result in
/-- The selected ordinary packed store covers the PV operand's actual byte. -/
theorem selected_write_covers {h j cta : Nat} {d : Wg0.D} {site : Fin 4}
    {e : Event} {u : TState} {a : Acc} {bs : List Byte}
    (hpre : Pre P L mem0)
    (he : X.get (h, j) = some e)
    (hs : d.site = .pStore site) (hf : (Wg0.code P L h).toMachine.Fired (some d) e (some u))
    (row : Fin 128) (slot : Fin 64) (b : Fin 2)
    (hh : h = probabilityLane L cta row slot)
    (hk : site.val = slot.val % 32 / 8) (hsub : d.sub = slot.val / 2 % 4)
    (hw : X.MemWrites (.thread (h, j)) a bs) :
    X.Writes (h, j) a bs ∧
      a.Covers ⟨.shared, cta, pLinearByte L (row.val % 64) slot.val b.val⟩ := by
  obtain ⟨p, hKind, hLoc, hSize, hBound⟩ := Wg0.fired_pStore_event hpre hs hf
  have hw' : X.Writes (h, j) a bs := by
    rcases hw with hwr | ⟨_, ⟨_, hrmw⟩⟩
    · exact hwr
    · have hbad := congrArg Event.kind (Option.some.inj (he.symm.trans hrmw))
      rw [hKind] at hbad
      cases hbad
  have hEq := congrArg Event.kind (Option.some.inj (he.symm.trans hw'.choose_spec))
  rw [hKind] at hEq
  have hp := (Kind.wr.inj hEq).1
  rw [hp] at hLoc hSize
  let half : Fin 2 := ⟨slot.val % 2, Nat.mod_lt _ (by decide)⟩
  obtain ⟨address, hSiteLoc, hPoint⟩ :=
    pStore_mmaByte (block := d.block) (Wg0.head_eq L h) site ⟨d.sub, hBound⟩ half b
  rw [hs] at hLoc
  have hAddr : address = a.loc := Option.some.inj (hSiteLoc.symm.trans hLoc)
  obtain ⟨hCTA, hHead, hHalf⟩ := probabilityLane_coords hpre cta row slot
  rw [← hh] at hCTA hHead hHalf
  have hSlotEq : 32 * Wg0.half L h + 2 * (4 * site.val + d.sub) + half.val = slot.val := by
    rw [hHalf, hk, hsub]
    dsimp [half]
    omega
  change address.at (2 * half.val + b.val) =
    ⟨.shared, ctaOf L h, pLinearByte L (Wg0.head L h)
      (32 * Wg0.half L h + 2 * (4 * site.val + d.sub) + half.val) b.val⟩ at hPoint
  rw [hAddr, hCTA, hHead, hSlotEq] at hPoint
  refine ⟨hw', ?_⟩
  rw [← hPoint]
  have hH := half.isLt
  have hB := b.isLt
  apply Acc.covers_at
  rw [hSize]
  omega

/-- A PV A byte is covered by its own block's packed probability write. The writer's
actual shared proxy fence and the MMA lane's matching acquire order that byte before PV. -/
theorem selected_byte_before_pv_of_followed {g i : Nat} {d : Wg1Mma.D} {issue : Fin 8}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ t < L.threads, (Machine.code P L t).Sound)
    (hi : X.MmaIssue (g, i) (Wg1Mma.pvDest issue) (pvOperands L g d.i issue)
      (pvAccum d.i issue) [0, 0, 0, 0])
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.mma d)))
    (hsite : d.site = .pvMma issue) (row : Fin 128) (k : Fin 16) (b : Fin 2)
    (hFollow : ∀ {a tag}, let slot : Fin 64 := ⟨pvSlot issue k, by unfold pvSlot; omega⟩
      let h := Result.probabilityLane L (ctaOf L g) row slot
      let m := GemmRing.score L (ctaOf L g) (rawSlot d.i)
      X.get (h, a) = some ⟨tag, .arrive m 0 1 true .cta⟩ →
      arrivals m ((X.tr h).take a) = d.i / 2 →
      Frame.stateAt (Machine.code P L) X h a ≠ some none) :
    let slot : Fin 64 := ⟨pvSlot issue k, by unfold pvSlot; omega⟩
    let h := Result.probabilityLane L (ctaOf L g) row slot
    let site : Fin 4 := ⟨slot.val % 32 / 8, by omega⟩
    let loc : Loc := ⟨.shared, ctaOf L g, pLinearByte L (row.val % 64) slot.val b.val⟩
    ∃ j w e u a bs, X.get (h, j) = some e ∧
      Frame.stateAt (Machine.code P L) X h j = some (some (.wg0 w)) ∧
      w.block = d.i ∧ w.site = .pStore site ∧ w.sub = slot.val / 2 % 4 ∧
      (Wg0.code P L h).toMachine.Fired (some w) e (some u) ∧
      X.MemWrites (.thread (h, j)) a bs ∧
      wbyte a bs loc = some (.float .bf16 (w.pw (row.val % 64) slot.val), b.val) ∧
      X.MmaFootprint (g, i) false (2 * (row.val * 16 + k.val) + b.val) loc ∧
      ProxyBefore L X (h, j) (g, i) loc := by
  let slot : Fin 64 := ⟨pvSlot issue k, by unfold pvSlot; omega⟩
  let h := Result.probabilityLane L (ctaOf L g) row slot
  let site : Fin 4 := ⟨slot.val % 32 / 8, by omega⟩
  let sub : Fin 4 := ⟨slot.val / 2 % 4, Nat.mod_lt _ (by decide)⟩
  let half : Fin 2 := ⟨slot.val % 2, Nat.mod_lt _ (by decide)⟩
  let loc : Loc := ⟨.shared, ctaOf L g, pLinearByte L (row.val % 64) slot.val b.val⟩
  let lane : Fin 128 := ⟨64 * (slot.val / 32) + row.val % 64, by
    have := slot.isLt
    omega⟩
  have hh : softmax L (ctaOf L g) lane = h := by
    simp [softmax, h, Result.probabilityLane, lane, Nat.add_assoc]
  obtain ⟨a, q, atag, ha, hq, hQSite, hQBlock, hAfter⟩ :=
    publication_before_pv_of_followed hpre hX (fun t ht' => (hs t ht').machine)
      hi.choose_spec hd hsite lane (by
        intro i tag
        dsimp only
        intro hGet hOrd
        rw [hh] at hGet hOrd ⊢
        exact hFollow hGet hOrd)
  rw [hh] at ha hq hAfter
  have hH := Frame.lt_of_get hX ha
  have hG := Frame.lt_of_get hX hi.choose_spec
  obtain ⟨f, ft, haf, hf, j, hjf, w, e, u, he, hw, hBlock, hSite, hSub, hFired⟩ :=
    Wg0ProbabilityRelease.actual_store_before_publication hX (hs h hH).machine ha hq hQSite site sub
  obtain ⟨hc, hhead, hhalf⟩ := Result.probabilityLane_coords hpre (ctaOf L g) row slot
  obtain ⟨access, bs, hwrite, hbyte⟩ := Result.probability_write_byte hpre hSite he hFired half b
  have hslot : 32 * Wg0.half L h + 2 * (4 * site.val + w.sub) + half.val = slot.val := by
    rw [hhalf, hSub]
    dsimp [site, sub, half]
    omega
  rw [hslot, hhead, hc] at hbyte
  have hFoot : X.MmaFootprint (g, i) false (2 * (row.val * 16 + k.val) + b.val) loc :=
    .inl ⟨_, _, _, _, hi, pvProbabilityByte L g d.i issue row k b⟩
  have hBefore : baseCausality L X (h, j) (h, f) :=
    .single (.inl (po_of_not_access rfl hjf (PTX.len_of_get hf) (by rw [hf]; rfl)))
  have hfa : baseCausality L X (h, f) (h, a) :=
    .single (.inl (po_of_source_not_access rfl (by omega) (PTX.len_of_get ha) (by rw [hf]; rfl)))
  have hproxy : ProxyBefore L X (h, j) (g, i) loc :=
    ⟨(h, f), _, none, ⟨ft, hf⟩, hH, ⟨rfl, hc.symm⟩,
      ⟨hH, hG, congrArg L.clusterOfCta hc⟩, hBefore, hfa.trans hAfter⟩
  exact ⟨j, w, e, u, access, bs, he, hw, hBlock.trans hQBlock, hSite, hSub,
    hFired, hwrite, hbyte, hFoot, hproxy⟩

theorem selected_byte_before_pv {g i : Nat} {d : Wg1Mma.D} {issue : Fin 8}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ t < L.threads, (Machine.code P L t).Sound)
    (ht : Frame.Tracked (Machine.code P L) X)
    (hi : X.MmaIssue (g, i) (Wg1Mma.pvDest issue) (pvOperands L g d.i issue)
      (pvAccum d.i issue) [0, 0, 0, 0])
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.mma d)))
    (hsite : d.site = .pvMma issue) (row : Fin 128) (k : Fin 16) (b : Fin 2) :
    let slot : Fin 64 := ⟨pvSlot issue k, by unfold pvSlot; omega⟩
    let h := Result.probabilityLane L (ctaOf L g) row slot
    let site : Fin 4 := ⟨slot.val % 32 / 8, by omega⟩
    let loc : Loc := ⟨.shared, ctaOf L g, pLinearByte L (row.val % 64) slot.val b.val⟩
    ∃ j w e u a bs, X.get (h, j) = some e ∧
      Frame.stateAt (Machine.code P L) X h j = some (some (.wg0 w)) ∧
      w.block = d.i ∧ w.site = .pStore site ∧ w.sub = slot.val / 2 % 4 ∧
      (Wg0.code P L h).toMachine.Fired (some w) e (some u) ∧
      X.MemWrites (.thread (h, j)) a bs ∧
      wbyte a bs loc = some (.float .bf16 (w.pw (row.val % 64) slot.val), b.val) ∧
      X.MmaFootprint (g, i) false (2 * (row.val * 16 + k.val) + b.val) loc ∧
      ProxyBefore L X (h, j) (g, i) loc :=
  selected_byte_before_pv_of_followed hpre hX hs hi hd hsite row k b
    (fun ha _ => ht _ _ (Frame.lt_of_get hX ha))

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.PvProbabilitySource
