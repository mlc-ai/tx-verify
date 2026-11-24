-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof2.Safety.Placed
public import Kernels.InklingRelDecode.Proof2.Lib.QTile
public import Lemmas.Protocol.RegionOrderExcept

@[expose] public section

/-! # The orders of the role word and the Q tile on the role table

Two regions of `Safety.SharedOrder`, from the role table's footprints and barrier 1's hand-off:

* `async_shared`: an asynchronous access of a shared byte is an MMA operand read (the A operand in
  the Q tile, the B operand in the rings) or a tensor copy's write (in the rings), of the issuer's
  CTA, below `sharedBase + 212992`.
* **The role word** (`role_ordered`): its accesses are the prologue's `st8` (barrier-1 count 0),
  the epilogue's `stTab` (count 3), both with one value from every default thread, and the
  dispatch's role-byte reads (count 1 or at least 4, `role_byte`). An access with fewer
  barrier-1 events before it is before one of another thread of its CTA with more (`b1_before`,
  `bar1_handoff`); with equal counts the two are stores of one word with one value, which the
  statement exempts.
* **The Q tile** (`q_ordered`): its accesses are the prologue's query stores (`q_thread`: the
  address determines the thread, `Lp.qOff_inj`) and the QK MMAs' A reads. A store is before the
  issue of every MMA of its CTA through its thread's proxy fence `fnc1` (`stq_fence`: the fence
  lies between the store and the thread's first barrier-1 arrival), which barrier 1 orders before
  the MMA warp's events (`ProxyBefore`).
-/

namespace PTX.Kernels.InklingRelDecode.Proof2
open PTX PTX.Proof PTX.Flow PTX.Frame
open PTX.Kernels.InklingRelDecode.Proof.Safety (InRole InQ)

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-! ### Asynchronous accesses of shared memory -/

/-- **An asynchronous access of a shared byte** is an MMA operand read from an MMA warp state
(the A operand in the Q tile, the B operand in the rings) or a tensor copy's write (in the rings),
of the issuer's CTA. -/
theorem async_shared (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    {i : EvId} {p : AsyncCopy.Part} {a : Acc} {w : Bool} {l : Loc}
    (hI : X.Intent (.async i p) a w) (hc : a.Covers l) (hsp : l.space = .shared) :
    i.1 < L.threads ∧ l.cta = i.1 / L.block ∧ L.sharedBase ≤ l.addr ∧
      ((∃ isB idx, p = .mmaRead isB idx ∧ w = false ∧ i.2 < (X.tr i.1).length ∧
          (∃ tm d P n, Frame.stateAt (thread Q L) X i.1 i.2 =
            some (some (.inr ⟨.inl (.worker tm), .mma d P⟩, n))) ∧
          (isB = false → InQ L l) ∧ (isB = true → l.addr < L.sharedBase + 196608)) ∨
        (∃ x y z, p = .write (.load x y z) ∧ w = true ∧ l.addr < L.sharedBase + 196608)) := by
  obtain ⟨hw, hfp⟩ := hI
  have hsa : a.loc.space = .shared := hc.1.symm.trans hsp
  cases p with
  | mmaRead isB index =>
    obtain ⟨hsz, hmf⟩ := hfp
    rcases hmf with ⟨d, s, acc, mask, ⟨pc, he⟩, hb⟩ | ⟨c, k, cta, hcp, -⟩
    · have hg := Frame.lt_of_get hX he
      obtain ⟨tm, dd, P, n, hσ, hsh⟩ := mma_ev_state hp hX he
      obtain ⟨hB, hA⟩ := Proof.Safety.mma_foot hp hsh
      obtain ⟨-, hc2, hlo, hhi⟩ := hc
      cases isB
      · obtain ⟨h1, h2, h3, h4⟩ := hA _ _ hb
        exact ⟨hg, hc2.trans h2, by omega, .inl ⟨false, index, rfl, hw,
          (List.getElem?_eq_some_iff.mp he).1, ⟨tm, dd, P, n, hσ⟩,
          (fun _ => ⟨hsp, by omega, by omega⟩), (fun h => absurd h (by decide))⟩⟩
      · obtain ⟨h1, h2, h3, h4⟩ := hB _ _ hb
        exact ⟨hg, hc2.trans h2, by omega, .inl ⟨true, index, rfl, hw,
          (List.getElem?_eq_some_iff.mp he).1, ⟨tm, dd, P, n, hσ⟩,
          (fun h => absurd h (by decide)), (fun _ => by omega)⟩⟩
    · exact absurd hcp (no_cp hX _ _)
  | readLoad x y k =>
    obtain ⟨s, addr, -, hloc, -⟩ := hfp
    have h := sourceLoc_global hloc
    rw [h] at hsa
    exact absurd hsa (by simp)
  | readCopy =>
    rcases hfp with ⟨s, ⟨pc, he⟩, -⟩ | ⟨pc, he⟩
    · exact absurd he (no_copy hX)
    · exact absurd he (no_bulkPrefetch hX)
  | readStore x y k =>
    obtain ⟨s, addr, ⟨pc, he⟩, -⟩ := hfp
    exact absurd he (no_tensorStore hX)
  | readPrefetch x y k =>
    obtain ⟨s, addr, ⟨pc, he⟩, -⟩ := hfp
    exact absurd he (no_tensorPrefetch hX)
  | writeLoad x y k =>
    obtain ⟨s, addr, ⟨pc, hget⟩, hloc, hsz⟩ := hfp
    have hg := Frame.lt_of_get hX hget
    obtain ⟨col, row, dst, bar, hs, hr1, hr2⟩ := copy_ring hp hX hget
    rw [hs] at hloc
    obtain ⟨h1, h2, h3, h4⟩ := Proof.Ring.Foot.copy_foot Q (i.1 / L.block) col row dst bar hloc
    obtain ⟨-, hc2, hlo, hhi⟩ := hc
    exact ⟨hg, hc2.trans h2, by omega, .inr ⟨x, y, k, rfl, hw, by omega⟩⟩
  | writeStore x y k =>
    obtain ⟨s, addr, ⟨pc, he⟩, -⟩ := hfp
    exact absurd he (no_tensorStore hX)
  | writeCta c =>
    obtain ⟨s, targets, ⟨pc, he⟩, -⟩ := hfp
    exact absurd he (no_clc hX)
  | writeCopy =>
    obtain ⟨s, ⟨pc, he⟩, -⟩ := hfp
    exact absurd he (no_copy hX)
  | writeElem j =>
    obtain ⟨s, ⟨pc, he⟩, -⟩ := hfp
    exact absurd he (no_copy hX)
  | oldStore x y k =>
    obtain ⟨s, r, ⟨pc, he⟩, -⟩ := hfp
    exact absurd he (no_tensorStore hX)
  | oldElem j =>
    obtain ⟨s, r, ⟨pc, he⟩, -⟩ := hfp
    exact absurd he (no_copy hX)
  | readCta c => exact hfp.elim
  | readElem j => exact hfp.elim
  | writePrefetch x y k => exact hfp.elim
  | oldCopy => exact hfp.elim
  | oldLoad x y k => exact hfp.elim
  | oldCta c => exact hfp.elim
  | oldPrefetch x y k => exact hfp.elim
  | notifyCopy => exact hfp.elim
  | notifyLoad => exact hfp.elim
  | notifyCta c => exact hfp.elim
  | readsDone => exact hfp.elim
  | fullDone => exact hfp.elim
  | resolve => exact hfp.elim
  | tcNotify r => exact hfp.elim
  | mmaDone => exact hfp.elim
  | arriveOn => exact hfp.elim

/-! ### Orders of thread accesses -/

/-- **Overlapping accesses of one thread are ordered** (program order). -/
theorem same_thread {k k' : Nat} {a b : Acc} {we wf : Bool} {l : Loc}
    (he : X.Access (g, k) a we) (hf : X.Access (g, k') b wf) (hne : k ≠ k') (hov : a.Overlap b) :
    modelCausality L X l (.thread (g, k)) (.thread (g, k')) ∨
      modelCausality L X l (.thread (g, k')) (.thread (g, k)) := by
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · exact .inl (.inl (.single (.inl (po_of_overlap he hf rfl hlt hov))))
  · exact .inr (.inl (.single (.inl (po_of_overlap hf he rfl hlt hov.symm))))

/-- **Two writes of one footprint and the same bytes are `SameValueWrites`.** -/
theorem same_value (hX : Consistent L kernel Assumptions.all m X) {e f : EvId} {pc pc' : Nat}
    {a b : Acc} {bs : List Byte} (he : X.get e = some ⟨pc, .wr a bs⟩)
    (hf : X.get f = some ⟨pc', .wr b bs⟩) (hl : a.loc = b.loc) (hz : a.size = b.size) :
    SameValueWrites X (.thread e) (.thread f) a b := by
  refine ⟨.inr (.inl ⟨bs, ⟨pc, he⟩, rfl⟩), .inr (.inl ⟨bs, ⟨pc', hf⟩, rfl⟩), ⟨hl, hz⟩, ?_⟩
  intro b1 b2 h1 h2
  rcases h1 with ⟨p1, h1⟩ | ⟨o1, p1, h1⟩
  · rcases h2 with ⟨p2, h2⟩ | ⟨o2, p2, h2⟩
    · rw [he] at h1
      rw [hf] at h2
      simp only [Option.some.injEq, Event.mk.injEq, Kind.wr.injEq] at h1 h2
      rw [← h1.2.2, ← h2.2.2]
    · exact absurd h2 (no_rmw hX)
  · exact absurd h1 (no_rmw hX)

/-- **Barrier-1 order.** An event that is no barrier-1 event is before every event of a thread of
its CTA with more barrier-1 events before it (`bar1_handoff`). -/
theorem b1_before (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    {h e f : Nat} (hg : g < L.threads) (hh : h < L.threads) (hc : g / L.block = h / L.block)
    {ev : Event} (he : X.get (g, e) = some ev) (hnb : Execution.isBarId 1 ev = false)
    (hlt : c1 X g e < c1 X h f) (hf : f < (X.tr h).length) :
    baseCausality L X (g, e) (h, f) := by
  have hb : L.block = 256 := hp.block
  refine bar1_handoff hp hX g h e f ⟨⟨hg, hh, hc⟩, ?_, trivial⟩ hf ?_
  · have := Nat.mod_lt g (show 0 < L.block by omega)
    simp only [Finset.mem_range, CtaBarrier.warps, hb]
    omega
  · have he' : (X.tr g)[e]? = some ev := he
    simp only [c1] at hlt
    simp only [List.take_add_one, he', Option.toList_some, List.countP_append,
      List.countP_singleton, hnb]
    simpa using hlt

/-! ### The role word -/

/-- **An access of a byte of the role word** is a thread's: a store of the role word with the
prologue's value at barrier-1 count 0 or the epilogue's at count 3, or a read at count 1 or at
least 4. -/
theorem role_acc (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    {r : AsyncCopy.Ref} {c : Acc} {v : Bool} {l : Loc} (hI : X.Intent r c v) (hc : c.Covers l)
    (hl : InRole L l) :
    ∃ g k ev, r = .thread (g, k) ∧ g < L.threads ∧ l.cta = g / L.block ∧
      X.get (g, k) = some ev ∧ Execution.isBarId 1 ev = false ∧
      ((v = true ∧ c = roleAcc L (g / L.block) ∧ ∃ pc bs x, ev = ⟨pc, .wr c bs⟩ ∧
          ((x = 16777730 ∧ c1 X g k = 0) ∨ (x = 50529027 ∧ c1 X g k = 3)) ∧
          ∃ w, storeValue 32 (b32 x) = .ok w ∧ bs = w.toBytes) ∨
        (v = false ∧ (c1 X g k = 1 ∨ 4 ≤ c1 X g k))) := by
  obtain ⟨hsp, hlo, hhi⟩ := hl
  have hsr := hp.sharedRange
  unfold sharedBytes at hsr
  rcases r with ⟨g, k⟩ | ⟨i, p⟩
  · have hsa : c.loc.space = .shared := hc.1.symm.trans hsp
    rcases hI with ⟨bs, ⟨pc, he⟩, rfl⟩ | ⟨bs, ⟨pc, he⟩, rfl⟩ | ⟨old, new, pc, he⟩
    · have hg := Frame.lt_of_get hX he
      obtain ⟨hcta, -, -⟩ := rd_placed hp hX he hsa hc
      obtain ⟨-, hcc, hca, hcb⟩ := hc
      cases rd_class hp hX he hsa with
      | base h hz => simp only [h, hz] at hca hcb; omega
      | role h4 hpc h hz =>
        subst hpc
        obtain ⟨-, -, hcnt, -, -⟩ := role_byte hp hX he
        exact ⟨g, k, _, rfl, hg, hcta, he, by simp [Execution.isBarId], .inr ⟨rfl, hcnt⟩⟩
      | pair _ _ hz h => rw [hz] at hcb; omega
      | scratch h hz => simp only [h, hz] at hca hcb; omega
    · have hg := Frame.lt_of_get hX he
      obtain ⟨hcta, -, -⟩ := wr_placed hp hX he hsa hc
      obtain ⟨ha, -, hcase⟩ := role_wr_info hp hX he hc ⟨hsp, hcta, hlo, hhi⟩
      refine ⟨g, k, _, rfl, hg, hcta, he, by simp [Execution.isBarId], .inl ⟨rfl, ha, ?_⟩⟩
      rcases hcase with ⟨w, hw, hb, hn⟩ | ⟨w, hw, hb, hn⟩
      · exact ⟨pc, bs, _, rfl, .inl ⟨rfl, hn⟩, w, hw, hb⟩
      · exact ⟨pc, bs, _, rfl, .inr ⟨rfl, hn⟩, w, hw, hb⟩
    · exact absurd he (no_rmw hX)
  · obtain ⟨-, -, -, hcl⟩ := async_shared hp hX hI hc hsp
    exfalso
    rcases hcl with ⟨isB, idx, -, -, -, -, hq, hk⟩ | ⟨x, y, z, -, -, h⟩
    · cases isB
      · have := (hq rfl).2.2; omega
      · have := hk rfl; omega
    · omega

/-- **The conflicting accesses of the role word are ordered**, but for two stores of one word. -/
theorem role_ordered (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X) :
    ConflictsOrderedExcept L X (InRole L) := by
  intro e f a b l hc ha hb hl hS
  obtain ⟨hne, we, wf, hie, hif, hw, hov⟩ := hc
  obtain ⟨g, k, ev, rfl, hg, hcg, hev, hnb, hcl⟩ := role_acc hp hX hie ha hl
  obtain ⟨g', k', ev', rfl, hg', hcg', hev', hnb', hcl'⟩ := role_acc hp hX hif hb hl
  by_cases hgg : g = g'
  · subst hgg
    exact same_thread hie hif (fun h => hne (by rw [h])) hov
  have hcta : g / L.block = g' / L.block := hcg.symm.trans hcg'
  have hk' : k' < (X.tr g').length := (List.getElem?_eq_some_iff.mp hev').1
  have hk : k < (X.tr g).length := (List.getElem?_eq_some_iff.mp hev).1
  rcases lt_trichotomy (c1 X g k) (c1 X g' k') with hlt | heq | hgt
  · exact .inl (.inl (b1_before hp hX hg hg' hcta hev hnb hlt hk'))
  · exfalso
    rcases hcl with ⟨rfl, rfl, pc, bs, x, rfl, hx, w, hw1, rfl⟩ | ⟨rfl, h0⟩ <;>
      rcases hcl' with ⟨rfl, rfl, pc', bs', x', rfl, hx', w', hw1', rfl⟩ | ⟨rfl, h0'⟩
    · have hxx : x = x' := by omega
      subst hxx
      rw [hw1'] at hw1
      obtain rfl := Except.ok.inj hw1
      exact hS (same_value hX hev hev' (by rw [hcta]) rfl)
    · omega
    · omega
    · rcases hw with h | h <;> cases h
  · exact .inr (.inl (b1_before hp hX hg' hg hcta.symm hev' hnb' hgt hk))

/-! ### The Q tile -/

/-- **A thread access of a byte of the Q tile is a query store** of a default thread of the byte's
CTA, from its prologue state at the store, at the store's address. -/
theorem q_thread (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X) {k : Nat}
    {c : Acc} {v : Bool} {l : Loc} (hI : X.Access (g, k) c v) (hc : c.Covers l) (hl : InQ L l) :
    v = true ∧ g < L.threads ∧ g % L.block < 128 ∧ l.cta = g / L.block ∧
      ∃ (i : Fin 8) (j : Fin 4) (tm : Nat) (bw : Value) (dt : Proof.ProA.Dat) (n : Cls → Nat),
        Frame.stateAt (thread Q L) X g k =
          some (some (.inr ⟨.inl (.dp tm bw), .inl ⟨.stq i j, dt⟩⟩, n)) ∧
        ∃ b < 4, l.addr = L.sharedBase + 196608 + 2048 * Proof.ProA.qGroup i.val +
          Proof.ProA.qSwz (Proof.ProA.tidOf L g) + 4 * j.val + b := by
  obtain ⟨hsp, hqlo, hqhi⟩ := hl
  have hsr := hp.sharedRange
  unfold sharedBytes at hsr
  have hsa : c.loc.space = .shared := hc.1.symm.trans hsp
  rcases hI with ⟨bs, ⟨pc, he⟩, rfl⟩ | ⟨bs, ⟨pc, he⟩, rfl⟩ | ⟨old, new, pc, he⟩
  · exfalso
    obtain ⟨-, -, hca, hcb⟩ := hc
    cases rd_class hp hX he hsa with
    | base h hz => simp only [h, hz] at hca hcb; omega
    | role h4 _ h hz => simp only [h, hz] at hca hcb; omega
    | pair _ _ hz h => rcases h with h | h <;> omega
    | scratch h hz => simp only [h, hz] at hca hcb; omega
  · have hg := Frame.lt_of_get hX he
    obtain ⟨hcta, -, -⟩ := wr_placed hp hX he hsa hc
    obtain ⟨-, -, hca, hcb⟩ := hc
    obtain ⟨σ, t, ins, o, hσ, hJ, hat, hi, hc, hf⟩ := ev_state hp hX he (fun f h => by cases h)
    cases o with
    | none => exact absurd (fires_none_ends hf) (by simp [Ends])
    | some u =>
      have hev := frag_ev hp hg hJ hat hi hc hf
      have hpc := OpPcsFast.mem kernel_wr_pcs hc (fires_write_op hf rfl)
      obtain ⟨x, n⟩ := σ
      rcases x with st | ⟨_ | r, d⟩
      · exfalso
        rcases startup_wr st.site hpc with hs | hs
        · have h' : Startup.Ev L g st ⟨pc, .wr c bs⟩ := hev
          simp [Startup.Ev, hs] at h'
        · have h' : Startup.Ev L g st ⟨pc, .wr c bs⟩ := hev
          simp only [Startup.Ev, hs] at h'
          obtain ⟨col, -, h'⟩ := h'
          simp only [Event.mk.injEq, Kind.wr.injEq] at h'
          obtain ⟨-, rfl, -⟩ := h'
          simp only at hca hcb
          omega
      · rename_i ii
        cases ii with
        | dp tm bw =>
          rcases d with d | ⟨_ | _, τ⟩
          · have hx : d.site ≠ .exit := by
              rcases proA_wr d.site hpc with ⟨_, _, hs⟩ | hs | ⟨_, hs⟩ <;> rw [hs] <;> simp
            have hF := ProA.fired_old (P := Startup.inh L g Q tm) hx hat hi.1 hc hf
            have htid : g % L.block < 128 := hi.1.args.tid
            have hsb : Proof.ProA.SbRoom L := by unfold Proof.ProA.SbRoom; omega
            rcases proA_wr d.site hpc with ⟨i, jj, hs⟩ | hs | ⟨jj, hs⟩
            · obtain ⟨v, bs', a', -, he', hl', hz, h1, h2⟩ := Proof.ProA.shape_stq_foot
                (m := i.val) (w := jj.val) i.isLt jj.isLt htid hsb hF
                (by simp only [ProA.D.old, hs, stq_old])
              simp only [Event.mk.injEq, Kind.wr.injEq] at he'
              obtain ⟨-, rfl, rfl⟩ := he'
              rw [hl', Proof.ProA.qStoreBase_form L g _ htid hsb i.isLt] at hca
              rw [hl', Proof.ProA.qStoreBase_form L g _ htid hsb i.isLt, hz] at hcb
              obtain ⟨site, dt⟩ := d
              simp only at hs
              subst hs
              refine ⟨rfl, hg, htid, hcta, i, jj, tm, bw, dt, n, hσ, l.addr - (L.sharedBase +
                196608 + 2048 * Proof.ProA.qGroup i.val + Proof.ProA.qSwz (Proof.ProA.tidOf L g) +
                4 * jj.val), by simp only at hca hcb; omega, by simp only at hca hcb; omega⟩
            · exfalso
              obtain ⟨v, -, he'⟩ := Proof.ProA.shape_st8 hF
                (by simp [ProA.D.old, hs, ProA.Site.old])
              simp only [Event.mk.injEq, Kind.wr.injEq] at he'
              obtain ⟨-, rfl, rfl⟩ := he'
              simp only [Proof.EvD.wordAcc] at hca hcb
              rw [Nat.mod_eq_of_lt (by omega)] at hca
              omega
            · exfalso
              fin_cases jj
              · obtain ⟨v, -, he'⟩ := Proof.ProA.shape_st9_0 hF
                  (by simp [ProA.D.old, hs, ProA.Site.old])
                simp only [Event.mk.injEq, Kind.wr.injEq] at he'
                obtain ⟨-, rfl, rfl⟩ := he'
                simp only [Proof.EvD.wordAcc] at hca hcb
                rw [Nat.mod_eq_of_lt (by omega)] at hca
                omega
              · obtain ⟨v, -, he'⟩ := Proof.ProA.shape_st9_1 hF
                  (by simp [ProA.D.old, hs, ProA.Site.old])
                simp only [Event.mk.injEq, Kind.wr.injEq] at he'
                obtain ⟨-, rfl, rfl⟩ := he'
                simp only [Proof.EvD.wordAcc] at hca hcb
                rw [Nat.mod_eq_of_lt (by omega)] at hca
                omega
          · exfalso
            cases τ with
            | sm d =>
              have hs := sm_wr d.site hpc
              obtain ⟨bs', he'⟩ := Proof.Sm.shape_store10_foot (Proof.ProA.sharedOk_of_pre hp)
                (sm_fired hat hi hc hf) hs
              simp only [Event.mk.injEq, Kind.wr.injEq] at he'
              obtain ⟨-, rfl, rfl⟩ := he'
              simp only [Proof.EvD.wordAcc] at hca hcb
              omega
            | epi d =>
              have h' : Proof.Epi.Shape L g d ⟨pc, .wr c bs⟩ := hev
              unfold Proof.Epi.Shape at h'
              split at h'
              all_goals first
                | exact h'.elim
                | (simp only [Event.mk.injEq, reduceCtorEq, and_false, exists_false] at h'; done)
                | (obtain ⟨v, hv, h'⟩ := h'
                   simp only [Event.mk.injEq, Kind.wr.injEq] at h'
                   obtain ⟨-, rfl, rfl⟩ := h'
                   first
                     | (simp only [Proof.EvD.wordAcc] at hca hcb
                        rw [Nat.mod_eq_of_lt (by omega)] at hca
                        omega)
                     | (simp [Proof.EvD.wordAcc] at hsa))
          · exact hJ.elim
        | worker w =>
          exfalso
          cases d with
          | worker w => exact worker_wr w.site hpc
          | idle d => exact idle_wr d.site hpc
          | loader d P => exact loader_wr d.site hpc
          | mma d P => exact mma_wr d.site hpc
          | exit x => exact exitsite_wr x.site hpc
      · exact hJ.elim
  · exact absurd he (no_rmw hX)

/-- **A thread stays in its role.** -/
theorem role_const {k : Nat} {i : Role ⊕ Startup.Entry}
    {d : (Code.withStubs (frag Q L g) Startup.Entry.pc i).D} {n : Cls → Nat}
    (hσ : Frame.stateAt (thread Q L) X g k = some (some (.inr ⟨i, d⟩, n))) :
    ∀ j, k ≤ j → j ≤ (X.tr g).length → ∀ σ, Frame.stateAt (thread Q L) X g j = some (some σ) →
      ∃ d', σ.1 = .inr ⟨i, d'⟩ := by
  intro j
  induction j with
  | zero =>
    intro hk _ σ hσ'
    have : k = 0 := by omega
    subst this
    rw [hσ] at hσ'
    obtain rfl := Option.some.inj (Option.some.inj hσ')
    exact ⟨d, rfl⟩
  | succ j ih =>
    intro hk hj σ hσ'
    by_cases heq : k = j + 1
    · subst heq
      rw [hσ] at hσ'
      obtain rfl := Option.some.inj (Option.some.inj hσ')
      exact ⟨d, rfl⟩
    have hlt : j < (X.tr g).length := by omega
    obtain ⟨e, he⟩ : ∃ e, (X.tr g)[j]? = some e := ⟨_, List.getElem?_eq_getElem hlt⟩
    rw [Frame.stateAt_succ he] at hσ'
    rcases hj0 : Frame.stateAt (thread Q L) X g j with _ | _ | σj
    · rw [hj0] at hσ'; cases hσ'
    · rw [hj0] at hσ'; cases hσ'
    · rw [hj0] at hσ'
      obtain ⟨d', hd'⟩ := ih (by omega) hlt.le σj hj0
      obtain ⟨x, nj⟩ := σj
      simp only at hd'
      subst hd'
      exact next_same_role hσ'

/-- **No step of the prologue goes past its second proxy fence except the fence's own.** -/
theorem cross_fnc1 {d d' : ProA.D} {e : Event} (h : ProA.next L g d e = some (some d'))
    (hs : d.site.pc ≤ 569) (hd : 569 < d'.site.pc) : d.site = .fnc1 := by
  obtain ⟨s, dt⟩ := d
  simp only at hs ⊢
  by_cases hk : ProA.kill ⟨s, dt⟩ e = true
  · simp [ProA.next, hk] at h
  have h' : ProA.next0 L g ⟨s, dt⟩ e = some (some d') := by simpa [ProA.next, hk] using h
  by_cases h1 : s = .bar18
  · subst h1; exact absurd hs (by decide)
  by_cases h2 : s = .exit
  · subst h2; simp [ProA.next0] at h'
  by_cases h3 : s = .ld 2
  · subst h3
    rw [ld2_succ h'] at hd
    exact absurd hd (by decide)
  have hf := ProA.next0_flat h1 h2 h3 h'
  have hx' : d'.site ≠ .exit := fun hx => h1 (exit_from_bar18 h hx)
  have hf' : Proof.ProA.next L g ⟨s.old, dt⟩ e = some (some (ProA.D.old d')) := hf
  have hc := Proof.ProA.next_cross_fnc1 hf' (by rw [← ProA.pc_old s h2]; exact hs)
    (by show Proof.ProA.Site.fnc1.pc < d'.site.old.pc; rw [← ProA.pc_old _ hx']; exact hd)
  rw [← ProA.ofOld_old s h2, hc]
  rfl

/-- **Between a prologue state at or before the second proxy fence and a later one past it**, the
thread is at the fence. -/
theorem fnc1_between (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hg : g < L.threads) (tm : Nat) (bw : Value) {k0 : Nat} {d0 : ProA.D} {n0 : Cls → Nat}
    (h0 : Frame.stateAt (thread Q L) X g k0 = some (some (.inr ⟨.inl (.dp tm bw), .inl d0⟩, n0)))
    (hp0 : d0.site.pc ≤ 569) :
    ∀ k, k0 ≤ k → k < (X.tr g).length → ∀ d n,
      Frame.stateAt (thread Q L) X g k = some (some (.inr ⟨.inl (.dp tm bw), .inl d⟩, n)) →
      569 < d.site.pc → ∃ j, k0 ≤ j ∧ j < k ∧ ∃ d1 n1,
        Frame.stateAt (thread Q L) X g j = some (some (.inr ⟨.inl (.dp tm bw), .inl d1⟩, n1)) ∧
        d1.site = .fnc1 := by
  intro k
  induction k with
  | zero =>
    intro hk0 _ d n hσ hpc
    have : k0 = 0 := by omega
    subst this
    rw [hσ] at h0
    simp only [Option.some.injEq, Prod.mk.injEq, Sum.inr.injEq, heq_eq_eq, Sigma.mk.injEq,
      true_and, Sum.inl.injEq] at h0
    rw [← h0.1] at hp0
    omega
  | succ k ih =>
    intro hk0 hk d' n' hσ' hpc
    by_cases heq : k0 = k + 1
    · subst heq
      rw [hσ'] at h0
      simp only [Option.some.injEq, Prod.mk.injEq, Sum.inr.injEq, heq_eq_eq, Sigma.mk.injEq,
        true_and, Sum.inl.injEq] at h0
      rw [← h0.1] at hp0
      omega
    have hlt : k < (X.tr g).length := by omega
    obtain ⟨e, he⟩ : ∃ e, (X.tr g)[k]? = some e := ⟨_, List.getElem?_eq_getElem hlt⟩
    rw [Frame.stateAt_succ he] at hσ'
    have hF := good_all' hp hX hg k
    rcases hk0' : Frame.stateAt (thread Q L) X g k with _ | _ | σ
    · rw [hk0'] at hσ'; cases hσ'
    · exact absurd hk0' hF.1
    · rw [hk0'] at hσ'
      have hn : (thread Q L g).next σ e = some (some (.inr ⟨.inl (.dp tm bw), .inl d'⟩, n')) :=
        hσ'
      have hJ := hF.2 σ hk0'
      obtain ⟨x, n⟩ := σ
      rcases x with s | ⟨_ | r, dd⟩
      · exfalso
        rw [next_start] at hn
        obtain ⟨s', -, hs'⟩ := mm_some hn
        cases hx : Startup.enterOf s' with
        | none =>
          rw [enter_inl hx] at hs'
          simp at hs'
        | some r =>
          cases hsel : sel L g r s' with
          | none =>
            rw [Code.enter_some (i := Sum.inr r) (by simp [Code.gatedExit, hx, hsel])] at hs'
            simp at hs'
          | some ro =>
            rw [Code.enter_some (i := Sum.inl ro) (by simp [Code.gatedExit, hx, hsel])] at hs'
            cases ro with
            | worker w => simp at hs'
            | dp tm1 bw1 =>
              have h1 := congrArg (thread Q L g).pc hs'
              change 27 = d'.site.pc at h1
              omega
      · rename_i i
        obtain ⟨d2, hd2⟩ := next_same_role hn
        simp only [Sum.inr.injEq] at hd2
        cases i with
        | dp tm0 bw0 =>
          obtain ⟨h1, h2⟩ : tm0 = tm ∧ bw0 = bw := by
            have := (Sigma.mk.inj hd2).1
            simp only [Sum.inl.injEq, Role.dp.injEq] at this
            exact ⟨this.1.symm, this.2.symm⟩
          cases h1
          cases h2
          rcases dd with d | ⟨_ | _, τ⟩
          · rw [next_pro] at hn
            obtain ⟨d'', hd'', he''⟩ := mm_some hn
            have hx : ProA.exitOf d'' = none := by
              cases hxo : ProA.exitOf d'' with
              | none => rfl
              | some v =>
                exfalso
                cases hsel : ProA.selTail Q L g v d'' with
                | some dt' =>
                  rw [Code.enter_some (i := Sum.inl dt')
                    (by simp [Code.gatedExit, hxo, hsel])] at he''
                  simp at he''
                | none =>
                  rw [Code.enter_some (i := Sum.inr ())
                    (by simp [Code.gatedExit, hxo, hsel])] at he''
                  simp at he''
            rw [Code.enter_none (by simp [Code.gatedExit, hx])] at he''
            simp only [Prod.mk.injEq, Sum.inr.injEq, heq_eq_eq, Sigma.mk.injEq, true_and,
              Sum.inl.injEq] at he''
            obtain ⟨rfl, -⟩ := he''
            by_cases hle : d.site.pc ≤ 569
            · exact ⟨k, by omega, by omega, d, n, hk0', cross_fnc1 hd'' hle hpc⟩
            · obtain ⟨j, hj0, hj, d1, n1, h1, h8⟩ := ih (by omega) hlt d n hk0' (by omega)
              exact ⟨j, hj0, by omega, d1, n1, h1, h8⟩
          · exfalso
            rw [next_tail] at hn
            obtain ⟨τ', -, he''⟩ := mm_some hn
            simp at he''
          · exact hJ.elim
        | worker w =>
          exfalso
          have := (Sigma.mk.inj hd2).1
          simp at this
      · exact hJ.elim

/-- **A query store is followed by its thread's proxy fence `fnc1`**, before the thread's first
barrier-1 event, once a thread of the CTA has passed its first barrier-1 event. -/
theorem stq_fence (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hg : g < L.threads) {k : Nat} (hk : k < (X.tr g).length) {i : Fin 8} {jj : Fin 4} {tm : Nat}
    {bw : Value} {dt : Proof.ProA.Dat} {n : Cls → Nat}
    (hσ : Frame.stateAt (thread Q L) X g k =
      some (some (.inr ⟨.inl (.dp tm bw), .inl ⟨.stq i jj, dt⟩⟩, n)))
    {h f : Nat} (hcta : g / L.block = h / L.block) (hc : 1 ≤ c1 X h f)
    (hf : f < (X.tr h).length) :
    ∃ kf pcf, k < kf ∧ X.get (g, kf) =
        some ⟨pcf, .fenceProxy (.async (some (.shared .cta))) none⟩ ∧ c1 X g (kf + 1) = 0 := by
  have hbk : L.block = 256 := hp.block
  -- the first barrier-1 event of `h`
  obtain ⟨j0, hj0, ev, hget0, hb0, hc0⟩ := nth_of_count (X := X) (g := h) (q := 0) hc
  obtain ⟨pc0, k0⟩ := ev
  cases k0 with
  | bar id c md =>
    simp only [Execution.isBarId, beq_iff_eq] at hb0
    subst hb0
    obtain ⟨rfl, h1 | ⟨h1, -⟩⟩ := bar_event_static hX (by omega) hget0
    swap; · cases h1
    obtain ⟨rfl, -⟩ := h1
    have hb0 : X.IsBarrier (h, j0) 1 none pc0 := hget0
    have hpass : j0 + 1 < (X.tr h).length := by omega
    have hw1 : (g % L.block) / 32 ∈ Finset.range (CtaBarrier.warps L.block) := by
      have := Nat.mod_lt g (show 0 < L.block by omega)
      simp only [Finset.mem_range, CtaBarrier.warps, hbk]; omega
    obtain ⟨i0, pci, mi, hi0, hci⟩ := (bar1_sources hp hX).member_arrival_any hX (bar1_shape hp)
      hb0 hpass hcta hw1 (fun hex => by
        obtain ⟨i', pc', hIs, hord⟩ := bar1Exits hp hX hb0 hpass hcta hex
        exact ⟨i', pc', .sync, hIs, hord⟩)
    simp only at hci
    rw [hc0] at hci
    have hlen0 : i0 < (X.tr g).length := (List.getElem?_eq_some_iff.mp hi0).1
    have hi0' : (X.tr g)[i0]? = some ⟨pci, .bar 1 none mi⟩ := hi0
    have hk0 : k < i0 := by
      rcases Nat.lt_or_ge k i0 with h | h
      · exact h
      · exfalso
        rcases Nat.lt_or_eq_of_le h with h | h
        · have h1 : ((X.tr g).take (i0 + 1)).countP (Execution.isBarId 1) = 1 := by
            rw [List.take_add_one, hi0', Option.toList_some, List.countP_append, hci]
            simp [Execution.isBarId]
          have hC : _ = proPh ⟨.stq i jj, dt⟩ := c1_inv hp hX hg k hk _ hσ
          have h2 : ((X.tr g).take k).countP (Execution.isBarId 1) = 0 := by
            rw [hC]; simp [proPh]
          have := countP_take_mono (Execution.isBarId 1) (X.tr g) (show i0 + 1 ≤ k by omega)
          omega
        · subst h
          obtain ⟨σ', t', ins', o', hσ', -, hat', hi', hc', hf'⟩ := ev_state hp hX hi0
            (fun f h => by cases h)
          rw [hσ] at hσ'
          obtain rfl := Option.some.inj (Option.some.inj hσ')
          have hpc := bar1_pc hc' hf' rfl (by omega)
          exact absurd (proA_site_bar1 (.stq i jj) hpc) (by simp)
    -- the state at `i0` is the prologue's last barrier
    obtain ⟨σ, t, ins, o, hσ0, hJ, hat, hi, hcd, hfd⟩ := ev_state hp hX hi0
      (fun f h => by cases h)
    have hC := c1_inv hp hX hg i0 hlen0 σ hσ0
    have hpc := bar1_pc hcd hfd rfl (by omega)
    have hdef : g % L.block < 128 := by
      obtain ⟨ek, hek⟩ : ∃ e, X.get (g, k) = some e :=
        ⟨_, List.getElem?_eq_getElem (show k < (X.tr g).length by omega)⟩
      obtain ⟨σk, -, -, -, hσk, -, -, hik, -, -⟩ := ev_state hp hX hek
        (fun f h => not_ends_of_lt hX hg hek (by omega) (.inl ⟨f, h⟩))
      rw [hσ] at hσk
      obtain rfl := Option.some.inj (Option.some.inj hσk)
      exact hik.1.args.tid
    obtain ⟨x, n0⟩ := σ
    rcases x with st | ⟨_ | r, d⟩
    · exact (startup_bar1 st.site hpc).elim
    · rename_i ii
      cases ii with
      | dp tm' bw' =>
        rcases d with d | ⟨_ | _, τ⟩
        · have hs := proA_site_bar1 d.site hpc
          have hrole : tm' = tm ∧ bw' = bw := by
            obtain ⟨d', hd'⟩ := role_const hσ i0 (by omega) hlen0.le _ hσ0
            have := (Sigma.mk.inj (Sum.inr.inj hd')).1
            simp only [Sum.inl.injEq, Role.dp.injEq] at this
            exact this
          obtain ⟨rfl, rfl⟩ := hrole
          obtain ⟨j, hkj, hj, d1, n1, hσ1, hs1⟩ := fnc1_between hp hX hg tm' bw'
            (d0 := ⟨.stq i jj, dt⟩) hσ (by simp only [ProA.Site.pc]; omega) i0 (by omega) hlen0
            d n0 hσ0 (by rw [hs]; decide)
          have hkj' : k < j := by
            rcases Nat.lt_or_eq_of_le hkj with h | rfl
            · exact h
            · rw [hσ] at hσ1
              simp only [Option.some.injEq, Prod.mk.injEq, Sum.inr.injEq, heq_eq_eq,
                Sigma.mk.injEq, true_and, Sum.inl.injEq] at hσ1
              rw [← hσ1.1] at hs1
              simp at hs1
          obtain ⟨e1, he1⟩ : ∃ e1, X.get (g, j) = some e1 :=
            ⟨_, List.getElem?_eq_getElem (show j < (X.tr g).length by omega)⟩
          have hne : ¬ Ends e1 := not_ends_of_lt hX hg he1 (by omega)
          obtain ⟨σ1, t1, ins1, o1, hσ1', -, hat1, hi1, hc1, hf1⟩ := ev_state hp hX he1
            (fun f h => hne (.inl ⟨f, h⟩))
          rw [hσ1] at hσ1'
          obtain rfl := Option.some.inj (Option.some.inj hσ1')
          cases o1 with
          | none => exact absurd (fires_none_ends hf1) hne
          | some u =>
            have hx : d1.site ≠ .exit := by rw [hs1]; simp
            have hF := ProA.fired_old (P := Startup.inh L g Q tm') hx hat1 hi1.1 hc1 hf1
            have hev := Proof.ProA.shape_fnc hF (.inr (by simp [ProA.D.old, hs1, ProA.Site.old]))
            refine ⟨j, _, hkj', by rw [he1, hev], ?_⟩
            have := countP_take_mono (Execution.isBarId 1) (X.tr g) (show j + 1 ≤ i0 by omega)
            simp only [c1]
            omega
        · exfalso
          cases τ with
          | sm d =>
            have hC' : _ = smPh d := hC
            have : 1 ≤ smPh d := by unfold smPh; split <;> omega
            omega
          | epi d =>
            have hC' : _ = epiPh d := hC
            have : 2 ≤ epiPh d := by unfold epiPh; split <;> omega
            omega
        · exact hJ.elim
      | worker w =>
        exfalso
        have : 4 ≤ g % L.block / 32 := (tm_inv hp hX hg i0 hlen0 _ hσ0).2
        omega
    · exact hJ.elim
  | _ => simp [Execution.isBarId] at hb0

/-- **A query store is before the issue of every MMA of its CTA** for every shared byte of the
CTA, through its thread's fence `fnc1` and barrier 1 (`ProxyBefore`). -/
theorem stq_proxy (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hg : g < L.threads) {k : Nat} (hk : k < (X.tr g).length) {i : Fin 8} {jj : Fin 4} {tm : Nat}
    {bw : Value} {dt : Proof.ProA.Dat} {n : Cls → Nat}
    (hσ : Frame.stateAt (thread Q L) X g k =
      some (some (.inr ⟨.inl (.dp tm bw), .inl ⟨.stq i jj, dt⟩⟩, n)))
    {h f : Nat} (hh : h < L.threads) (hcta : g / L.block = h / L.block) (hc : 1 ≤ c1 X h f)
    (hf : f < (X.tr h).length) {l : Loc} (hls : l.space = .shared) (hlc : l.cta = g / L.block) :
    ProxyBefore L X (g, k) (h, f) l := by
  have hb : L.block = 256 := hp.block
  obtain ⟨kf, pcf, hkf, hget, hc0⟩ := stq_fence hp hX hg hk hσ hcta hc hf
  have hkfl : kf < (X.tr g).length := (List.getElem?_eq_some_iff.mp hget).1
  refine ⟨(g, kf), _, _, ⟨pcf, hget⟩, hg, ⟨hls, hlc⟩, ⟨hg, hh, by simp only; rw [hcta]⟩, ?_, ?_⟩
  · exact .single (.inl (po_of_not_access rfl hkf hkfl (by rw [hget]; rfl)))
  · refine bar1_handoff hp hX g h kf f ⟨⟨hg, hh, hcta⟩, ?_, trivial⟩ hf ?_
    · have := Nat.mod_lt g (show 0 < L.block by omega)
      simp only [Finset.mem_range, CtaBarrier.warps, hb]
      omega
    · simp only [c1] at hc0 hc
      simp only [hc0]
      omega

/-- An MMA warp state has made a barrier-1 event. -/
theorem mma_c1 (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hg : g < L.threads) {k : Nat} (hk : k < (X.tr g).length) {tm : Value} {d : Proof.Mma.D}
    {P : Proof.Loader.Pro} {n : Cls → Nat}
    (hσ : Frame.stateAt (thread Q L) X g k =
      some (some (.inr ⟨.inl (.worker tm), .mma d P⟩, n))) : 1 ≤ c1 X g k := by
  have := role_count hp hX hg hk rfl hσ
  simp only [c1, this]
  split <;> omega

/-- **The conflicting accesses of the Q tile are ordered.** -/
theorem q_ordered (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X) :
    ConflictsOrdered L X (InQ L) := by
  intro e f a b l hc ha hb hl
  obtain ⟨hne, we, wf, hie, hif, hw, hov⟩ := hc
  have hls : l.space = .shared := hl.1
  -- a store and an MMA read: the store first
  have mixed : ∀ {g k : Nat} {j : EvId} {p : AsyncCopy.Part} {a b : Acc} {we wf : Bool},
      X.Intent (.thread (g, k)) a we → X.Intent (.async j p) b wf → a.Covers l →
      b.Covers l → modelCausality L X l (.thread (g, k)) (.async j p) := by
    intro g k j p a b we wf hie hif ha hb
    obtain ⟨-, hg, -, hcta, i, jj, tm, bw, dt, n, hσ, -⟩ := q_thread hp hX hie ha hl
    have hk : k < (X.tr g).length := Execution.Access.lt hie
    obtain ⟨hjt, hjc, -, hcl⟩ := async_shared hp hX hif hb hls
    rcases hcl with ⟨isB, idx, rfl, -, hjl, ⟨tm', d, P, n', hσm⟩, -, -⟩ | ⟨x, y, z, -, -, h⟩
    · exact ⟨⟨b, wf, hif, hb⟩, .inl (stq_proxy hp hX hg hk hσ hjt (hcta.symm.trans hjc)
        (mma_c1 hp hX hjt hjl hσm) hjl hls hcta)⟩
    · exact absurd hl.2.1 (by omega)
  rcases e with ⟨g, k⟩ | ⟨i, p⟩ <;> rcases f with ⟨g', k'⟩ | ⟨j, p'⟩
  · -- two stores: one thread, program order
    obtain ⟨-, hg, hdef, hcta, i, jj, -, -, -, -, -, c, hc4, hadd⟩ := q_thread hp hX hie ha hl
    obtain ⟨-, hg', hdef', hcta', i', jj', -, -, -, -, -, c', hc4', hadd'⟩ :=
      q_thread hp hX hif hb hl
    obtain ⟨ht, -, -⟩ := Proof.Lp.qOff_inj (m := i.val) (m' := i'.val)
      (t := Proof.ProA.tidOf L g) (t' := Proof.ProA.tidOf L g') (w := jj.val) (w' := jj'.val)
      (b := c) (b' := c') i.isLt i'.isLt hdef hdef' jj.isLt jj'.isLt hc4 hc4' (by omega)
    have hgg : g = g' := by
      have h1 := Nat.div_add_mod g L.block
      have h2 := Nat.div_add_mod g' L.block
      have h3 : g / L.block = g' / L.block := hcta.symm.trans hcta'
      have h4 : g % L.block = g' % L.block := ht
      rw [← h1, ← h2, h3, h4]
    subst hgg
    exact same_thread hie hif (fun h => hne (by rw [h])) hov
  · exact .inl (mixed hie hif ha hb)
  · exact .inr (mixed hif hie hb ha)
  · -- two MMA reads: no write
    exfalso
    obtain ⟨-, -, -, h1⟩ := async_shared hp hX hie ha hls
    obtain ⟨-, -, -, h2⟩ := async_shared hp hX hif hb hls
    rcases h1 with ⟨-, -, -, rfl, -⟩ | ⟨-, -, -, -, -, h⟩
    · rcases h2 with ⟨-, -, -, rfl, -⟩ | ⟨-, -, -, -, -, h⟩
      · rcases hw with h | h <;> cases h
      · exact absurd hl.2.1 (by omega)
    · exact absurd hl.2.1 (by omega)

end
end PTX.Kernels.InklingRelDecode.Proof2
