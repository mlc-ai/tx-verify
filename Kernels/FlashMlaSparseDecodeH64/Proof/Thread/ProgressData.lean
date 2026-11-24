-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.ProgressNext
import Lemmas.Flow.StoreValue
import Lemmas.Step.Issue
import Lemmas.Step.ReadSource

public section

/-! # Counted extensions of the dequantization path -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress
open PTX PTX.Flow PTX.Proof

noncomputable section

/-- A released read can take a consistent reference for each of its bytes. -/
theorem shared_read_extension {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}
    {t u : TState} {a : Acc} {k : List (Option Byte) → TState}
    (hX : Consistent L kernel Assumptions.all mem0 X) (hg : g < L.threads)
    (hne : X.tr g ≠ []) (hrel : PTX.Step.Released L X g)
    (hrun : Run kernel Assumptions.all L g {} (X.tr g) (some t))
    (hτ : Relation.ReflTransGen (Tau kernel Assumptions.all L g) t u)
    (hout : out kernel Assumptions.all L g u = .ev (.read a k))
    (hguarded : SyncGuarded L kernel X) :
    ∃ Y, Consistent L kernel Assumptions.all mem0 Y ∧ X.le Y ∧ X.size L < Y.size L :=
  PTX.Step.read_source_counted_extension hX hg hne hrel hrun hτ hout
    (fun _ _ _ => Interface.all_wf_snoc_of_not_nc hX (by simp) (by simp)) hguarded

private theorem tile_template {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {d : Wg2.D}
    {r : Fin 4} {s : Fin 8} {t : TState}
    (hpre : Pre P L mem0) (hd : d.site = .store r s) (hat : Wg2.AtD P L g d t)
    (hinv : Wg2.Inv P L g d) :
    ∃ a u, a.release = false ∧
      eventTmpl Assumptions.all L g t (.mem (Wg2.tileStore r s)) =
        .write a (Wg2.Numeric.dequantChunk d.raw
          (Wg2.Numeric.byteAt d.sc (Wg2.scaleIdx L g s.val))).toBytes u := by
  have hp : Holds t.regs (Wg2.storePayload L g r s d) := by
    simpa [Wg2.payloadFacts, hd] using hat.payloadRegs
  have hra : t.regs (Wg2.storeBaseReg r s) = some (b32
      (L.sharedBase + Wg2.tileBase d.buf + Wg2.tileOff L g r.val s.val)) := by
    simpa [sb, Nat.add_assoc] using hp.2.1
  have hsub : t.sub = 0 := by rw [hat.2.1, hd]; rfl
  set base := L.sharedBase + Wg2.tileBase d.buf + Wg2.tileOff L g r.val s.val
  have hal := Wg2.sharedTile_align hpre g d.buf r s
  have hfit := Wg2.sharedTile_lt hpre hinv r s
  rw [eventTmpl, memTmpl_store (sp := .shared) (base := Wg2.storeBaseReg r s)
    (w := 32) rfl rfl rfl rfl (by simp [Wg2.tileStore])]
  simp only [Wg2.tileStore, DType.width, storeTmpl, effAddr_b32 hra hfit,
    bind, Except.bind, hsub]
  rw [elemAcc_ok (by decide) (by simpa using hal)]
  simp only [pure, Except.pure, List.getElem?_singleton, readValue, readReg, ite_true, hp.1]
  let scale := Wg2.Numeric.byteAt d.sc (Wg2.scaleIdx L g s.val)
  rw [storeValue_of_bytes (w := 128) (v := Wg2.Numeric.dequantChunk d.raw scale) (by
    have := Wg2.Numeric.dequantChunk_width d.raw scale
    omega)]
  exact ⟨_, _, rfl, rfl⟩

private theorem alloc_cannot_enter_store {P : Params} {L : Launch} {g pc n : Nat}
    {grp : CtaGroup} {dst : Option Loc} {d before : Machine.ThreadD} {r : Fin 4} {s : Fin 8}
    (d' : Wg2.D) (hd : d'.site = .store r s)
    (hn : Machine.next P L g before ⟨pc, .tc (.resource grp dst (.alloc n))⟩ =
      some (some d)) (he : d = .wg2 d') : False := by
  subst d
  cases before with
  | prologue p =>
    simp only [Machine.next] at hn
    split at hn
    · cases hn
    · rename_i hnext
      split at hn
      · split at hn
        · have hstart : ∀ w : Fin 3, Machine.roleStart P L g w ≠ .wg2 d' := by
            intro w hw
            fin_cases w <;> cases hw
            simp [Wg2.init, Wg2.firstSite] at hd
            split at hd
            · cases hd
            · split at hd <;> cases hd
          exact hstart _ (Option.some.inj (Option.some.inj hn))
        · cases hn
      · cases hn
    · cases hn
  | wg2 d =>
    simp only [Machine.next, Wg2.next] at hn
    cases h : d.site <;> simp [h, Wg2.nextSite] at hn
  | head | done => simp [Machine.next] at hn
  | wg0 d | mma d | tma d | index d | idle d =>
    simp only [Machine.next] at hn
    repeat' (first | cases hn | split at hn)

private theorem before_store_ne_alloc {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    {g : Nat} {d : Wg2.D} {r : Fin 4} {s : Fin 8} (hs : SoundThreads P L)
    (hX : Consistent L kernel Assumptions.all mem0 X) (hub : ¬ HasUb X)
    (ht : Frame.Tracked (Machine.code P L) X)
    (hσ : Frame.stateAt (Machine.code P L) X g (X.tr g).length = some (some (.wg2 d)))
    (hd : d.site = .store r s) :
    ∀ pc grp dst n, X.get (g, (X.tr g).length - 1) =
      some ⟨pc, .tc (.resource grp dst (.alloc n))⟩ → False := by
  intro pc grp dst n he
  obtain ⟨before, hb⟩ := Frame.state_of_noUb hs hX ht hub he
  have hl : (X.tr g).length - 1 < (X.tr g).length := len_of_get he
  have hlast : (X.tr g).length - 1 + 1 = (X.tr g).length := by omega
  have hstep := Frame.stateAt_succ (C := Machine.code P L) (e := _) he
  rw [hlast, hσ, hb] at hstep
  exact alloc_cannot_enter_store d hd hstep.symm rfl

/-- A released pending dequantizer can publish the packed chunk at its tile store site. -/
theorem dequant_store_extension {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    {g : Nat} {d : Wg2.D} {r : Fin 4} {s : Fin 8} (hpre : Pre P L mem0)
    (hs : SoundThreads P L) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hub : ¬ HasUb X) (ht : Frame.Tracked (Machine.code P L) X)
    (hp : Frame.Pending L X g) (hrel : PTX.Step.Released L X g)
    (hσ : Frame.stateAt (Machine.code P L) X g (X.tr g).length = some (some (.wg2 d)))
    (hd : d.site = .store r s) :
    ∃ Y, Consistent L kernel Assumptions.all mem0 Y ∧ X.le Y ∧ X.size L < Y.size L := by
  have hne : X.tr g ≠ [] := by
    intro he
    rw [he, List.length_nil, Frame.stateAt_zero] at hσ
    cases hσ
  obtain ⟨t, hr⟩ := Frame.run_some hX hub hp
  obtain ⟨u, ins, hτ, ha, hi, hc, hout⟩ := Frame.end_at hs hp.1 hr hσ
  change kernel.code[d.site.pc]? = some ins at hc
  have hstore := Wg2.tileStore_code r s
  rw [← hd] at hstore
  obtain rfl := Option.some.inj (hc.symm.trans hstore)
  obtain ⟨a, v, hweak, htmpl⟩ := tile_template hpre hd ha hi
  rw [htmpl] at hout
  let scale := Wg2.Numeric.byteAt d.sc (Wg2.scaleIdx L g s.val)
  let bs := (Wg2.Numeric.dequantChunk d.raw scale).toBytes
  exact PTX.Step.plain_counted_extension hX hp.1 (.inl hne) hrel hr hτ
    (e := ⟨u.pc, .wr a bs⟩) (o := some v) ⟨_, hout, rfl, rfl⟩
    (by simp [Kind.Plain, hweak]) (by simp [Kind.isTma, hweak])
    (by simp) (by simp) (by simp) rfl
    (hX.tmemPairResult.snoc_last
      (fun pc grp dst n he => (before_store_ne_alloc hs hX hub ht hσ hd pc grp dst n he).elim))
    (Interface.all_wf_snoc_of_not_nc hX (by simp) (by simp))

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress
