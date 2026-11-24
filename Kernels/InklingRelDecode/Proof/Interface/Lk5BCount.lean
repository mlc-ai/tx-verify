-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.Lk5Defs
public import Kernels.InklingRelDecode.Proof.Interface.Lk2Pro
public import Kernels.InklingRelDecode.Proof.Interface.ClassCopyPage
public import Kernels.InklingRelDecode.Proof.Interface.RdSmProg
public import Kernels.InklingRelDecode.Proof.Thread.Lk5BR

@[expose] public section

/-!
# The barrier-0 events of a default-partition thread, counted along its trace

`count_inv`: before every state of a default-partition thread, the number of its barrier-0
events is the state's count without a count (`Ledger.dN0`: the common start's two, the
epilogue's last), plus its count of `bar.sync 0, 128` other than `bar24` (`Lk5B.p128`, with the
prologue's count `1 + 5 nbQ` and the loop's `Lfun num_iters`), plus the number of its earlier
`bar24` states (`nB24`).

* `b0_event`: an event is on barrier 0 exactly when its state's instruction is (`b0At ≠ 0`);
* `nbQ`: the number of blocks the prologue preloads, a function of the CTA (`nbQ_cta`), which is
  the guards' number at every prologue state after the loads (`nbOf_pro`).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Interface.B0N
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof.Ledger
open PTX.Kernels.InklingRelDecode.Proof.Lk5B
open Classical

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-! ### The barrier-0 events -/

theorem b0At_le (pc : Nat) : b0At pc ≤ 2 := by
  unfold b0At
  split
  · split <;> omega
  · omega

/-- **An event is on barrier 0 exactly when its state's instruction is.** -/
theorem b0_event (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hS : ∀ g < L.threads, (threadCode L g Q).Sound) {g k : Nat} {s : TSt} {e : Event}
    (he : X.get (g, k) = some e) (hσ : St Q L X g k = some (some s)) :
    Execution.isBarId 0 e = true ↔ b0At (TSt.pc s) ≠ 0 := by
  obtain ⟨t, ins, o, -, -, hc, hf⟩ := Frame.fired_site hS hX he hσ
  have hc' : kernel.code[TSt.pc s]? = some ins := hc
  have hf' : Fires (TSt.pc s) (eventTmpl asms L g t ins.op) e o := hf
  have hb : L.block ≠ 128 := by have := hpre.block; omega
  have hmem := List.mem_of_getElem? hc'
  constructor
  · intro h
    obtain ⟨pc, kd⟩ := e
    cases kd <;> simp only [Execution.isBarId, Bool.false_eq_true] at h
    rename_i id c m
    have hid : id = 0 := by simpa using h
    subst hid
    rcases bar_kind_op hb hmem hf' rfl with ⟨al, hop⟩ | ⟨-, al, hop⟩ <;>
      simp [b0At, hc', hop]
  · intro h
    simp only [b0At, hc'] at h
    split at h
    · rename_i al hop
      rw [hop] at hf'
      rw [EvD.fires_barSync_imm (id := 0) (by decide) hf']
      simp [Execution.isBarId]
    · rename_i al hop
      rw [hop] at hf'
      rw [EvD.fires_barSyncN_128 hb hf']
      simp [Execution.isBarId]
    · exact absurd rfl h

/-! ### The prologue's number of blocks -/

/-- The prologue's data with the request words of the thread's request. -/
def dtQ (Q : Params) (L : Launch) (g : Nat) : ProA.Dat :=
  { ProA.Dat.start (DStart.inh L g Q 0) with
    cu0 := Q.qStart (ProA.cta L g .z), cu1 := Q.qStart (ProA.cta L g .z + 1),
    sk := Q.seqK (ProA.cta L g .z) }

/-- **The number of blocks the prologue of the thread's CTA preloads.** -/
def nbQ (Q : Params) (L : Launch) (g : Nat) : Nat := nbOf L g (dtQ Q L g)

theorem nbOf_congr {g h : Nat} {dt dt' : ProA.Dat}
    (h31 : ProA.v_r31 L g dt = ProA.v_r31 L h dt') : nbOf L g dt = nbOf L h dt' := by
  obtain ⟨a1, a2, a3⟩ := Lk.guards_of_r31 h31
  simp only [nbOf, a1, a2, a3]

/-- **One number of blocks in a CTA.** -/
theorem nbQ_cta {g h : Nat} (hc : g / L.block = h / L.block) : nbQ Q L g = nbQ Q L h := by
  have hx : ProA.cta L g .x = ProA.cta L h .x := ProA.cta_eq_of_block hc .x
  have hz : ProA.cta L g .z = ProA.cta L h .z := ProA.cta_eq_of_block hc .z
  refine nbOf_congr (Lk.r31_congr hx rfl ?_ ?_ ?_) <;> simp [dtQ, hz]

/-- **The guards' number of blocks at a prologue state after the loads is the CTA's.** -/
theorem nbOf_pro (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) {g k : Nat} {d : ProA.D} (hg : g < L.threads)
    (hσ : St Q L X g k = some (some (.d (.pro d)))) (hs : d.site.afterSk = true) :
    nbOf L g d.dt = nbQ Q L g := by
  obtain ⟨-, tm, -, hpro⟩ := hf.reach hg hσ
  obtain ⟨w0, w1, w2⟩ := Mbar.wordsSo_all hpre hX hf k _ hσ
  have hne : d.site ≠ .sMax ∧ d.site ≠ .ldCu0 := by
    constructor <;> (intro h'; rw [h'] at hs; simp [ProA.Site.afterSk] at hs)
  refine nbOf_congr (Lk.r31_congr rfl ?_ ?_ ?_ ?_)
  · rw [hpro]; rfl
  · rw [w2 hs]; rfl
  · rw [w0 hne.1 hne.2]; rfl
  · rw [w1 (Or.inl hs)]; rfl

/-! ### The count along the trace -/

/-- The thread's state before event `j` is the softmax region's `bar24`. -/
def IsB24 (Q : Params) (L : Launch) (X : Execution) (g j : Nat) : Prop :=
  ∃ d : Sm.D, St Q L X g j = some (some (.d (.sm d))) ∧ d.site = .bar24

/-- The number of `bar24` states before event `k`. -/
def nB24 (Q : Params) (L : Launch) (X : Execution) (g k : Nat) : Nat :=
  ((Finset.range k).filter (fun j => IsB24 Q L X g j)).card

theorem nB24_succ (g k : Nat) :
    nB24 Q L X g (k + 1) = nB24 Q L X g k + if IsB24 Q L X g k then 1 else 0 := by
  unfold nB24
  rw [Finset.range_add_one, Finset.filter_insert]
  by_cases h : IsB24 Q L X g k
  · simp only [h, ↓reduceIte]
    rw [Finset.card_insert_of_notMem]
    simp
  · simp [h]

/-- The number of barrier-0 events before event `k`. -/
def cnt0 (X : Execution) (g k : Nat) : Nat := ((X.tr g).take k).countP (Execution.isBarId 0)

/-- The prologue's count of `bar.sync 0, 128` of the thread's CTA. -/
def C0 (Q : Params) (L : Launch) (g : Nat) : Int := 1 + 5 * (nbQ Q L g : Int)

/-- The loop's count of `bar.sync 0, 128` other than `bar24` of the thread's CTA. -/
def Lc (Q : Params) (L : Launch) (g : Nat) : Int :=
  Lfun (Q.numIters (ProA.cta L g .z) (ProA.cta L g .x))

/-- The count of a state. -/
def cntOf (Q : Params) (L : Launch) (g : Nat) (s : DComp.St) : Int :=
  (dN0 s : Int) + p128 L g (C0 Q L g) (Lc Q L g) s

theorem r26_numIters (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) {g k : Nat} {d : Sm.D} {e : Event} (hg : g < L.threads)
    (he : X.get (g, k) = some e) (hσ : St Q L X g k = some (some (.d (.sm d)))) :
    d.e.r26 = Q.numIters (ProA.cta L g .z) (ProA.cta L g .x) := by
  obtain ⟨-, hm⟩ := hf.reach hg hσ
  have hI := Sv.sm_inv_at hX hf he hσ
  have h25 := hm.ent.r25
  have hlt := numIters_lt31 hpre (ProA.cta_lt hpre hg).2.2 (ProA.cta L g .x)
  rw [hI.ok.r26, h25]
  simp only [hlt, ↓reduceIte]

/-- **The barrier-0 events of a default-partition thread before each of its states.** -/
theorem count_inv (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) {g : Nat} (hg : g < L.threads) (hd : g % L.block < 128) :
    ∀ k, k ≤ (X.tr g).length → ∀ s : DComp.St, St Q L X g k = some (some (.d s)) →
      (cnt0 X g k : Int) = cntOf Q L g s + nB24 Q L X g k := by
  intro k
  induction k with
  | zero =>
    intro _ s hs
    have hs' : Frame.stateAt (code L Q) X g 0 = some (some (.d s)) := hs
    rw [Frame.stateAt_zero] at hs'
    have h1 := Option.some.inj (Option.some.inj hs')
    change (if g % L.block < 128 then TSt.d (DComp.code L g Q).init
      else TSt.w (WComp.code L g Q).init) = TSt.d s at h1
    simp only [hd, ↓reduceIte] at h1
    cases h1
    simp only [cnt0, List.take_zero, List.countP_nil, Nat.cast_zero, cntOf, nB24,
      Finset.range_zero, Finset.filter_empty, Finset.card_empty]
    show (0 : Int) = (dN0 (.dstart (DStart.D.start L g)) : Int) + 0 + 0
    simp only [DStart.D.start]
    split_ifs <;> rfl
  | succ k ih =>
    intro hk s' hs'
    obtain ⟨e, he⟩ : ∃ e, (X.tr g)[k]? = some e := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    have hge : X.get (g, k) = some e := he
    obtain ⟨σ, hσ⟩ : ∃ σ, St Q L X g k = some (some σ) :=
      Frame.stateAt_live (C := code L Q) hf.tracked hg hs' (show k ≤ k + 1 by omega)
    have hn := Lk.next_of_st_succ he hσ hs'
    obtain ⟨s, rfl⟩ : ∃ s, σ = .d s := by
      cases σ with
      | d s => exact ⟨s, rfl⟩
      | w s =>
        exfalso
        obtain ⟨a, -, ha⟩ := Ledger.mapInv (show (WComp.next L g s e).map
          (Option.map TSt.w) = some (some (.d s')) from hn)
        cases ha
    obtain ⟨a, ha, hsa⟩ := Lk.next_d_inv hn
    cases hsa
    have h0 := ih (by omega) s hσ
    -- the increments
    have hN := d_next_n0 ha
    have hP := p128_next (C := C0 Q L g) (Lc := Lc Q L g) ha
      (fun d hd => by subst hd; exact (pgSo_all hpre hX hf (g := g) k _ hσ).1)
      (fun d hd hb => by
        subst hd
        have hs : d.site.afterSk = true := by rw [hb]; decide
        have hnb := nbOf_pro hpre hX hf hg hσ hs
        obtain ⟨st, dt⟩ := d
        simp only at hb
        subst hb
        have hlt : ¬ ProA.Site.bar18.ctorIdx ≤ ProA.Site.bar2.ctorIdx := by decide
        simp only [proOff, blkOff, hlt, ↓reduceIte, C0]
        simp only at hnb
        rw [hnb]
        push_cast
        ring)
      (fun d hd => by
        subst hd
        rw [Lc, r26_numIters hpre hX hf hg hge hσ])
    have hB := b0_event hpre hX hf.sound hge hσ
    have hc : cnt0 X g (k + 1) = cnt0 X g k + if Execution.isBarId 0 e = true then 1 else 0 := by
      unfold cnt0
      rw [List.take_add_one, he]
      simp [List.countP_append]
    have hb24 : IsB24 Q L X g k ↔ isB24 s = true := by
      constructor
      · rintro ⟨d, hd, hs⟩
        rw [hσ] at hd
        cases hd
        simp [isB24, hs]
      · intro h
        cases s with
        | sm d => exact ⟨d, hσ, by simpa [isB24] using h⟩
        | _ => simp [isB24] at h
    have hb1 := d_b0 s
    have hle := b0At_le (DComp.pc s)
    have h24 : isB24 s = true → b0At (DComp.pc s) = 2 := by
      intro h
      cases s with
      | sm d =>
        simp only [isB24, decide_eq_true_eq] at h
        simp only [DComp.pc, sm_b0At, h]
        rfl
      | _ => simp [isB24] at h
    rw [hc, nB24_succ]
    unfold cntOf at h0 ⊢
    rw [hN, hP]
    push_cast
    rw [h0]
    simp only [inc128, bInc]
    have hpc : TSt.pc (.d s) = DComp.pc s := rfl
    rw [hpc] at hB
    by_cases h1 : b0At (DComp.pc s) = 0
    · have : ¬ Execution.isBarId 0 e = true := fun h => hB.mp h h1
      have h2 : dB0 s = false := by
        cases hh : dB0 s
        · rfl
        · rw [← hb1] at hh; omega
      have h3 : ¬ IsB24 Q L X g k := fun h => by have := h24 (hb24.mp h); omega
      simp [this, h2, h1, h3]
    · have : Execution.isBarId 0 e = true := hB.mpr h1
      by_cases h2 : b0At (DComp.pc s) = 1
      · have h3 : dB0 s = true := hb1.mp h2
        have h4 : ¬ IsB24 Q L X g k := fun h => by have := h24 (hb24.mp h); omega
        simp [this, h2, h3, h4]
        ring
      · have h2' : b0At (DComp.pc s) = 2 := by omega
        have h3 : dB0 s = false := by
          cases hh : dB0 s
          · rfl
          · rw [← hb1] at hh; omega
        by_cases h4 : isB24 s = true
        · have h5 : IsB24 Q L X g k := hb24.mpr h4
          simp [this, h2', h3, h4, h5]
          ring
        · have h5 : ¬ IsB24 Q L X g k := fun h => h4 (hb24.mp h)
          simp [this, h2', h3, h4, h5]
          ring

end
end PTX.Kernels.InklingRelDecode.Proof.Interface.B0N
