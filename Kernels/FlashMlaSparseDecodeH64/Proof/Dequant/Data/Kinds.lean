-- SPDX-License-Identifier: Apache-2.0
-- domain: valid-rows
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.Data.Machine
public import Lemmas.Flow.DataLoad

@[expose] public section

/-! # The data steps of warpgroup 2, by kind

A data step (`Code.DataStep`) of the data machine, per kind of site, from the local code after
its event stated as `Code.Reach` (from the facts after the event, the first state that performs an
event holds the successor's data facts, or the thread is dead). The per-site `Reach` facts are
generated (`Dequant/Gen/DataSites*.lean`).

* `ds_quiet`: every successor has no data facts (the set-up, the polls, the arrivals, the
  elements of a scale load before its last, the last store of a row);
* `ds_scale`: the last element of a row's scale load; the scale run states the sixteen scale
  halfwords (`scaleFacts`) of the four words;
* `ds_raw0`, `ds_raw`: raw load `s` of a row (`s = 0`: the halfword run; `s ≥ 1`: the chunk
  run of step `s - 1`);
* `ds_store`, `ds_store6`: a store of a row before the last but one (the next word's halfword
  run), the last but one (the last word's halfword and chunk runs). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.Data
open PTX PTX.Proof PTX.Flow PTX.Flow.Code PTX.Kernels.FlashMlaSparseDecodeH64
open PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Numeric.Dequant

noncomputable section

variable {P : Params} {L : Launch} {g : Nat} {w : BitVec 64}

/-- A followed step is a control step and a data step. -/
theorem next_ctl {d d' : D} {e : Event} (h : (code P L g w).next d e = some (some d')) :
    ∃ c', Control.succ P L g d.c e = some (some c') ∧ dataNext d c' e = some d' := by
  change succ P L g d e = _ at h
  unfold succ at h
  split at h
  · cases h
  · cases h
  · rename_i c' hc; exact ⟨c', hc, Option.some.inj h⟩

/-- A site without data facts. -/
def Quiet : Site → Prop
  | .raw _ _ => False
  | .store _ _ => False
  | _ => True

theorem dF_quiet {d : D} (h : Quiet d.c.site) : dF L g d = [] := by
  unfold dF
  split <;> simp_all [Quiet]

/-- **Quiet successors**: no data step. -/
theorem ds_quiet {d : D} (h : ∀ e c', Control.succ P L g d.c e = some (some c') → Quiet c'.site) :
    DataStep (code P L g w) (dF L g) d :=
  DataStep.nil fun e d' hn => by
    obtain ⟨c', hc, hd⟩ := next_ctl hn
    exact dF_quiet (dataNext_c hd ▸ h e c' hc)

/-- The words of four elements. -/
def words (l : List Nat) : List Value := l.map fun x => .bits 32 (BitVec.ofNat 64 x)

theorem wordOf_some {n x : Nat} {v : Value} (h : wordOf n v = some x) :
    x < 2 ^ n ∧ v = .bits n (BitVec.ofNat 64 x) := by
  unfold wordOf at h
  split at h
  · split at h
    · rename_i m y _ hc
      obtain ⟨rfl, hb⟩ := hc
      cases h
      exact ⟨hb, by simp⟩
    · cases h
  · cases h

theorem scaleOf_some {l : List Value} {sc : {sc // ScOk sc}} (h : scaleOf l = some sc) :
    ∃ w0 w1 w2 w3, w0 < 2 ^ 32 ∧ w1 < 2 ^ 32 ∧ w2 < 2 ^ 32 ∧ w3 < 2 ^ 32 ∧
      l = words [w0, w1, w2, w3] ∧ sc.1 = scWord w0 w1 w2 w3 := by
  unfold scaleOf at h
  split at h
  · split at h
    · rename_i h0 h1 h2 h3
      split at h
      · cases h
        obtain ⟨b0, rfl⟩ := wordOf_some h0
        obtain ⟨b1, rfl⟩ := wordOf_some h1
        obtain ⟨b2, rfl⟩ := wordOf_some h2
        obtain ⟨b3, rfl⟩ := wordOf_some h3
        exact ⟨_, _, _, _, b0, b1, b2, b3, rfl, rfl⟩
      · cases h
    · cases h
  · cases h

theorem rawOf_some {v : Value} {x : {x // WordOk x}} (h : rawOf v = some x) :
    x.1 < 2 ^ 64 ∧ v = .bits 64 (BitVec.ofNat 64 x.1) := by
  unfold rawOf at h
  split at h
  · rename_i y hy
    split at h
    · cases h; exact wordOf_some hy
    · cases h
  · cases h

/-- A load's value that is a word is the bytes' rebuilt value. -/
theorem loadVal_ok {bs : List (Option Byte)} {n : Nat} {x : BitVec 64}
    (h : loadVal bs = .bits n x) : rebuild 3 bs = .ok (loadVal bs) := by
  unfold loadVal at h ⊢
  cases hr : rebuild 3 bs with
  | ok v => rfl
  | error f => rw [hr] at h; cases h

theorem pc_eq {d : D} {s : Site} (hs : d.c.site = s) : (code P L g w).pc d = s.pc := by
  show d.c.site.pc = _; rw [hs]

/-- The state after a one-register load or a store, with the start state's facts. -/
theorem at_after {t : TState} {d : D} {s : Site} {ds : List Nat} {vs : List Value}
    (hs : d.c.site = s) (hat : (code P L g w).AtD d t)
    (hoff : ∀ q ∈ Control.facts P L g d.c ++ dF L g d, q.1 ∉ ds) (hnd : ds.Nodup) :
    At { setRegs t ds vs with pc := t.pc + 1, sub := 0, acc := [] } (s.pc + 1)
      (ds.zip vs ++ (Control.facts P L g d.c ++ dF L g d)) := by
  obtain ⟨hp, -, -, hf, hF⟩ := hat
  obtain ⟨-, -, -, hskF⟩ := setRegs_skel t ds vs
  refine ⟨?_, rfl, rfl, hskF.trans hf, (holds_append _ _ _).mpr
    ⟨holds_setRegs_zip t ds vs hnd, holds_setRegs_off hF hoff⟩⟩
  show t.pc + 1 = _; rw [hp, pc_eq hs]

/-- **The last element of a scale load.** -/
theorem ds_scale {d : D} {r : Fin 4} {a : MemAccess} (hs : d.c.site = .scale r)
    (hc : kernel.code[(Site.scale r).pc]? = some ⟨none, .mem a⟩) (hk : a.kind = .load)
    (hnc : a.nc = false) (he : a.ext = .same) (hlen : a.regs.length = 4) (hnd : a.regs.Nodup)
    (hoff : ∀ q ∈ Control.facts P L g d.c, q.1 ∉ a.regs)
    (hR : ∀ w0 w1 w2 w3 : Nat, w0 < 2 ^ 32 → w1 < 2 ^ 32 → w2 < 2 ^ 32 → w3 < 2 ^ 32 →
      Reach kernel Assumptions.all L g ((Site.scale r).pc + 1)
        (a.regs.zip (words [w0, w1, w2, w3]) ++ Control.facts P L g d.c)
        (scaleFacts (scBase r) (scWord w0 w1 w2 w3))) :
    DataStep (code P L g w) (dF L g) d := by
  have hF0 : dF L g d = [] := dF_quiet (by rw [hs]; trivial)
  refine @DataStep.load _ _ _ _ _ _ _ _ (fun v d' => ∃ w0 w1 w2 w3, w0 < 2 ^ 32 ∧ w1 < 2 ^ 32 ∧
      w2 < 2 ^ 32 ∧ w3 < 2 ^ 32 ∧ d.c.acc ++ [v] = words [w0, w1, w2, w3] ∧
      dF L g d' = scaleFacts (scBase r) (scWord w0 w1 w2 w3))
    (by rw [pc_eq (P := P) (L := L) (g := g) (w := w) hs]; exact hc) hk hnc he ?_ ?_ ?_
  · intro hm e d' hn
    obtain ⟨c', hc', hd⟩ := next_ctl hn
    rw [hlen] at hm
    have hm' : d.c.el + 1 < 4 := hm
    apply dF_quiet
    rw [dataNext_c hd]
    simp only [Control.succ, hs] at hc'
    split at hc'
    · obtain rfl := Option.some.inj (Option.some.inj hc').symm
      simp only [Control.scaleNext, hm', ↓reduceIte, hs]; trivial
    · cases hc'
  · intro hm x bs d' hn
    rw [hlen] at hm
    have hm' : ¬ d.c.el + 1 < 4 := hm
    obtain ⟨c', hc', hd⟩ := next_ctl hn
    simp only [Control.succ, hs] at hc'
    obtain rfl := Option.some.inj (Option.some.inj hc').symm
    simp only [dataNext, hs, hm', ↓reduceIte] at hd
    obtain ⟨sc, hsc, rfl⟩ := Option.map_eq_some_iff.mp hd
    obtain ⟨w0, w1, w2, w3, b0, b1, b2, b3, hl, hsw⟩ := scaleOf_some hsc
    have hv : loadVal bs = .bits 32 (BitVec.ofNat 64 w3) := by
      have := congrArg List.getLast? hl; simpa [words] using this
    refine ⟨loadVal bs, loadVal_ok hv, w0, w1, w2, w3, b0, b1, b2, b3, hl, ?_⟩
    simp [dF, Control.scaleNext, hm', hsw]
  · intro _ v d' t hq hat
    obtain ⟨w0, w1, w2, w3, b0, b1, b2, b3, hl, hdF⟩ := hq
    have e : t.acc ++ [v] = words [w0, w1, w2, w3] := by
      obtain ⟨-, -, ha, -⟩ := hat
      rw [← hl]; exact congrArg (· ++ [v]) ha
    rw [e, hdF]
    have hu := at_after (vs := words [w0, w1, w2, w3]) hs hat
      (by rw [hF0, List.append_nil]; exact hoff) hnd
    rw [hF0, List.append_nil] at hu
    exact hR w0 w1 w2 w3 b0 b1 b2 b3 _ hu

theorem acc_nil {d : D} {t : TState} (hat : (code P L g w).AtD d t)
    (hi : (code P L g w).inv d) (he : Control.elems d.c.site = 1) : t.acc = [] := by
  have h0 : d.c.el = 0 := by
    have : d.c.el < Control.elems d.c.site := hi
    omega
  obtain ⟨-, -, ha, -⟩ := hat
  exact ha.trans (by simp [Control.D.acc, h0])

/-- **A raw load** (any step): the successor's data facts from the word loaded. -/
theorem ds_rawG {d : D} {r : Fin 4} {s : Fin 8} {a : MemAccess} (hs : d.c.site = .raw r s)
    (hc : kernel.code[(Site.raw r s).pc]? = some ⟨none, .mem a⟩) (hk : a.kind = .load)
    (hnc : a.nc = false) (he : a.ext = .same) (hr : a.regs = [rawReg r s])
    (hoff : ∀ q ∈ Control.facts P L g d.c ++ dF L g d, q.1 ≠ rawReg r s)
    (hR : ∀ x : {x // WordOk x}, Reach kernel Assumptions.all L g ((Site.raw r s).pc + 1)
      ((rawReg r s, .bits 64 (BitVec.ofNat 64 x.1)) :: (Control.facts P L g d.c ++ dF L g d))
      (dF L g ⟨{ d.c with site := Control.rawNext r s }, d.sc, Function.update d.ws s.val x.1,
        d.scOk, update_ok d.wsOk s.val x⟩)) :
    DataStep (code P L g w) (dF L g) d := by
  refine @DataStep.load _ _ _ _ _ _ _ _ (fun v d' => ∃ x : {x // WordOk x},
      v = .bits 64 (BitVec.ofNat 64 x.1) ∧ d' = ⟨{ d.c with site := Control.rawNext r s }, d.sc,
        Function.update d.ws s.val x.1, d.scOk, update_ok d.wsOk s.val x⟩)
    (by rw [pc_eq (P := P) (L := L) (g := g) (w := w) hs]; exact hc) hk hnc he ?_ ?_ ?_
  · intro hm; rw [hr] at hm; exact absurd hm (by simp)
  · intro _ x bs d' hn
    obtain ⟨c', hc', hd⟩ := next_ctl hn
    simp only [Control.succ, hs, Control.dataRd] at hc'
    obtain rfl := Option.some.inj (Option.some.inj hc').symm
    simp only [dataNext, hs] at hd
    obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.mp hd
    obtain ⟨-, hv⟩ := rawOf_some hy
    exact ⟨_, loadVal_ok hv, y, hv, rfl⟩
  · intro hi v d' t hq hat
    obtain ⟨x, rfl, rfl⟩ := hq
    rw [acc_nil hat hi (by rw [hs]; rfl), List.nil_append, hr]
    exact hR x _ (at_after hs hat (fun q hq => by simpa using hoff q hq) (List.nodup_singleton _))

/-- **Raw load 0 of a row**: the halfwords of its word. -/
theorem ds_raw0 {d : D} {r : Fin 4} {a : MemAccess} (hs : d.c.site = .raw r 0)
    (hc : kernel.code[(Site.raw r 0).pc]? = some ⟨none, .mem a⟩) (hk : a.kind = .load)
    (hnc : a.nc = false) (he : a.ext = .same) (hr : a.regs = [rawReg r 0])
    (hoff : ∀ q ∈ Control.facts P L g d.c ++ scaleFacts (scBase r) d.sc, q.1 ≠ rawReg r 0)
    (hR : ∀ x, x < 2 ^ 64 → Reach kernel Assumptions.all L g ((Site.raw r 0).pc + 1)
      ((rawReg r 0, .bits 64 (BitVec.ofNat 64 x)) ::
        (Control.facts P L g d.c ++ scaleFacts (scBase r) d.sc))
      (scaleFacts (scBase r) d.sc ++ halfFacts r 0 x)) :
    DataStep (code P L g w) (dF L g) d := by
  have hF : dF L g d = scaleFacts (scBase r) d.sc := by simp [dF, hs]
  apply ds_rawG hs hc hk hnc he hr (by rw [hF]; exact hoff)
  intro x
  rw [hF]
  have e : Control.rawNext r 0 = .raw r 1 := rfl
  obtain ⟨x, -, hx⟩ := x
  simpa [dF, e] using hR x hx

/-- **Raw load `s + 1` of a row**: the chunk of step `s`. -/
theorem ds_raw {d : D} {r : Fin 4} {s s1 : Fin 8} {a : MemAccess} (hs : d.c.site = .raw r s1)
    (h1 : s1.val = s.val + 1) (hn : Control.rawNext r s1 = .store r s)
    (hc : kernel.code[(Site.raw r s1).pc]? = some ⟨none, .mem a⟩) (hk : a.kind = .load)
    (hnc : a.nc = false) (he : a.ext = .same) (hr : a.regs = [rawReg r s1])
    (hoff : ∀ q ∈ Control.facts P L g d.c ++ (scaleFacts (scBase r) d.sc ++
      halfFacts r s (d.ws s)), q.1 ≠ rawReg r s1)
    (hR : ∀ x, x < 2 ^ 64 → Reach kernel Assumptions.all L g ((Site.raw r s1).pc + 1)
      ((rawReg r s1, .bits 64 (BitVec.ofNat 64 x)) ::
        (Control.facts P L g d.c ++ (scaleFacts (scBase r) d.sc ++ halfFacts r s (d.ws s))))
      ((scaleFacts (scBase r) d.sc ++ [(rawReg r s1, .bits 64 (BitVec.ofNat 64 x))]) ++
        [(chunkReg r s, dequantChunk (d.ws s) (selByte L g d.sc s))])) :
    DataStep (code P L g w) (dF L g) d := by
  have hF : dF L g d = scaleFacts (scBase r) d.sc ++ halfFacts r s (d.ws s) := by
    simp [dF, hs, h1]
  apply ds_rawG hs hc hk hnc he hr (by rw [hF]; exact hoff)
  intro x
  rw [hF]
  have h7 : s.val < 7 := by omega
  have hne : s.val ≠ s1.val := by omega
  obtain ⟨x, -, hx⟩ := x
  simpa [dF, hn, h7, chunkVal, Function.update_of_ne hne, ← h1] using hR x hx

/-- **A store** (any step): the successor's data facts from the start state's. -/
theorem ds_storeG {d : D} {r : Fin 4} {s : Fin 8} {a : MemAccess} (hs : d.c.site = .store r s)
    (hc : kernel.code[(Site.store r s).pc]? = some ⟨none, .mem a⟩) (hk : a.kind = .store)
    (hsr : a.srcs.length = 1)
    (hR : Reach kernel Assumptions.all L g ((Site.store r s).pc + 1)
      (Control.facts P L g d.c ++ dF L g d)
      (dF L g { d with c := { d.c with site := Control.storeNext r s } })) :
    DataStep (code P L g w) (dF L g) d := by
  apply DataStep.store (by rw [pc_eq (P := P) (L := L) (g := g) (w := w) hs]; exact hc) hk hsr
  intro hi e d' t hn hat
  obtain ⟨c', hc', hd⟩ := next_ctl hn
  simp only [Control.succ, hs] at hc'
  obtain rfl := Option.some.inj (Option.some.inj hc').symm
  unfold dataNext at hd
  split at hd
  · rename_i h _; rw [hs] at h; cases h
  · rename_i h _; rw [hs] at h; cases h
  · obtain rfl := (Option.some.inj hd).symm
    have ha := acc_nil (t := t) hat hi (by rw [hs]; rfl)
    obtain ⟨hp, -, -, hf, hF⟩ := hat
    refine hR _ ⟨?_, rfl, ha, hf, hF⟩
    show t.pc + 1 = _; rw [hp, pc_eq hs]

/-- **Store `s ≤ 5` of a row**: the halfwords of the next word. -/
theorem ds_store {d : D} {r : Fin 4} {s s2 : Fin 8} {a : MemAccess} (hs : d.c.site = .store r s)
    (h2 : s2.val = s.val + 2) (hn : Control.storeNext r s = .raw r s2)
    (hc : kernel.code[(Site.store r s).pc]? = some ⟨none, .mem a⟩) (hk : a.kind = .store)
    (hsr : a.srcs.length = 1)
    (hR : Reach kernel Assumptions.all L g ((Site.store r s).pc + 1)
      (Control.facts P L g d.c ++ ((scaleFacts (scBase r) d.sc ++
        [(rawReg r (s.val + 1), .bits 64 (BitVec.ofNat 64 (d.ws (s.val + 1))))]) ++
        [(chunkReg r s, chunkVal L g d s)]))
      (scaleFacts (scBase r) d.sc ++ halfFacts r (s.val + 1) (d.ws (s.val + 1)))) :
    DataStep (code P L g w) (dF L g) d := by
  apply ds_storeG hs hc hk hsr
  have h7 : s.val < 7 := by omega
  have h0 : s2.val ≠ 0 := by omega
  have e : s2.val - 1 = s.val + 1 := by omega
  simpa [dF, hs, hn, h7, h0, e] using hR

/-- **Store 6 of a row**: the last word's halfwords and chunk. -/
theorem ds_store6 {d : D} {r : Fin 4} {a : MemAccess} (hs : d.c.site = .store r 6)
    (hc : kernel.code[(Site.store r 6).pc]? = some ⟨none, .mem a⟩) (hk : a.kind = .store)
    (hsr : a.srcs.length = 1)
    (hR : Reach kernel Assumptions.all L g ((Site.store r 6).pc + 1)
      (Control.facts P L g d.c ++ ((scaleFacts (scBase r) d.sc ++
        [(rawReg r 7, .bits 64 (BitVec.ofNat 64 (d.ws 7)))]) ++ [(chunkReg r 6, chunkVal L g d 6)]))
      [(chunkReg r 7, dequantChunk (d.ws 7) (selByte L g d.sc 7))]) :
    DataStep (code P L g w) (dF L g) d := by
  apply ds_storeG hs hc hk hsr
  have e : Control.storeNext r 6 = .store r 7 := rfl
  simpa [dF, hs, e, chunkVal] using hR

/-! ### Quiet successors and the registers a load writes -/

/-- A site whose successors have no data facts. -/
def QuietSrc : Site → Prop
  | .scale _ => False
  | .raw _ _ => False
  | .store _ s => s.val = 7
  | _ => True

/-- **The successors of a quiet source are quiet.** -/
theorem quiet_succ {c c' : Control.D} {e : Event} (h : Control.succ P L g c e = some (some c'))
    (hq : QuietSrc c.site) : Quiet c'.site := by
  obtain ⟨site, el, ac, l0, l1, cnt, sb, pb⟩ := c
  cases site with
  | smr =>
    obtain rfl := Option.some.inj (Option.some.inj h)
    unfold Control.afterSmr Control.afterA
    dsimp only
    repeat' split
    all_goals exact .intro
  | lenA =>
    simp only [Control.succ] at h
    split at h
    · unfold Code.ncNext at h
      split at h
      · obtain rfl := Option.some.inj (Option.some.inj h)
        unfold Control.afterA
        split <;> exact .intro
      · cases h
      · cases h
    · cases h
  | lenB =>
    simp only [Control.succ] at h
    split at h
    · unfold Code.ncNext at h
      split at h
      · obtain rfl := Option.some.inj (Option.some.inj h)
        exact .intro
      · cases h
      · cases h
    · cases h
  | wq =>
    simp only [Control.succ] at h
    split at h
    · obtain rfl := Option.some.inj (Option.some.inj h)
      unfold Control.loopEntry
      repeat' split
      all_goals exact .intro
    · cases h
  | wraw | wsv =>
    simp only [Control.succ, Control.poll] at h
    split at h
    · obtain rfl := Option.some.inj (Option.some.inj h)
      split <;> exact .intro
    · cases h
  | scale | raw => exact hq.elim
  | store r s =>
    obtain rfl : s = 7 := Fin.ext hq
    obtain rfl := Option.some.inj (Option.some.inj h)
    show Quiet (Control.rowNext r)
    fin_cases r <;> exact .intro
  | fpx | arrD | bar =>
    obtain rfl := Option.some.inj (Option.some.inj h)
    exact .intro
  | arrF =>
    obtain rfl := Option.some.inj (Option.some.inj h)
    unfold Control.advance
    dsimp only
    split <;> exact .intro
  | exit => cases h

theorem key_scale {b sc : Nat} {q : Nat × Value} (h : q ∈ scaleFacts b sc) :
    b ≤ q.1 ∧ q.1 < b + 16 := by
  simp only [scaleFacts, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> dsimp only <;> omega

/-- The control facts of a scale load leave its word registers. -/
theorem hoff_scale {d : D} {r : Fin 4} (hs : d.c.site = .scale r) {regs : List Nat}
    (h : ∀ k ∈ regs, k ∉ Control.ctlLive (Site.scale r).pc) :
    ∀ q ∈ Control.facts P L g d.c, q.1 ∉ regs := fun q hq hk =>
  not_mem_factsFrom (by rw [hs]; exact h _ hk) q hq rfl

/-- The facts before a raw load leave its register. -/
theorem hoff_raw {d : D} {r : Fin 4} {s1 : Fin 8} (hs : d.c.site = .raw r s1) (s : Fin 8) (y : Nat)
    (hk : rawReg r s1 ∉ Control.ctlLive (Site.raw r s1).pc) :
    ∀ q ∈ Control.facts P L g d.c ++ (scaleFacts (scBase r) d.sc ++ halfFacts r s y),
      q.1 ≠ rawReg r s1 := by
  intro q hq
  have h0 : 3837 ≤ rawReg r s1 := by unfold rawReg; split_ifs <;> omega
  have hr := r.isLt
  have hs8 := s.isLt
  rcases List.mem_append.mp hq with hq | hq
  · exact not_mem_factsFrom (by rw [hs]; exact hk) q hq
  rcases List.mem_append.mp hq with hq | hq
  · have := key_scale hq; unfold scBase at this; omega
  · simp only [halfFacts, halfReg, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl <;> dsimp only <;> omega

theorem hoff_raw0 {d : D} {r : Fin 4} (hs : d.c.site = .raw r 0)
    (hk : rawReg r 0 ∉ Control.ctlLive (Site.raw r 0).pc) :
    ∀ q ∈ Control.facts P L g d.c ++ scaleFacts (scBase r) d.sc, q.1 ≠ rawReg r 0 :=
  fun q hq => hoff_raw hs 0 0 hk q (by
    rcases List.mem_append.mp hq with h | h
    · exact List.mem_append_left _ h
    · exact List.mem_append_right _ (List.mem_append_left _ h))

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.Data
