-- SPDX-License-Identifier: Apache-2.0
-- domain: valid-rows
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.Data.StrictBase
public import Lemmas.Flow.Step.VecLoad

@[expose] public section

/-! # The strict steps of warpgroup 2's data machine, by kind

`sk_<kind>`: the strict step (`Code.StepFor`) of the data machine at a state of a data site, for
every event: the event reads or writes, the control successor is followed with its data, and the
local code from there reaches the successor's site with its facts, control facts included. The
local code is stated as an exact segment (`Gen/DataSegs*.lean`), taken as a hypothesis of the kind
and given by the generated dispatch (`Gen/DataStepsS.lean`), which also gives the kind its site's
pcs and instruction.

* `sk_scale_mid`, `sk_scale_last`: an element of a row's scale load (the vector load of four
  words); the middle elements keep the value read, the last follows only valid scale bytes;
* `sk_raw0`, `sk_raw`: raw load `s` of a row (`sk_rawG`: any); follows only a valid raw word;
* `sk_store`, `sk_store6`: store `s ≤ 5` (the next word's halfwords) and store 6 (the last
  word's halfwords and chunk). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.Data
open PTX PTX.Proof PTX.Flow PTX.Flow.Code PTX.Kernels.FlashMlaSparseDecodeH64
open PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Numeric.Dequant

noncomputable section

variable {P : Params} {L : Launch} {g : Nat} {w : BitVec 64}

/-- An event that, when it reads, reads bytes that rebuild to a value. -/
def WfE (e : Event) : Prop := ∀ x bs, e.kind = .rd x bs → ∃ v, rebuild 3 bs = .ok v

theorem elems_pos (s : Site) : 0 < Control.elems s := by
  unfold Control.elems; split <;> decide

theorem dropReg_self {r : Nat} {F : List (Nat × Value)} (h : ∀ q ∈ F, q.1 ≠ r) :
    dropReg r F = F := by
  unfold dropReg
  exact List.filter_eq_self.mpr fun q hq => by simpa using h q hq

theorem sk_rawG {d : D} {r : Fin 4} {s : Fin 8} {a : MemAccess} {nx : Nat}
    (hs : d.c.site = .raw r s) (he0 : d.c.el = 0)
    (hc : kernel.code[(Site.raw r s).pc]? = some ⟨none, .mem a⟩) (hk : a.kind = .load)
    (hnc : a.nc = false) (he : a.ext = .same) (hr : a.regs = [rawReg r s])
    (hoff : ∀ q ∈ (code P L g w).facts d, q.1 ≠ rawReg r s)
    (hpc : (Control.rawNext r s).pc = nx)
    (hR : ∀ x : {x // WordOk x}, ∃ n, Seg kernel Assumptions.all L g n ((Site.raw r s).pc + 1)
      ((rawReg r s, .bits 64 (BitVec.ofNat 64 x.1)) :: (code P L g w).facts d) nx
      ((code P L g w).facts ⟨{ d.c with site := Control.rawNext r s }, d.sc,
        Function.update d.ws s.val x.1, d.scOk, update_ok d.wsOk s.val x⟩)) (e : Event) :
    (code P L g w).StepFor d e := by
  have hsub : (code P L g w).sub d = 0 := he0
  have hacc : (code P L g w).acc d = [] := by simp [Control.D.acc, he0]
  refine fun {t u} ins hat hi hc' hf => (Code.step_load_sel (C := code P L g w)
    (nv := fun v => some ((rawOf v).map fun x => ⟨{ d.c with site := Control.rawNext r s }, d.sc,
      Function.update d.ws s.val x.1, d.scOk, update_ok d.wsOk s.val x⟩))
    (by rw [pc_eq hs]; exact hc) hk hnc he hr ?_ ?_ hsub hacc (fun _ => by simp) ?_).step
    ins hat hi hc' hf
  · intro x bs v hv
    simp [succ, Control.succ, hs, Control.dataRd, dataNext, loadVal, hv]
    rfl
  · intro x bs f hv
    right
    simp [succ, Control.succ, hs, Control.dataRd, dataNext, loadVal, hv, rawOf, wordOf,
      Except.toOption]
  · intro v d' hv
    obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.mp (Option.some.inj hv)
    obtain ⟨-, rfl⟩ := rawOf_some hx
    refine ⟨fun _ => ?_, he0, by simp [Control.D.acc, he0], fun _ => ?_⟩
    · rw [dropReg_self hoff]
      obtain ⟨n, hseg⟩ := hR x
      refine ⟨n, ?_⟩
      show Seg _ _ _ _ _ ((code P L g w).pc d + 1) _ ((Control.rawNext r s).pc) _
      rw [pc_eq hs, hpc]
      exact hseg
    · show d.c.el < Control.elems (Control.rawNext r s)
      rw [he0]; exact elems_pos _

theorem sk_raw0 {d : D} {r : Fin 4} {a : MemAccess} {nx : Nat} (hs : d.c.site = .raw r 0)
    (he0 : d.c.el = 0) (hc : kernel.code[(Site.raw r 0).pc]? = some ⟨none, .mem a⟩)
    (hk : a.kind = .load) (hnc : a.nc = false) (he : a.ext = .same)
    (hr : a.regs = [rawReg r 0]) (hno : rawReg r 0 ∉ Control.ctlLive (Site.raw r 0).pc)
    (hpc : (Site.raw r 1).pc = nx)
    (hR : ∀ x, x < 2 ^ 64 → ∃ n, Seg kernel Assumptions.all L g n ((Site.raw r 0).pc + 1)
      ((rawReg r 0, .bits 64 (BitVec.ofNat 64 x)) ::
        (Control.facts P L g d.c ++ scaleFacts (scBase r) d.sc)) nx
      (Control.facts P L g { d.c with site := .raw r 1 } ++
        (scaleFacts (scBase r) d.sc ++ halfFacts r 0 x))) (e : Event) :
    (code P L g w).StepFor d e := by
  have hF : (code P L g w).facts d = Control.facts P L g d.c ++ scaleFacts (scBase r) d.sc := by
    simp [dF, hs]
  apply sk_rawG hs he0 hc hk hnc he hr (by rw [hF]; exact hoff_raw0 hs hno) hpc
  intro x
  obtain ⟨x, -, hx⟩ := x
  simpa [code, dF, hs, Control.rawNext] using hR x hx

theorem sk_raw {d : D} {r : Fin 4} {s s1 : Fin 8} {a : MemAccess} {nx : Nat}
    (hs : d.c.site = .raw r s1) (he0 : d.c.el = 0) (h1 : s1.val = s.val + 1)
    (hn : Control.rawNext r s1 = .store r s)
    (hc : kernel.code[(Site.raw r s1).pc]? = some ⟨none, .mem a⟩) (hk : a.kind = .load)
    (hnc : a.nc = false) (he : a.ext = .same) (hr : a.regs = [rawReg r s1])
    (hno : rawReg r s1 ∉ Control.ctlLive (Site.raw r s1).pc) (hpc : (Site.store r s).pc = nx)
    (hR : ∀ x, x < 2 ^ 64 → ∃ n, Seg kernel Assumptions.all L g n ((Site.raw r s1).pc + 1)
      ((rawReg r s1, .bits 64 (BitVec.ofNat 64 x)) ::
        (Control.facts P L g d.c ++ (scaleFacts (scBase r) d.sc ++ halfFacts r s (d.ws s)))) nx
      (Control.facts P L g { d.c with site := .store r s } ++
        ((scaleFacts (scBase r) d.sc ++ [(rawReg r s1, .bits 64 (BitVec.ofNat 64 x))]) ++
          [(chunkReg r s, dequantChunk (d.ws s) (selByte L g d.sc s))]))) (e : Event) :
    (code P L g w).StepFor d e := by
  have hF : (code P L g w).facts d = Control.facts P L g d.c ++
      (scaleFacts (scBase r) d.sc ++ halfFacts r s (d.ws s)) := by
    simp [dF, hs, h1]
  apply sk_rawG hs he0 hc hk hnc he hr (by rw [hF]; exact hoff_raw hs s _ hno)
    (hn ▸ hpc)
  intro x
  have h7 : s.val < 7 := by omega
  have hz : s1.val ≠ 0 := by omega
  have hs1 : s1.val - 1 = s.val := by omega
  have hne : s.val ≠ s1.val := by omega
  obtain ⟨x, -, hx⟩ := x
  simpa [code, dF, hs, hn, h7, hz, hs1, chunkVal, Function.update_of_ne hne, ← h1] using hR x hx

theorem sk_store {d : D} {r : Fin 4} {s s2 : Fin 8} {a : MemAccess} {nx : Nat}
    (hs : d.c.site = .store r s) (he0 : d.c.el = 0)
    (h2 : s2.val = s.val + 2) (hn : Control.storeNext r s = .raw r s2)
    (hc : kernel.code[(Site.store r s).pc]? = some ⟨none, .mem a⟩) (hk : a.kind = .store)
    (hsr : a.srcs.length = 1) (hpc : (Site.raw r s2).pc = nx)
    (hR : ∃ n, Seg kernel Assumptions.all L g n ((Site.store r s).pc + 1)
      (Control.facts P L g d.c ++ ((scaleFacts (scBase r) d.sc ++
        [(rawReg r (s.val + 1), .bits 64 (BitVec.ofNat 64 (d.ws (s.val + 1))))]) ++
        [(chunkReg r s, chunkVal L g d s)])) nx
      (Control.facts P L g { d.c with site := .raw r s2 } ++
        (scaleFacts (scBase r) d.sc ++ halfFacts r (s.val + 1) (d.ws (s.val + 1)))))
    (e : Event) : (code P L g w).StepFor d e := by
  have hsub : (code P L g w).sub d = 0 := he0
  have hacc : (code P L g w).acc d = [] := by simp [Control.D.acc, he0]
  have h7 : s.val < 7 := by omega
  have h0 : s2.val ≠ 0 := by omega
  have e1 : s2.val - 1 = s.val + 1 := by omega
  refine fun {t u} ins hat hi hc' hf => (Code.step_vec_last (C := code P L g w)
    (dn := ⟨{ d.c with site := Control.storeNext r s }, d.sc, d.ws, d.scOk, d.wsOk⟩)
    (by rw [pc_eq hs]; exact hc) hk (by rw [hsub]; simp [hsr]) ?_ hacc ?_).step ins hat hi hc' hf
  · intro e
    simp [succ, Control.succ, hs, dataNext]
  · refine ⟨fun _ => ?_, he0, by simp [Control.D.acc, he0], fun _ => ?_⟩
    · obtain ⟨n, hseg⟩ := hR
      refine ⟨n, ?_⟩
      have hF : (code P L g w).facts d = Control.facts P L g d.c ++ ((scaleFacts (scBase r) d.sc ++
          [(rawReg r (s.val + 1), .bits 64 (BitVec.ofNat 64 (d.ws (s.val + 1))))]) ++
          [(chunkReg r s, chunkVal L g d s)]) := by
        simp [dF, hs, h7]
      have hG : (code P L g w).facts ⟨{ d.c with site := Control.storeNext r s }, d.sc, d.ws,
          d.scOk, d.wsOk⟩ = Control.facts P L g { d.c with site := .raw r s2 } ++
          (scaleFacts (scBase r) d.sc ++ halfFacts r (s.val + 1) (d.ws (s.val + 1))) := by
        simp [dF, hn, h0, e1]
      rw [hF, hG]
      show Seg _ _ _ _ _ ((code P L g w).pc d + 1) _ ((Control.storeNext r s).pc) _
      rw [pc_eq hs, hn, hpc]
      exact hseg
    · show d.c.el < Control.elems (Control.storeNext r s)
      rw [he0]; exact elems_pos _

theorem sk_store6 {d : D} {r : Fin 4} {a : MemAccess} {nx : Nat} (hs : d.c.site = .store r 6)
    (he0 : d.c.el = 0) (hc : kernel.code[(Site.store r 6).pc]? = some ⟨none, .mem a⟩)
    (hk : a.kind = .store) (hsr : a.srcs.length = 1) (hpc : (Site.store r 7).pc = nx)
    (hR : ∃ n, Seg kernel Assumptions.all L g n ((Site.store r 6).pc + 1)
      (Control.facts P L g d.c ++ ((scaleFacts (scBase r) d.sc ++
        [(rawReg r 7, .bits 64 (BitVec.ofNat 64 (d.ws 7)))]) ++ [(chunkReg r 6, chunkVal L g d 6)]))
      nx (Control.facts P L g { d.c with site := .store r 7 } ++
        [(chunkReg r 7, dequantChunk (d.ws 7) (selByte L g d.sc 7))])) (e : Event) :
    (code P L g w).StepFor d e := by
  have hsub : (code P L g w).sub d = 0 := he0
  have hacc : (code P L g w).acc d = [] := by simp [Control.D.acc, he0]
  have hn : Control.storeNext r 6 = .store r 7 := rfl
  refine fun {t u} ins hat hi hc' hf => (Code.step_vec_last (C := code P L g w)
    (dn := ⟨{ d.c with site := Control.storeNext r 6 }, d.sc, d.ws, d.scOk, d.wsOk⟩)
    (by rw [pc_eq hs]; exact hc) hk (by rw [hsub]; simp [hsr]) ?_ hacc ?_).step ins hat hi hc' hf
  · intro e
    simp [succ, Control.succ, hs, dataNext]
  · refine ⟨fun _ => ?_, he0, by simp [Control.D.acc, he0], fun _ => ?_⟩
    · obtain ⟨n, hseg⟩ := hR
      refine ⟨n, ?_⟩
      have hF : (code P L g w).facts d = Control.facts P L g d.c ++ ((scaleFacts (scBase r) d.sc ++
          [(rawReg r 7, .bits 64 (BitVec.ofNat 64 (d.ws 7)))]) ++
          [(chunkReg r 6, chunkVal L g d 6)]) := by
        simp [dF, hs]
      have hG : (code P L g w).facts ⟨{ d.c with site := Control.storeNext r 6 }, d.sc, d.ws,
          d.scOk, d.wsOk⟩ = Control.facts P L g { d.c with site := .store r 7 } ++
          [(chunkReg r 7, dequantChunk (d.ws 7) (selByte L g d.sc 7))] := by
        simp [dF, hn, chunkVal]
      rw [hF, hG]
      show Seg _ _ _ _ _ ((code P L g w).pc d + 1) _ ((Control.storeNext r 6).pc) _
      rw [pc_eq hs, hn, hpc]
      exact hseg
    · show d.c.el < Control.elems (Control.storeNext r 6)
      rw [he0]; exact elems_pos _

theorem sk_scale_mid {d : D} {r : Fin 4} {a : MemAccess} (hs : d.c.site = .scale r)
    (hm : d.c.el + 1 < 4)
    (hc : kernel.code[(Site.scale r).pc]? = some ⟨none, .mem a⟩) (hk : a.kind = .load)
    (hnc : a.nc = false) (he : a.ext = .same) (hlen : a.regs.length = 4) {e : Event}
    (hwf : ∀ x bs, e = ⟨(Site.scale r).pc, .rd x bs⟩ → ∃ v, rebuild 3 bs = .ok v) :
    (code P L g w).StepFor d e := by
  have hF0 : dF L g d = [] := dF_quiet (by rw [hs]; trivial)
  refine fun {t u} ins hat hi hc' hf => (stepFor_vload_mid (C := code P L g w)
    (dn := fun v => ⟨Control.scaleNext r d.c v, d.sc, d.ws, d.scOk, d.wsOk⟩) (e := e)
    (by rw [pc_eq hs]; exact hc) hk hnc he (by rw [hlen]; exact hm)
    (fun x bs hq => hwf x bs (hq.trans (by rw [pc_eq hs]))) ?_ ?_ ?_ ?_ ?_ ?_) ins hat hi hc' hf
  · intro x bs v hv
    simp [succ, Control.succ, hs, dataNext, hm, hv, Except.toOption]
  · intro v
    simp [Control.scaleNext, hm, hs]
  · intro v
    simp [Control.scaleNext, hm]
  · intro v
    simp [Control.scaleNext, hm, Control.D.acc]
  · intro v
    simp only [dF, Control.scaleNext, hm, hs, ↓reduceIte, List.append_nil]
    unfold Control.facts
    rw [hs]
    rfl
  · intro _ v
    show (Control.scaleNext r d.c v).el < Control.elems (Control.scaleNext r d.c v).site
    simp [Control.scaleNext, hm, hs, Control.elems]

theorem scaleOf_pred (l : List Value) (b : Bool) : scaleOf (l ++ [.pred b]) = none := by
  unfold scaleOf
  split
  · rename_i v0 v1 v2 v3 h
    have h3 : v3 = .pred b := by
      have := congrArg List.getLast? h
      simpa using this.symm
    subst h3
    simp [wordOf]
  · rfl

theorem sk_scale_last {d : D} {r : Fin 4} {a : MemAccess} {nx : Nat} {rs : List Nat}
    (hs : d.c.site = .scale r) (hl : ¬ d.c.el + 1 < 4)
    (hc : kernel.code[(Site.scale r).pc]? = some ⟨none, .mem a⟩) (hk : a.kind = .load)
    (hnc : a.nc = false) (he : a.ext = .same) (hregs : a.regs = rs) (hnd : rs.Nodup)
    (hno : ∀ k ∈ rs, k ∉ Control.ctlLive (Site.scale r).pc) (hlen : rs.length = 4)
    (hpc : (Site.raw r 0).pc = nx)
    (hR : ∀ w0 w1 w2 w3 : Nat, w0 < 2 ^ 32 → w1 < 2 ^ 32 → w2 < 2 ^ 32 → w3 < 2 ^ 32 →
      ∃ n, Seg kernel Assumptions.all L g n ((Site.scale r).pc + 1)
        (rs.zip (words [w0, w1, w2, w3]) ++ Control.facts P L g d.c) nx
        (Control.facts P L g { d.c with site := .raw r 0, el := 0, ac := [] } ++
          scaleFacts (scBase r) (scWord w0 w1 w2 w3))) (e : Event) :
    (code P L g w).StepFor d e := by
  have hF0 : dF L g d = [] := dF_quiet (by rw [hs]; trivial)
  have hF : (code P L g w).facts d = Control.facts P L g d.c := by simp [hF0]
  refine fun {t u} ins hat hi hc' hf => (Code.step_vload_last (C := code P L g w)
    (nv := fun v => some ((scaleOf (d.c.acc ++ [v])).map fun sc =>
      ⟨Control.scaleNext r d.c v, sc.1, d.ws, sc.2, d.wsOk⟩))
    (by rw [pc_eq hs]; exact hc) hk hnc he (by rw [hregs, hlen]; exact hl) (hregs ▸ hnd)
    (by rw [hF, hregs]; exact fun q hq hk' => hoff_scale hs hno q hq hk') ?_ ?_
    (fun _ => by simp) ?_).step ins hat hi hc' hf
  · intro x bs v hv
    simp [succ, Control.succ, hs, dataNext, hl, hv, loadVal, Except.toOption]
  · intro x bs f hv
    right
    simp [succ, Control.succ, hs, dataNext, hl, hv, loadVal, Except.toOption, scaleOf_pred]
  · intro v d' hv
    obtain ⟨sc, hsc, rfl⟩ := Option.map_eq_some_iff.mp (Option.some.inj hv)
    obtain ⟨w0, w1, w2, w3, b0, b1, b2, b3, hw, hsw⟩ := scaleOf_some hsc
    refine ⟨fun _ => ?_, by simp [Control.scaleNext, hl], by simp [Control.scaleNext, hl,
      Control.D.acc], fun _ => ?_⟩
    · obtain ⟨n, hseg⟩ := hR w0 w1 w2 w3 b0 b1 b2 b3
      refine ⟨n, ?_⟩
      have hG : (code P L g w).facts ⟨Control.scaleNext r d.c v, sc.1, d.ws, sc.2, d.wsOk⟩ =
          Control.facts P L g { d.c with site := .raw r 0, el := 0, ac := [] } ++
            scaleFacts (scBase r) (scWord w0 w1 w2 w3) := by
        simp [dF, Control.scaleNext, hl, hsw]
      rw [hG]
      show Seg _ _ _ _ _ ((code P L g w).pc d + 1) _ ((Control.scaleNext r d.c v).site.pc) _
      have hp : (Control.scaleNext r d.c v).site.pc = nx := by
        simp [Control.scaleNext, hl, hpc]
      rw [pc_eq hs, hp]
      have : (code P L g w).acc d ++ [v] = words [w0, w1, w2, w3] := hw
      rw [hF, this, hregs]
      exact hseg
    · show (Control.scaleNext r d.c v).el < Control.elems (Control.scaleNext r d.c v).site
      simp [Control.scaleNext, hl, Control.elems]
end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.Data
