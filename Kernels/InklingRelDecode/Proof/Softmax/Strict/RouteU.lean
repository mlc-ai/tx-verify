-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module
public import Kernels.InklingRelDecode.Proof.Softmax.Strict.RouteC
import Kernels.InklingRelDecode.Proof.Softmax.Data.Rescale
import Kernels.InklingRelDecode.Gen.TypedLateLane01
import Kernels.InklingRelDecode.Gen.TypedLate01
import Kernels.InklingRelDecode.Flow.Code.Part036
import Lemmas.Flow.IssueNext
@[expose] public section
/-! # The update of the running maximum (pc 949) and the sites that jump to it -/
namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Strict
open PTX PTX.Proof PTX.Flow PTX.Flow.TyG PTX.Flow.Havoc PTX.Assumption
open PTX.Kernels.InklingRelDecode.Gen.TypedLateQt
set_option maxRecDepth 100000
variable {e : Control.Entry} {L : Launch} {g : Nat}

theorem dat32_alpha {t : TState} {m mx : Value} (h1 : t.regs 1914 = some m)
    (h2 : t.regs 1522 = some mx) (hT : TypedF (lateQt 949) t) : Dat32 m ∧ Dat32 mx := by
  obtain ⟨x, hx, hd⟩ := d32_ok (r := 1914) (by decide +kernel) hT
  obtain ⟨y, hy, hd'⟩ := d32_ok (r := 1522) (by decide +kernel) hT
  rw [h1] at hx
  rw [h2] at hy
  cases hx
  cases hy
  exact ⟨hd, hd'⟩

theorem exec_upd {F : List (Nat × Value)} (m mx : Value)
    (h1 : (1914, m) ∈ F) (h2 : (1522, mx) ∈ F)
    (h3 : (168, Lib.alphaVal (Data.scaleW L) m mx 168) ∈ F) {t : TState} (ht : At t 949 F)
    (hT : TypedF (lateQt 949) t) :
    execLocalA Assumptions.all L g t (XItem.base Lib.updItem).op =
      .ok (PTX.next (setReg t 1914 (Lib.mNext (Data.scaleW L) m mx))) := by
  obtain ⟨hpc, -, -, -, hregs⟩ := ht
  have hat := (Lib.upd_at (L := L) (g := g)).1
  obtain ⟨hd1, hd2⟩ := dat32_alpha (holds_mem hregs h1) (holds_mem hregs h2) hT
  have hr : ∀ r ∈ (XItem.base Lib.updItem).reads,
      t.regs r = some (Lib.alphaVal (Data.scaleW L) m mx r) := by
    intro r hr
    simp [XItem.reads, OItem.reads, Lib.updItem, Flow.opndRegs] at hr
    rcases hr with rfl | rfl | rfl
    · exact holds_mem hregs h3
    · rw [Data.alphaVal_m]; exact holds_mem hregs h1
    · rw [Data.alphaVal_mx]; exact holds_mem hregs h2
  have hq : (XItem.base Lib.updItem).req (Lib.alphaVal (Data.scaleW L) m mx) = true := by
    have pred : isPred (Lib.alphaVal (Data.scaleW L) m mx 168) = true := by
      simp [Lib.alphaVal, Lib.alphaRest, xFinal, XItem.upd, XItem.vals, OItem.vals, isPred,
        Function.update]
    simp [XItem.req, OItem.req, Lib.updItem, pred, isRegOrF32]
  have hx := XItem.exec (XItem.base Lib.updItem) (V := Lib.alphaVal (Data.scaleW L) m mx) (t := t)
    (hpc ▸ hat.2.1) (hat.2.2 t hpc) hr hq
  have hc : (XItem.base Lib.updItem).cond (Lib.alphaVal (Data.scaleW L) m mx) := by
    simp only [XItem.cond, OItem.cond, Lib.updItem, opndVal, Data.alphaVal_m, Data.alphaVal_mx]
    split <;> exact bits_dat32 ‹_›
  rw [hx.1 hc]
  simp [XItem.post, XItem.vals, OItem.vals, Lib.updItem, Lib.mNext, oFinal, OItem.upd,
    Data.alphaVal_m, Data.alphaVal_mx, opndVal]

theorem dat32_mNext {t : TState} {m mx : Value} (h1 : t.regs 1914 = some m)
    (h2 : t.regs 1522 = some mx) (hT : TypedF (lateQt 949) t) (c : Value) :
    Dat32 (Lib.mNext c m mx) := by
  obtain ⟨hd1, hd2⟩ := dat32_alpha h1 h2 hT
  simp only [Lib.mNext, oFinal, OItem.upd, Lib.updItem, OItem.vals, opndVal, Data.alphaVal_m,
    Data.alphaVal_mx]
  simp
  split <;> assumption

/-- **The update of the running maximum at pc 949** writes the new maximum. -/
theorem seg_upd {F G : List (Nat × Value)} (m mx : Value) (h1 : (1914, m) ∈ F)
    (h2 : (1522, mx) ∈ F) (h3 : (168, Lib.alphaVal (Data.scaleW L) m mx 168) ∈ F)
    (hG : ∀ p ∈ G, p = (1914, Lib.mNext (Data.scaleW L) m mx) ∨ (p ∈ F ∧ p.1 ≠ 1914)) :
    SegQ kernel Assumptions.all L g (LQ Assumptions.all L g (LateR' L g)) 949 F 950 G :=
  SegQ.tauAll _ (segQF_set (d := 1914) (tg := .dat32) (v := Lib.mNext (Data.scaleW L) m mx)
    (OItem.instrB_eq (Lib.upd_at (L := L) (g := g)).1.1) (by decide)
    (fun t ht hT => exec_upd m mx h1 h2 h3 ht hT)
    (fun t ht hT => by
      obtain ⟨-, -, -, -, hr⟩ := ht
      exact ⟨_, rfl, dat32_mNext (holds_mem hr h1) (holds_mem hr h2) hT _⟩)
    (by decide +kernel) hG)

variable {i : Nat} {v : Control.Carry} {w : Data.Vals}

/-- The sites that jump to the update of the running maximum. -/
def UpdSite (s : Site) : Prop := s = .shfl6 ∨ s = .shfl12 ∨ s = .waitStO

/-- The words after the update: the running maximum is the new one. -/
noncomputable abbrev updW (L : Launch) (w : Data.Vals) : Data.Vals :=
  { w with
    m := Lib.mNext (Data.scaleW L) w.m w.mx, mp := w.m,
    l := Lib.lStep w.l (Lib.alphaVal (Data.scaleW L) w.m w.mx 507) w.ps }

/-- The words after the update at the shuffle of pc 2234 (the sent and the received word). -/
noncomputable abbrev updW6 (L : Launch) (w : Data.Vals) (a x : Value) : Data.Vals :=
  { updW L w with
    ps := Lib.psWord a x,
    l := Lib.lStep w.l (Lib.alphaVal (Data.scaleW L) w.m w.mx 507) (Lib.psWord a x) }

/-- The facts at the barrier of pc 999 after the update of a round at the site `s`. -/
noncomputable abbrev UG (e : Control.Entry) (L : Launch) (g : Nat) (s : Site) (i : Nat)
    (v : Control.Carry) (w : Data.Vals) : List (Nat × Value) :=
  Data.dF L ⟨⟨.bar20, i, v⟩, updW L w⟩ ++
    factsFrom (Control.ctlLive 999) (Control.valueOf e L g ⟨s, i, v⟩)

/-- **The update of the running maximum and its packs**: from the jump's target to the barrier of
pc 999, for a round that did not end. -/
theorem upd_tail {s : Site} (hs : UpdSite s) (w : Data.Vals) :
    SegQ kernel Assumptions.all L g (LQ Assumptions.all L g (LateR' L g)) 949
      (Data.dF L ⟨⟨s, i, v⟩, w⟩ ++ factsFrom (Control.ctlLive 949)
        (Control.valueOf e L g ⟨s, i, v⟩))
      999 (UG e L g s i v w) := by
  have hr : Data.inRound s = true := by rcases hs with rfl | rfl | rfl <;> rfl
  have hD : Data.dF L ⟨⟨s, i, v⟩, w⟩ =
      [(498, Data.scaleW L), (1914, w.m)] ++ Data.alphaFacts L w := by
    rcases hs with rfl | rfl | rfl <;> rfl
  have hG : ∀ p ∈ UG e L g s i v w, p = (1914, Lib.mNext (Data.scaleW L) w.m w.mx) ∨
      (p ∈ Data.dF L ⟨⟨s, i, v⟩, w⟩ ++ factsFrom (Control.ctlLive 949)
        (Control.valueOf e L g ⟨s, i, v⟩) ∧ p.1 ≠ 1914) := by
    intro p hp
    rcases List.mem_append.mp hp with h | h
    · have hE : Data.dF L ⟨⟨.bar20, i, v⟩, updW L w⟩ =
          [(498, Data.scaleW L), (1914, Lib.mNext (Data.scaleW L) w.m w.mx)] := rfl
      rw [hE] at h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl
      · exact .inr ⟨List.mem_append_left _ (by rw [hD]; simp), by simp⟩
      · exact .inl rfl
    · obtain ⟨r, hr', rfl⟩ := List.mem_map.mp h
      obtain ⟨h1, h2⟩ := (by decide +kernel : ∀ r ∈ Control.ctlLive 999,
        r ∈ Control.ctlLive 949 ∧ r ≠ 1914) r hr'
      exact .inr ⟨List.mem_append_right _ (mem_factsFrom h1), h2⟩
  refine SegQ.comp (b := 950) (G := UG e L g s i v w) (seg_upd w.m w.mx
    (List.mem_append_left _ (by rw [hD]; simp))
    (List.mem_append_left _ (by rw [hD]; simp [Data.alphaFacts]))
    (List.mem_append_left _ (by rw [hD]; simp [Data.alphaFacts])) hG) ?_
  refine SegQ.comp (b := 959) (G := UG e L g s i v w) (by win lw_l01_950) ?_
  refine SegQ.comp (b := 967) (G := UG e L g s i v w) (by win lw_l01_959) ?_
  refine SegQ.comp (b := 975) (G := UG e L g s i v w) (by win lw_l01_967) ?_
  refine SegQ.comp (b := 983) (G := UG e L g s i v w) (by win lw_l01_975) ?_
  refine SegQ.comp (b := 991) (G := UG e L g s i v w) (by win lw_l01_983) ?_
  refine SegQ.comp (b := 999) (G := UG e L g s i v w) (by win lw_l01_991) ?_
  exact SegQ.weaken fun _ h => h

/-- **The wait for the rescale store** continues at the barrier after the update. -/
theorem sstep_waitStO (ev : Event) :
    (Data.code e L g).StepForQP (QTF lateQt) (TauAll kernel Assumptions.all L g (LateR' L g))
      LWf ⟨⟨.waitStO, i, v⟩, w⟩ ev := by
  refine adv_soft (d := ⟨⟨.waitStO, i, v⟩, w⟩) (dn := ⟨⟨.bar20, i, v⟩, updW L w⟩) (p := 2329) rfl
    Flow.code_2329
    (fun _ => fires_tcWaitSt_next) (fun ev => by
      obtain ⟨_, k⟩ := ev; cases k <;> simp [Data.succ, Control.next, Data.record])
    (fun hi => Control.body_inv hi rfl rfl) (by decide +kernel) (by decide +kernel) ?_ ev
  refine SegQ.comp (b := 949) (G := Data.dF L ⟨⟨.waitStO, i, v⟩, w⟩ ++ factsFrom
    (Control.ctlLive 2330) (Control.valueOf e L g ⟨.waitStO, i, v⟩))
    (SegQ.tauAll _ (SegQF.jmpS (qt := lateQt) Flow.code_2330 (fun t _ a ha => Lib.bra_rule t _ ha)
    (segFree (by dsimp only; decide +kernel)) (by dsimp only; decide +kernel))) ?_
  exact SegQ.fromFacts (sub_facts (fun _ h => h) (by decide +kernel))
    (upd_tail (Or.inr (Or.inr rfl)) w)
end PTX.Kernels.InklingRelDecode.Proof.Softmax.Strict
