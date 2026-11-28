-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module
public import Kernels.InklingRelDecode.Proof.Softmax.Strict.RouteJ
public import Kernels.InklingRelDecode.Proof.Softmax.Strict.RouteR
public import Kernels.InklingRelDecode.Proof.Softmax.Strict.Emu
public import Lemmas.Flow.SegQFItems
import Kernels.InklingRelDecode.Proof.Softmax.Data.Alpha
import Kernels.InklingRelDecode.Gen.TypedLateLane05
import Kernels.InklingRelDecode.Gen.TypedLate05
import Kernels.InklingRelDecode.Flow.Code.Part028
import Lemmas.Flow.StepsQFOs
@[expose] public section
/-! # The strict step of the shuffle that exchanges the row maximum (pc 1838) -/
namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Strict
open PTX PTX.Proof PTX.Flow PTX.Flow.TyG PTX.Flow.Havoc PTX.Assumption
open PTX.Kernels.InklingRelDecode.Gen.TypedLateQt
set_option maxRecDepth 100000
variable {e : Control.Entry} {L : Launch} {g : Nat} {i : Nat} {v : Control.Carry} {w : Data.Vals}

/-- **One instruction that writes a datum**, exact: it is a single piece under the lane's fact. -/
theorem seg_single {pc d : Nat} {tg : TagF} {it : XItem} {V : Nat → Value}
    {x : Value} {S T : List Nat} {H : List (Nat × Value)}
    (hat : OAt kernel Assumptions.all L g pc [it]) (hv : it.vals V = [(d, x)])
    (hs : singleOk it.op lateQt pc d = true) (hg : (singleNeeds it.op).map (·.2.2) = some tg)
    (hk : lateOk pc = true) (hr : ∀ r ∈ it.reads, r ∈ S) (hreq : it.req V = true)
    (hT : ∀ r ∈ T, r = d ∨ r ∈ S) (hH : ∀ p ∈ H, p.1 ≠ d) :
    SegQ kernel Assumptions.all L g (LQ Assumptions.all L g (LateR' L g)) pc
      (factsFrom S V ++ H) (pc + 1) (factsFrom T (it.upd V) ++ H) := by
  obtain ⟨⟨hc, hS, hR⟩, -⟩ := hat
  unfold singleOk at hs
  split at hs
  swap
  · cases hs
  rename_i nd hn
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hs
  obtain ⟨⟨⟨hl, hN⟩, hq⟩, hd⟩ := hs
  simp only [hn, Option.map_some, Option.some.injEq] at hg
  rw [hd, hg] at hq
  have hupd : it.upd V = Function.update V d x := by simp [XItem.upd, hv]
  have key : ∀ t, At t pc (factsFrom S V ++ H) → TypedF (lateQt pc) t → LateR' L g t →
      execLocalA Assumptions.all L g t it.op = .ok (PTX.next (setReg t d x)) ∧ tg.ok (some x) := by
    intro t ht hT' hR'
    obtain ⟨hpc, -, -, -, hregs⟩ := ht
    obtain ⟨y, hy, hdy⟩ := single_late hk it.op nd (OItem.instrB_eq hc) hn t hpc
      (typedF_of_needs hN hT') hR'
    rw [hd] at hy
    rw [hg] at hdy
    have hx := XItem.exec it (V := V) (t := t) (hpc ▸ hS) (hR t hpc) (fun r hr' =>
      holds_mem hregs (List.mem_append_left _ (mem_factsFrom (hr r hr')))) hreq
    have hcond : it.cond V := by
      by_contra hc'
      obtain ⟨f, hf⟩ := hx.2 hc'
      rw [hy] at hf
      cases hf
    have hpost : it.post V t = PTX.next (setReg t d x) := by simp [XItem.post, hv]
    rw [hx.1 hcond, hpost] at hy
    have := congrArg (fun s => s.regs d) (Except.ok.inj hy)
    simp [PTX.next, setReg] at this
    subst this
    exact ⟨hx.1 hcond |>.trans (by rw [hpost]), hdy⟩
  refine segQR_set (d := d) (tg := tg) (x := x) (OItem.instrB_eq hc) hl
    (fun t ht hT' hR' => (key t ht hT' hR').1) (fun t ht hT' hR' => (key t ht hT' hR').2) hq ?_
  intro p hp
  rcases List.mem_append.mp hp with h | h
  · obtain ⟨r, hr', rfl⟩ := List.mem_map.mp h
    by_cases hrd : r = d
    · subst hrd
      exact .inl (by simp [hupd])
    · refine .inr ⟨List.mem_append_left _ ?_, hrd⟩
      rcases hT r hr' with h' | h'
      · exact absurd h' hrd
      · simp only [hupd, Function.update_of_ne hrd]
        exact mem_factsFrom h'
  · exact .inr ⟨List.mem_append_right _ h, hH p h⟩

/-- The control facts of the next shuffle site. -/
noncomputable abbrev HC (e : Control.Entry) (L : Launch) (g : Nat) (i : Nat) (v : Control.Carry) :
    List (Nat × Value) :=
  factsFrom (Control.ctlLive 2234) (Control.valueOf e L g ⟨.shfl6, i, v⟩)

/-- The facts of the next shuffle site, after the exchange of the halves `av` and `x`. -/
noncomputable abbrev G5 (e : Control.Entry) (L : Launch) (g : Nat) (i : Nat) (v : Control.Carry)
    (w : Data.Vals) (av x : Value) : List (Nat × Value) :=
  Data.dF L ⟨⟨.shfl6, i, v⟩, {w with mx := Lib.mxWord w.m av x}⟩ ++ HC e L g i v

theorem hc_nmem {items : List XItem} (h : ∀ r ∈ Control.ctlLive 2234, r ∉ xWrites items) :
    ∀ p ∈ HC e L g i v, p.1 ∉ xWrites items := by
  intro p hp
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hp
  exact h r hr

theorem hc_ne {d : Nat} (h : ∀ r ∈ Control.ctlLive 2234, r ≠ d) :
    ∀ p ∈ HC e L g i v, p.1 ≠ d := by
  intro p hp
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hp
  exact h r hr

/-- **The new maximum, the test and the factor** (pcs 1839 to 1846) are exact. -/
theorem seg_alpha (av x : Value) :
    SegQ kernel Assumptions.all L g (LQ Assumptions.all L g (LateR' L g)) 1839
      (factsFrom [1520, 1521, 1914, 498] (Data.alphaV L w.m av x) ++ HC e L g i v) 1847
      (G5 e L g i v w av x) := by
  have hA : OAt kernel Assumptions.all L g 1839 (Lib.alphaItems.take 3 ++
      ((Lib.alphaItems.drop 3).take 1 ++ ((Lib.alphaItems.drop 4).take 1 ++
      Lib.alphaItems.drop 5))) := Lib.alpha_at
  have h1 := SegQF.of_items lateQt hA.left (by decide +kernel) (by decide +kernel)
    (V := Data.alphaV L w.m av x) (liveS := [1520, 1521, 1914, 498])
    (liveT := [498, 1914, 1522, 1523]) (H := HC e L g i v) (Data.req_alpha _)
    (by decide +kernel) (hc_nmem (by decide +kernel)) (by decide +kernel)
    (AbsSound.mono (absF5_sound (fp3_of (L := L) (g := g) (a := 1839) (b := 1842)
    (by decide +kernel))) (by decide +kernel) (by decide +kernel)) (by decide +kernel)
  have h2 := seg_single (tg := .dat32) (S := [498, 1914, 1522, 1523]) (T := [498, 1914, 1522, 1524])
    (H := HC e L g i v) (V := xFinal (Data.alphaV L w.m av x) (Lib.alphaItems.take 3))
    hA.right.left rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by simp [XItem.req, OItem.req])
    (by decide +kernel) (hc_ne (by decide +kernel))
  have h3 := seg_single (tg := .dat32) (S := [498, 1914, 1522, 1524]) (T := [498, 1914, 1522, 1270])
    (H := HC e L g i v) (V := xFinal (Data.alphaV L w.m av x) (Lib.alphaItems.take 4))
    hA.right.right.left rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by simp [XItem.req, OItem.req])
    (by decide +kernel) (hc_ne (by decide +kernel))
  have h4 := SegQF.of_items lateQt hA.right.right.right (by decide +kernel) (by decide +kernel)
    (V := xFinal (Data.alphaV L w.m av x) (Lib.alphaItems.take 5))
    (liveS := [498, 1914, 1522, 1270]) (liveT := [498, 1914, 1522, 168, 507])
    (H := HC e L g i v) (by simp [Lib.alphaItems, Lib.alphaRest, xReq, XItem.req, OItem.req,
      XItem.upd, XItem.vals, OItem.vals, isPred, isRegOrF32, fcmpBase, Function.update])
    (by decide +kernel) (hc_nmem (by decide +kernel)) (by decide +kernel)
    (AbsSound.mono (absF5_sound (fp3_of (L := L) (g := g) (a := 1844) (b := 1847)
    (by decide +kernel))) (by decide +kernel) (by decide +kernel)) (by decide +kernel)
  have hf := Data.alpha_facts (L := L) w.m av x
  have key := (((SegQ.tauAll _ h1).comp h2).comp h3).comp (SegQ.tauAll _ h4)
  have hG : G5 e L g i v w av x = factsFrom [498, 1914, 1522, 168, 507]
      (xFinal (Data.alphaV L w.m av x) Lib.alphaItems) ++ HC e L g i v :=
    congrArg (· ++ HC e L g i v) hf.symm
  rw [hG]
  exact key

theorem emu_nmem (av x : Value) : ∀ p ∈ G5 e L g i v w av x, ∀ k < 16,
    p.1 ∉ Lib.emuW (1913 + 11 * k) := fun p hp k hk h =>
  facts_nmem (wr := (List.range 16).flatMap fun k => Lib.emuW (1913 + 11 * k))
    (d := ⟨⟨.shfl6, i, v⟩, {w with mx := Lib.mxWord w.m av x}⟩)
    (by (try dsimp only); decide +kernel) (by decide +kernel) p hp
    (List.mem_flatMap.mpr ⟨k, List.mem_range.mpr hk, h⟩)

/-- **The span of the shuffle**: the exact run, the windows and the software `exp2`s. -/
theorem span5 (av x : Value) :
    SegQ kernel Assumptions.all L g (LQ Assumptions.all L g (LateR' L g)) 1839
      (factsFrom [1520, 1521, 1914, 498] (Data.alphaV L w.m av x) ++ HC e L g i v) 2234
      (G5 e L g i v w av x) := by
  refine SegQ.comp (b := 1847) (G := G5 e L g i v w av x) (seg_alpha av x) ?_
  refine SegQ.comp (b := 1913) (G := G5 e L g i v w av x) (by win lw_l05_1847) ?_
  refine SegQ.comp (b := 2089) (G := G5 e L g i v w av x) (seg_emus (fun _ h => h)
    (emu_nmem av x)) ?_
  refine SegQ.comp (b := 2207) (G := G5 e L g i v w av x) (by win lw_l05_2089) ?_
  refine SegQ.comp (b := 2215) (G := G5 e L g i v w av x) (by win lw_l05_2207) ?_
  refine SegQ.comp (b := 2223) (G := G5 e L g i v w av x) (by win lw_l05_2215) ?_
  refine SegQ.comp (b := 2231) (G := G5 e L g i v w av x) (by win lw_l05_2223) ?_
  refine SegQ.comp (b := 2234) (G := G5 e L g i v w av x) (by win lw_l05_2231) ?_
  exact SegQ.weaken fun _ h => h

theorem val_shfl5 (e : Control.Entry) (L : Launch) (g : Nat) (i : Nat) (v : Control.Carry) :
    Control.valueOf e L g ⟨.shfl6, i, v⟩ = Control.valueOf e L g ⟨.shfl5, i, v⟩ := rfl

/-- The facts of the shuffle site with the sent and the received word cover the span's start. -/
theorem start5 (av x : Value) : ∀ p ∈ factsFrom [1520, 1521, 1914, 498]
    (Data.alphaV L w.m av x) ++ HC e L g i v,
    p ∈ (1521, x) :: (1520, av) :: (Data.code e L g).facts ⟨⟨.shfl5, i, v⟩, w⟩ := by
  intro p hp
  rcases List.mem_append.mp hp with h | h
  · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
    · exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_right _
        (by simp [Data.dF, Data.dFS, Data.alphaV])))
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_right _
        (by simp [Data.dF, Data.dFS, Data.alphaV])))
  · refine List.mem_cons_of_mem _ (List.mem_cons_of_mem _ ?_)
    rw [HC, val_shfl5] at h
    exact ctl_in (w := w) (p := 1838) (q := 2234) .shfl5 (by decide +kernel)
      (by decide +kernel) p h

/-- **The shuffle that exchanges the row maximum** continues at the next shuffle. -/
theorem sstep_shfl5 (ev : Event) :
    (Data.code e L g).StepForQP (QTF lateQt) (TauAll kernel Assumptions.all L g (LateR' L g))
      LWf ⟨⟨.shfl5, i, v⟩, w⟩ ev := by
  intro t u ins hat hinv hc hQ hw hf hP
  have hr : ∀ q ∈ (Data.code e L g).facts ⟨⟨.shfl5, i, v⟩, w⟩, q.1 ≠ 1521 :=
    facts_ne (by dsimp only; decide +kernel) (by dsimp only; decide +kernel)
  have hbf : ∀ ev' : Event, LWf ev' → ev'.pc = (Data.code e L g).pc ⟨⟨.shfl5, i, v⟩, w⟩ →
      ∀ m av bv cv recv ok, ev'.kind = .shfl m av bv cv recv ok → Dat32 recv :=
    fun _ he hpc m av bv cv recv ok hk =>
      he.bfly (hpc ▸ (by change 1838 ∈ _; decide)) m av bv cv recv ok hk
  have e1 : (Data.code e L g).pc ⟨⟨.shfl5, i, v⟩, w⟩ = 1838 := by
    change Site.pc .shfl5 = 1838
    decide +kernel
  have e2 : (Data.code e L g).pc ⟨⟨.shfl6, i, v⟩, w⟩ = 2234 := by
    change Site.pc .shfl6 = 2234
    decide +kernel
  have hn : ∀ m av bv cv recv ok, Dat32 recv →
      (Data.code e L g).next ⟨⟨.shfl5, i, v⟩, w⟩ ⟨1838, .shfl m av bv cv recv ok⟩ =
        some (some ⟨⟨.shfl6, i, v⟩, {w with mx := Lib.mxWord w.m av recv}⟩) := by
    intro m av bv cv recv ok _
    simp [Data.code, Data.succ, Control.next, Data.record]
  have key := Code.shflSentFP (C := Data.code e L g) (qt := lateQt) (Wf := LWf)
    (P := TauAll kernel Assumptions.all L g (LateR' L g)) (d := ⟨⟨.shfl5, i, v⟩, w⟩)
    (f := fun av x => ⟨⟨.shfl6, i, v⟩, {w with mx := Lib.mxWord w.m av x}⟩) (r := 1521)
    (src := 1520) (tr := .dat32) (Pv := Dat32) Flow.code_1838
  refine key hr (by decide) (fun hf hk => hop_bfly hf hk) hbf (fun x hx => ⟨x, rfl, hx⟩) hn rfl rfl
    (by change afterF lateQt 1838 _ = true; decide +kernel) ?_ ev ins hat hinv hc hQ hw hf hP
  intro av x hx
  refine ⟨rfl, rfl, Control.body_inv hinv rfl rfl, ?_⟩
  rw [e1, e2]
  exact (SegQ.fromFacts (start5 av x) (span5 av x)).comp (SegQ.weaken
    fun _ hR => holds_of_forall fun p hp => holds_mem hR
      (swap_mem (ctl_out (w := {w with mx := Lib.mxWord w.m av x}) .shfl6
        (by decide +kernel) p hp)))
end PTX.Kernels.InklingRelDecode.Proof.Softmax.Strict
