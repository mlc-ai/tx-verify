-- SPDX-License-Identifier: Apache-2.0
-- domain: valid-rows
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Control.StrictSink
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.SegLib
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.StepKinds
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Gen.DataSites0
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.GenRules
public import Lemmas.Flow.NcLoadSel
public import Tactics.KernelRfl
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part002
import Lemmas.Flow.SegFrameSet

@[expose] public section

/-! # The strict step of the sink's load (pc 156)

The window after the event: the scaling run (pc 157, data registers), then the control code to the
site after the sink (`Control.sinkSegS`), which keeps the sink word's facts. -/

/-! # The strict step of a scalar `.nc` word load of warpgroup 0's data machine

`skW_ncv`: the sink's load. The machine follows only a 32-bit word that satisfies the window's
condition `Cd`; the successor's data are on the chain exactly when `succOk` says so. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data
open PTX PTX.Proof PTX.Flow PTX.Flow.Code PTX.Kernels.FlashMlaSparseDecodeH64

noncomputable section

variable {P : Params} {L : Launch} {g : Nat} {w : BitVec 64}

/-- The successor of a state on the chain, with the flag `succOk` says. -/
theorem next_ok {d : D} {c' : Control.D} {b' : Blk} (hna : d.c.site ≠ .arrS) (hok : d.ok = true)
    {e : Event} (hrec : record d.c e d.b = b') :
    dataNext L d c' e = ⟨c', b', d.hist, succOk d.c c'⟩ := by
  rw [dataNext_eq hna, hrec]
  simp [hok]

/-- **A scalar `.nc` word load** that follows only a 32-bit word satisfying `Cd`. -/
theorem skW_ncv {d : D} {c' : Control.D} {a : MemAccess} {r base wd pc pc' : Nat} {sp : Space}
    {mk : BitVec 64 → Blk} {e : Event} {Cd : BitVec 64 → Prop}
    (hOk : ∀ x bs, e.kind = .nc x bs → ∃ y, rebuild 3 bs = .ok (.bits 32 y) ∧ Cd y)
    (hp : d.c.site.pc = pc) (hp' : c'.site.pc = pc') (hna : d.c.site ≠ .arrS)
    (hc : kernel.code[d.c.site.pc]? = some ⟨none, .mem a⟩)
    (hru : a.rule = some .threadAccess) (hloc : a.locSpace? = some sp)
    (hb : a.addr.base = .reg base wd) (hk : a.kind = .load) (hsem : a.sem = .weak)
    (hnc : a.nc = true) (hr : a.regs = [r])
    (hel1 : Control.elems d.c.site = 1) (hok : d.ok = true)
    (hsucc : ∀ x bs, Control.succ P L g w d.c ⟨d.c.site.pc, .nc x bs⟩ = some (some c'))
    (hrec : ∀ x bs y, rebuild 3 bs = .ok (.bits 32 y) →
      record d.c ⟨d.c.site.pc, .nc x bs⟩ d.b = mk y)
    (he1 : d.c.el = 0 → c'.el = 0) (hel : d.c.el = 0 → c'.el < Control.elems c'.site)
    (hoff : ∀ q ∈ Control.facts P L g w d.c ++ wF (scX L) d.c.site d.b, q.1 ≠ r)
    (hseg : ∀ y, Cd y → ∃ n, Seg kernel Assumptions.all L g n (pc + 1)
      ((Control.facts P L g w d.c ++ wF (scX L) d.c.site d.b) ++ [(r, .bits 32 y)]) pc'
      ((code P L g w).facts ⟨c', mk y, d.hist, succOk d.c c'⟩)) :
    (code P L g w).StepFor d e := by
  classical
  let Ok : Event → Prop := fun e => ∀ x bs, e.kind = .nc x bs →
    ∃ y, rebuild 3 bs = .ok (.bits 32 y) ∧ Cd y
  suffices h : ((code P L g w).cut Ok).StepFor d e from
    @StepFor.of_cut _ _ _ _ (code P L g w) Ok d e h hOk
  intro t u ins hat hi hc' hf
  have he0 := el0_of_one hel1 hi
  have hn : ∀ x bs y, rebuild 3 bs = .ok (.bits 32 y) →
      ((code P L g w).cut Ok).next d ⟨d.c.site.pc, .nc x bs⟩ =
      if Cd y then some (some ⟨c', mk y, d.hist, succOk d.c c'⟩) else some none := by
    intro x bs y hv
    by_cases hcd : Cd y
    · have hO : Ok ⟨d.c.site.pc, .nc x bs⟩ := by
        intro x' bs' hk'
        obtain ⟨rfl, rfl⟩ : x = x' ∧ bs = bs' := by simpa using hk'
        exact ⟨y, hv, hcd⟩
      rw [cut_next _ _ hO]
      simp only [hcd, ↓reduceIte]
      show (Control.succ P L g w d.c _).map _ = _
      rw [hsucc x bs]
      show some (some (dataNext L d c' _)) = _
      rw [next_ok hna hok (hrec x bs y hv)]
    · have hO : ¬ Ok ⟨d.c.site.pc, .nc x bs⟩ := by
        intro h
        obtain ⟨y', hv', hc2⟩ := h x bs rfl
        rw [hv] at hv'
        have h2 : (Value.bits 32 y' : Value) = .bits 32 y := (Except.ok.inj hv').symm
        obtain ⟨-, h3⟩ := Value.bits.inj h2
        exact hcd (h3 ▸ hc2)
      rw [cut_next_not _ _ hO]
      simp only [hcd, ↓reduceIte]
  have hno : ∀ x bs, ¬ (∃ y, rebuild 3 bs = .ok (.bits 32 y) ∧ Cd y) →
      ((code P L g w).cut Ok).next d ⟨d.c.site.pc, .nc x bs⟩ = some none := by
    intro x bs h
    refine cut_next_not _ _ fun hO => h ?_
    exact hO x bs rfl
  refine (Code.step_loadNcSel (C := (code P L g w).cut Ok) (r := r)
    (nv := fun y => if Cd y then some (some ⟨c', mk y, d.hist, succOk d.c c'⟩) else some none)
    hc hru hloc hb hk hsem hnc hr (by exact he0) (by simp [Control.D.acc, he0]) hn ?_ ?_
    (fun y => by by_cases h : Cd y <;> simp [h]) (fun q hq => ?_) ?_).step ins hat hi hc' hf
  · intro x bs v hv hv32
    refine hno x bs fun h => ?_
    obtain ⟨y, hy, -⟩ := h
    rw [hv] at hy
    exact hv32 y (Except.ok.inj hy)
  · intro x bs f hv
    right
    exact hno x bs fun h => by obtain ⟨y, hy, -⟩ := h; rw [hv] at hy; cases hy
  · exact hoff q (by
      have := facts_ok (P := P) (L := L) (g := g) (w := w) hok
      exact this ▸ hq)
  · intro y d' hd
    by_cases hcd : Cd y
    · simp only [hcd, ↓reduceIte] at hd
      obtain rfl := Option.some.inj (Option.some.inj hd)
      refine ⟨fun _ => ?_, he1 he0, by simp [Control.D.acc, he1 he0], fun _ => hel he0⟩
      obtain ⟨n, h⟩ := hseg y hcd
      refine ⟨n, ?_⟩
      show Seg _ _ _ _ _ (d.c.site.pc + 1) _ c'.site.pc _
      rw [hp, hp']
      refine (h.weaken_start fun R hR => ?_)
      have hR' : Holds R ((r, Value.bits 32 y) :: ((code P L g w).facts d)) := hR
      rw [facts_ok hok] at hR'
      exact (holds_append _ _ _).mpr ⟨hR'.2, ⟨hR'.1, trivial⟩⟩
    · simp only [hcd, ↓reduceIte] at hd; cases hd

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data
open PTX PTX.Proof PTX.Flow PTX.Flow.Code PTX.Kernels.FlashMlaSparseDecodeH64

noncomputable section

/-- The sink's scaling run (pc 157), from the facts after the load to those before pc 158, framed
over the control facts. -/
theorem sinkRunS (L : Launch) (g : Nat) (x : BitVec 64) (sk v : Value)
    (Hc Hc' : List (Nat × Value)) (hk : Hc'.map Prod.fst = Control.ctlLive 158)
    (hsub : ∀ R, Holds R Hc → Holds R Hc')
    (c1 : Gen.sk_cond (lookupD (s_sink x sk v))) :
    ∃ n, Seg kernel Assumptions.all L g n 157 (Hc ++ s_sink x sk v) 158
      (Hc' ++ f_set x (Gen.sk_v157 fun _ => v)) := by
  have h467 : lookupD (s_sink x sk v) 467 = .bits 32 x := by
    simp [s_sink, f_set, lookupD]
  have h932 : lookupD (s_sink x sk v) 932 = v := by
    simp [s_sink, f_set, lookupD, List.lookup]
  refine windowS_close (SegD.frame (H := Hc') rulesFrame
    (SegD.frame (H := factsFrom [467] (lookupD (s_sink x sk v))) rulesFrame
      (Gen.sk_run L g (lookupD (s_sink x sk v))) rfl (by kernel_rfl) (by kernel_rfl)
      fun _ _ => w0SegFree _)
    rfl (by kernel_rfl) (by rw [hk]; kernel_rfl) fun _ _ => w0SegFree _) c1 ?_ hsub ?_
  · intro R h
    have h2 := windowS_snd h
    exact (holds_append _ _ _).mpr ⟨holds_lookupD (live := [932]) h2 (by kernel_rfl),
      holds_lookupD (live := [467]) h2 (by kernel_rfl)⟩
  · intro R h
    have h1 := ((holds_append _ _ _).mp h).1
    have h2 := ((holds_append _ _ _).mp h).2
    have hs : Gen.sk_v157 (lookupD (s_sink x sk v)) = Gen.sk_v157 fun _ => v := by
      simp only [Gen.sk_v157, h932]
    simp only [Gen.sk_facts1, factsFrom, h467, hs, List.map_cons, List.map_nil] at h1 h2 ⊢
    exact ⟨h2.1, h1.1, trivial⟩

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data
open PTX PTX.Proof PTX.Flow PTX.Flow.Code PTX.Kernels.FlashMlaSparseDecodeH64

noncomputable section

variable {P : Params} {L : Launch} {g : Nat} {w : BitVec 64} {m : Mem0}

/-- The window of the sink's load, from the facts after the event to the site after the sink. -/
theorem sinkWin (hp : Pre P L m) (d : Control.D) (hs : d.site = .sink) (x : BitVec 64)
    (sk v : Value)
    (c1 : Gen.sk_cond (lookupD (s_sink x sk v))) :
    ∃ n, Seg kernel Assumptions.all L g n 157 (Control.facts P L g w d ++ s_sink x sk v)
      ((Control.code P L g w).pc (Control.afterSink P L g w d))
      (Control.facts P L g w (Control.afterSink P L g w d) ++
        f_set x (Gen.sk_v157 fun _ => v)) := by
  obtain ⟨n1, h1⟩ := sinkRunS L g x sk v (Control.facts P L g w d)
    (factsFrom (Control.ctlLive 158) (Control.valueOf P L g w d)) factsFrom_keys
    (fun R h => by
      have hpc : d.site.pc = 156 := by rw [hs]; rfl
      unfold Control.facts at h
      rw [hpc] at h
      exact holds_factsFrom_mono h (by decide +kernel)) c1
  obtain ⟨n2, h2⟩ := Control.sinkSegS (P := P) (L := L) (g := g) (w := w) hp d
  have h3 := Seg.frameSet (H := f_set x (Gen.sk_v157 fun _ => v)) rulesFrame
    (S := [158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 170,
        171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 183, 184,
        185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196,
        197, 1836, 1837, 1838, 1839]) (by kernel_rfl) (fun _ _ => w0SegFree _) (by kernel_rfl) h2
  exact ⟨n1 + n2, Seg.comp h1 h3⟩

/-- The strict step at pc 156. -/
theorem sk_156 (hp : Pre P L m) (d : D) (hs : d.c.site = .sink) (hok : d.ok = true) (e : Event)
    (hcd : ∀ x bs, e.kind = .nc x bs → ∃ y, rebuild 3 bs = .ok (.bits 32 y) ∧
      Gen.sk_cond (lookupD (s_sink (scX L) d.b.sk (.bits 32 y)))) :
    (code P L g w).StepFor d e := by
  refine skW_ncv (pc := 156) (pc' := (Control.afterSink P L g w d.c).site.pc) (r := 932)
    (mk := fun y => { d.b with sk := Gen.sk_v157 fun _ => .bits 32 y })
    (Cd := fun y => Gen.sk_cond (lookupD (s_sink (scX L) d.b.sk (.bits 32 y))))
    hcd (by rw [hs]; rfl) rfl (c' := Control.afterSink P L g w d.c) (by rw [hs]; decide)
    (by rw [hs]; exact Flow.code_156) rfl rfl rfl rfl rfl rfl rfl (by rw [hs]; decide) hok
    (fun x bs => by simp [Control.succ, hs, Control.dataRd])
    (fun x bs y hv => by simp [record, hs, loadVal_ok hv])
    (fun h => by rw [Control.afterSink_el]; exact h)
    (fun h => by rw [Control.afterSink_el, h]; exact Control.elems_pos _) ?_ ?_
  · exact facts_fresh (by rw [hs]) (by decide +kernel) (fun q hq h => by
      rw [hs] at hq
      exact hoff_of (F := wF (scX L) .sink d.b) (ds := [932]) (by kernel_rfl) q hq (by simp [h]))
  · intro y c1
    obtain ⟨n, h⟩ := sinkWin (g := g) (w := w) hp d.c hs (scX L) d.b.sk (.bits 32 y) c1
    have e1 : wF (scX L) d.c.site d.b ++ [(932, Value.bits 32 y)] =
        s_sink (scX L) d.b.sk (.bits 32 y) := by rw [hs]; rfl
    rw [← e1, ← List.append_assoc] at h
    refine ⟨n, h.weaken_end fun R hR => ?_⟩
    have hR' := (holds_append _ _ _).mp hR
    show Holds R (Control.facts P L g w (Control.afterSink P L g w d.c) ++
      (if succOk d.c (Control.afterSink P L g w d.c) = true then
        wF (scX L) (Control.afterSink P L g w d.c).site
          { d.b with sk := Gen.sk_v157 fun _ => .bits 32 y } else []))
    by_cases hso : succOk d.c (Control.afterSink P L g w d.c) = true
    · simp only [hso, ↓reduceIte]
      have e2 : wF (scX L) (Control.afterSink P L g w d.c).site
          { d.b with sk := Gen.sk_v157 fun _ => .bits 32 y } =
          f_set (scX L) (Gen.sk_v157 fun _ => .bits 32 y) := by
        simp only [succOk, hs, decide_eq_true_eq, List.mem_cons, List.not_mem_nil, or_false] at hso
        rcases hso with h1 | h1 | h1 <;> (rw [h1]; rfl)
      rw [e2]
      exact hR
    · simp only [hso, Bool.false_eq_true, ↓reduceIte]
      exact (holds_append _ _ _).mpr ⟨hR'.1, trivial⟩

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data
