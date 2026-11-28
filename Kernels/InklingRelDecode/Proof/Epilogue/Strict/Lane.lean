-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Epilogue.Strict.Window
public import Kernels.InklingRelDecode.Proof.Iface.LateValues
public import Kernels.InklingRelDecode.Proof.Lib.BcastWord
public import Lemmas.Kernel.StrictQPRunEnd
import Kernels.InklingRelDecode.Proof.Epilogue.Strict.Live
public import Kernels.InklingRelDecode.Proof.Epilogue.Strict.SafeA
import Kernels.InklingRelDecode.Proof.Epilogue.Strict.SafeB
import Lemmas.Flow.GlueStep
import Kernels.InklingRelDecode.Proof.Common.ShuffleOrdinal
import Kernels.InklingRelDecode.Proof.Common.BcastIdx
import Lemmas.Kernel.FrameU
import Lemmas.Flow.UbStop

@[expose] public section

/-! # No undefined behaviour in the epilogue of a data lane

The first undefined-behaviour event of a data lane at a pc from 2565 on: the strict window starts
at the epilogue's first state (`EpiAt`), whose invariant is the tags the softmax's window left, and
runs to the event. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Epilogue.Strict
open PTX PTX.Proof PTX.Flow PTX.Flow.TyG
open PTX.Kernels.InklingRelDecode.Gen.TypedLateQt

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- **The window's states are closed under the machine's steps.** -/
theorem winE_next {d d' : (lateThread Q L g).D} {e : Event} (hd : OkE d)
    (hn : (lateThread Q L g).next d e = some (some d')) : OkE d' := by
  obtain ⟨w, ent, z, n, hok, rfl⟩ := hd
  obtain ⟨hn1, hn2⟩ := Code.counted_next_some hn
  obtain ⟨x', h1, hd1⟩ := Code.glue_inr_some hn1
  obtain ⟨x'', h2, rfl⟩ := Code.glue_inr_some (P := prologueDCode Q L g w)
    (R := fun e => lateSoftD e L g) (exit := fun d => dataExit Q L g w (prologueErase Q L g w d))
    h1
  obtain ⟨z1, h3, rfl⟩ := Code.glue_inr_some h2
  obtain ⟨dd, nn⟩ := d'
  dsimp only at hd1 hn2
  subst hd1
  exact ⟨w, ent, z1, nn, hok, rfl⟩

theorem epi_launch (hp : Pre Q L m) : EpiLaunch L :=
  ⟨by rw [hp.block], hp.sharedAlignment, by
    have := hp.sharedRange
    unfold sharedBytes at this
    omega⟩

/-- The event of the window at an epilogue state is no undefined behaviour. -/
theorem epi_safe (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hnames : ∀ n P w, (P = 1261 ∨ P = 2603) → Lib.ShflAt X g P n w →
      w = b32 (g % L.block / 32))
    {k pc : Nat} {f : Fault} (he : X.get (g, k) = some ⟨pc, .ub f⟩) {w : Value}
    {ent : Softmax.Control.Entry} {z : Epilogue.Control.D} {n : Cls → Nat} {t1 : TState}
    {o' : Option TState} (hs : Frame.stateAt (lateThread Q L) X g k = some (some (eSt w ent z n)))
    (hok : EntOkE ent) (hgd : (lateThread Q L g).Good (some (eSt w ent z n)) t1)
    (hq : QTF lateQt t1) (hes : EStep kernel Assumptions.all L g t1 ⟨pc, .ub f⟩ o') : False := by
  have hg := Frame.lt_of_get hX he
  have nu := Frame.noUbBefore_of_get hX he
  have hlenk : k < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  have hC : ∀ g < L.threads, (lateThread Q L g).SoundU := fun g hg => lateThread_sound hp hg
  obtain ⟨ins, hc, hfire⟩ := Code.fired_of_good (hC g hg) hgd hes
  have hu := fires_ub hfire (rfl : (⟨pc, .ub f⟩ : Event).kind = .ub f)
  by_cases hz : z.site = .exit
  · have hpc : (lateThread Q L g).pc (eSt w ent z n) = 2855 := by
      change z.site.pc = 2855
      rw [hz]; rfl
    rw [hpc, Flow.code_2855] at hc
    obtain rfl := Option.some.inj hc
    rw [hpc] at hfire
    simp [eventTmpl] at hu
  obtain ⟨hb0, hob, hlb⟩ := hok
  obtain ⟨ho, hl⟩ := epiEntry_bases hob hlb (g % L.block)
  have hx : z.site = .load → ∃ x, z.received = b32 x ∧ x % 4 = g % L.block / 32 % 4 := by
    intro hld
    have hst : Frame.stateAt (thread Q L) X g k = some (some (epiState w ent z n)) :=
      Frame.stateAt_map_some lateThread_stepMap hs
    have := (shfl_epi hp hX hlenk.le hst nu).2.1 hld
    exact ⟨_, hnames _ 2603 _ (Or.inr rfl) this, rfl⟩
  exact safe_epi (e := epiEntry ent (g % L.block)) (epi_launch hp) hb0 ho hl hgd.1 hq hz hx hc f hu


/-- **A data lane has no undefined behaviour at a pc of the epilogue.** -/
theorem noUb_epi_core (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (hv : Iface.LateValues L X) (lane : g % L.block < 128)
    {R : TState → Prop} (hRP : ∀ t, Frame.LaneAt kernel Assumptions.all L X g t → R t)
    (hR : RcpStep L g R)
    (hS : ∀ pc, epiS pc = true → SingleStep kernel Assumptions.all L g R pc)
    (hnames : ∀ n P w, (P = 1261 ∨ P = 2603) → Lib.ShflAt X g P n w →
      w = b32 (g % L.block / 32))
    {i k pc : Nat} {f : Fault} (hik : i ≤ k) (hat : EpiAt Q L X g i)
    (he : X.get (g, k) = some ⟨pc, .ub f⟩) : False := by
  obtain ⟨⟨w, ent, z, n, hs0, hb0, hob, hlb⟩, hstop, htyped⟩ := hat
  have hok : EntOkE ent := ⟨hb0, hob, hlb⟩
  have hg := Frame.lt_of_get hX he
  rcases Nat.eq_or_lt_of_le hik with rfl | hlt
  · obtain ⟨t0, t1, o', hrun, htau, hgd, hes⟩ := hstop _ _ hs0 he
    exact epi_safe hp hX hnames he hs0 hok hgd (htyped _ t0 t1 hs0 hrun htau hgd) hes
  have nu := Frame.noUbBefore_of_get hX he
  have hC : ∀ g < L.threads, (lateThread Q L g).SoundU := fun g hg => lateThread_sound hp hg
  have hkk : i + (k - i - 1 + 1) = k := by omega
  have hWf : ∀ i', i ≤ i' → i' < i + (k - i - 1 + 1) → ∀ ej, X.get (g, i') = some ej →
      WfE ej := by
    intro i' hi1 hi2 ej hev
    obtain ⟨pc', kd⟩ := ej
    refine ⟨?_, ?_⟩
    · intro hpc2 mode a b c recv ok hk
      obtain rfl : kd = .shfl mode a b c recv ok := hk
      obtain ⟨rfl, rfl, rfl⟩ := bcast_idx hp hX hf hev (Or.inr hpc2)
      exact ⟨_, hnames _ pc' _ (Or.inr hpc2) ⟨i', a, ok, hev, rfl⟩⟩
    · intro hpc2 a vals sh hk w hw
      obtain rfl : kd = .tc (.ld a vals sh) := hk
      have hmem : pc' ∈ Iface.tcLdPcs := by
        change pc' = 2607 at hpc2
        rw [hpc2]; decide
      exact hv.tcLd hev lane hmem w hw
  have hQ0 : ∀ t t1', Frame.LanePos kernel Assumptions.all L X g t ((X.tr g).drop i) →
      Relation.ReflTransGen (Tau kernel Assumptions.all L g) t t1' →
      (lateThread Q L g).Good (some (eSt w ent z n)) t1' → QTF lateQt t1' := by
    rintro t t1' ⟨k', t0', hr', hes', hl0⟩ hl hgd
    have hk' : k' = i := by
      have := congrArg List.length hes'
      have hlenk : k < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
      simp only [List.length_drop] at this
      omega
    subst hk'
    exact htyped _ t0' t1' hs0 hr' (hl0.trans hl) hgd
  have key := Frame.strictQPRun_end
    (C := lateThread Q L) (J := fun g σ => guardedTable Q L g (lateErase Q L g σ))
    (Q := QTF lateQt) (P := TauAll kernel Assumptions.all L g R) (Wf := WfE) (Ok := OkE) hC hX
    (fun k => lateFollowed hf hg k)
    (fun t ⟨k, t0, hr, ht⟩ v hvt => hRP v ⟨k, t0, hr, ht.trans hvt⟩)
    (fun d e hd => winE_step hR hS d e hd) (fun d e d' hd _ _ hn => winE_next hd hn)
    (k0 := i) (m := k - i - 1) hs0 ⟨w, ent, z, n, hok, rfl⟩ hQ0 (e := ⟨pc, .ub f⟩)
    (by rw [hkk]; exact he) hWf ?live
  · obtain ⟨σ, hs, hok', t0, t1, o', -, -, hgd, hq, hes⟩ := key
    obtain ⟨w', ent', z', n', hok'', rfl⟩ := hok'
    rw [hkk] at hs
    exact epi_safe hp hX hnames he hs hok'' hgd hq hes
  · intro i' d v hi1 hi2 hok' hv' hd hJ nui hn
    have hu : ∀ f, v.kind ≠ .ub f := fun f => nui i' (by omega) v hv' f
    obtain ⟨t, ins, o', hat', hinv, hc, hfi⟩ := Frame.fired_siteU hC hX hv' hd hu
    obtain ⟨w', ent', z', n', hok'', rfl⟩ := hok'
    by_cases hz : z'.site = .exit
    · have hpc : (lateThread Q L g).pc (eSt w' ent' z' n') = 2855 := by
        change z'.site.pc = 2855
        rw [hz]; rfl
      rw [hpc, Flow.code_2855] at hc
      obtain rfl := Option.some.inj hc
      rw [hpc] at hfi
      obtain ⟨h1, -⟩ := hfi
      rw [h1]
    · exfalso
      have hs' : Epilogue.Control.next (epiEntry ent' (g % L.block)) L g z' v = none := by
        rcases h : Epilogue.Control.next (epiEntry ent' (g % L.block)) L g z' v with _ | _ | c
        · rfl
        · simp [lateThread, Code.roleThread, Code.counted, Code.glue, Code.withStubs, lateFrag,
            lateDataD, lateSoftD, epilogueDCode, h] at hn
        · simp [lateThread, Code.roleThread, Code.counted, Code.glue, Code.withStubs, lateFrag,
            lateDataD, lateSoftD, epilogueDCode, h] at hn
      exact live_epi (e := epiEntry ent' (g % L.block)) hz hc hfi hu hs'

end
end PTX.Kernels.InklingRelDecode.Proof.Epilogue.Strict
