-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Softmax.Data.Machine
public import Kernels.InklingRelDecode.Proof.Lib.RulesFrame
public import Kernels.InklingRelDecode.Proof.Lib.Segments
public import Lemmas.Flow.DataFrameAny
public import Lemmas.Flow.FrameScan

@[expose] public section

/-! # The data step at a site whose continuation keeps the successor's facts

`dstep_site`: one control site, one successor site, no change of the words. The event writes
none of the successor's data registers and the code up to the next event (a frame set) writes
none. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
open PTX PTX.Proof PTX.Flow PTX.Flow.Code PTX.EventFrame Control

noncomputable section

/-- The registers of the data facts of a site. -/
def dKeys (s : Site) : List Nat :=
  match s with
  | .setMaxReg | .bar0 => [525]
  | .pre _ => [525, 498]
  | .epilogue => []
  | .waitLdO => (Gen.rs_facts0 fun _ => b32 0).map Prod.fst
  | .bar24 | .stO => (Gen.rs_facts2 fun _ => b32 0).map Prod.fst
  | s => [498, 1914] ++ if inRound s then [1522, 168, 507] else []

theorem dFS_keys (L : Launch) (s : Site) (v : Vals) : (dFS L s v).map Prod.fst = dKeys s := by
  cases s <;> rfl

theorem succ_inv {e : Entry} {L : Launch} {g : Nat} {d d' : D} {ev : Event}
    (h : succ e L g d ev = some (some d')) :
    ∃ c', Control.next e L g d.c ev = some (some c') ∧ d' = ⟨c', record L d ev c'.site⟩ := by
  unfold succ at h
  cases hn : Control.next e L g d.c ev with
  | none => rw [hn] at h; cases h
  | some o =>
    cases o with
    | none => rw [hn] at h; cases h
    | some c => rw [hn] at h; exact ⟨c, rfl, (Option.some.inj (Option.some.inj h)).symm⟩

/-- The sites whose events change a word of the data facts (or, for the preloads, may). -/
def plainB : Site → Bool
  | .shfl5 | .shfl6 | .shfl12 | .waitStO | .ldO | .bar0 | .pre _ => false
  | _ => true

/-- The words of the data facts do not change at an event of a plain site. -/
theorem record_main {L : Launch} {d : D} (ev : Event) (z : Site) (h : plainB d.c.site = true) :
    (record L d ev z).main d.v := by
  unfold record
  split <;> simp_all [Vals.main, plainB] <;> split <;> simp

/-- The running maximum does not change at the other sites' events. -/
theorem record_m {L : Launch} {d : D} (ev : Event) (z : Site) (h6 : d.c.site ≠ .shfl6)
    (h12 : d.c.site ≠ .shfl12) (hw : d.c.site ≠ .waitStO) (h0 : d.c.site ≠ .bar0)
    (hp : ∀ j, d.c.site ≠ .pre j) : (record L d ev z).m = d.v.m := by
  unfold record
  split <;> simp_all <;> split <;> simp

/-- ... nor at a preload that does not leave the preloads. -/
theorem record_main_pre {L : Launch} {d : D} (ev : Event) (z : Site) (j : Fin 64)
    (h : d.c.site = .pre j) (hz : ¬loopB z) : (record L d ev z).main d.v := by
  unfold record
  split <;> simp_all [Vals.main, loopB]

theorem facts_dF {e : Entry} {L : Launch} {g : Nat} {d : D} :
    ∀ R, Holds R ((code e L g).facts d) → Holds R (dF L d) := fun _ h =>
  ((holds_append _ _ _).mp h).2

/-- A concrete state of a value state holds its data facts. -/
theorem atD_dF {e : Entry} {L : Launch} {g : Nat} {d : D} {t : TState}
    (hat : (code e L g).AtD d t) : Holds t.regs (dFS L d.c.site d.v) := by
  obtain ⟨-, -, -, -, h⟩ := hat
  exact ((holds_append _ _ _).mp h).2

/-- A concrete state of a value state is one of its control state. -/
theorem atD_ctl {e : Entry} {L : Launch} {g : Nat} {d : D} {t : TState}
    (hat : (code e L g).AtD d t) : (Control.code e L g).AtD d.c t := by
  obtain ⟨a, b, c, f, h⟩ := hat
  exact ⟨a, b, c, f, ((holds_append _ _ _).mp h).1⟩

/-- The Boolean checks of a frame site: no software `exp2` in the continuation, the event and
its continuation, the event's writes and the frame set, for the registers of every successor. -/
def siteOk (s : Site) (zs : List Site) (ivs : List (Nat × Nat)) : Bool :=
  !Assumptions.emuSites.contains s.pc &&
  (inIvs ivs s.pc || evAtB kernel s.pc) && (inIvs ivs (s.pc + 1) || evAtB kernel (s.pc + 1)) &&
  (match kernel.code[s.pc]? with
    | some ins => (zs.flatMap dKeys).all (fun r => !(eventWrites ins.op).contains r)
    | none => true)

/-- The checks that depend on the intervals and the registers only. -/
def ivsOk (ivs : List (Nat × Nat)) (keys : List Nat) : Bool :=
  ((pcsOf ivs).all fun pc => !Assumptions.emuSites.contains pc) && scanOk kernel ivs keys

/-- **The data step of a site that keeps the facts of its successors.** -/
theorem dstep_site {e : Entry} {L : Launch} {g : Nat} {d : D} {s : Site} {zs : List Site}
    (hs : d.c.site = s) (ivs : List (Nat × Nat)) (hok : siteOk s zs ivs = true)
    (hivs : ivsOk ivs (zs.flatMap dKeys) = true)
    (hz : ∀ ev c', Control.next e L g d.c ev = some (some c') → c'.site ∈ zs)
    (hv : ∀ ev, ∀ z ∈ zs, (record L d ev z).main d.v)
    (hsub : ∀ v, ∀ z ∈ zs, ∀ x ∈ dFS L z v, x ∈ dFS L s v) :
    Code.DataStep (code e L g) (dF L) d := by
  simp only [siteOk, Bool.and_eq_true, Bool.not_eq_true'] at hok
  simp only [ivsOk, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true'] at hivs
  obtain ⟨⟨⟨hs0, hp0⟩, hp1⟩, hev⟩ := hok
  obtain ⟨hS, hB⟩ := hivs
  have key : ∀ ev d', succ e L g d ev = some (some d') →
      d'.c.site ∈ zs ∧ d'.v.main d.v := by
    intro ev d' h
    obtain ⟨c', hn, rfl⟩ := succ_inv h
    have := hz ev c' hn
    exact ⟨this, hv ev _ this⟩
  have hdF : ∀ ev d', succ e L g d ev = some (some d') →
      dF L d' = dFS L d'.c.site d.v := by
    intro ev d' h
    exact dFS_congr L _ (key ev d' h).2
  have pc : (code e L g).pc d = s.pc := by
    change d.c.site.pc = s.pc
    rw [hs]
  have hB' := frameSetG_of_scan hB
  apply Code.DataStep.frameAny (C' := code e L g) (dF := dF L) (d := d) (S := pcsOf ivs)
    Lib.rulesFrame
    (fun pc hpc => Kernels.InklingRelDecode.Proof.segFree (by simpa using hS pc hpc))
    (by rw [pc]; exact Kernels.InklingRelDecode.Proof.segFree (by simpa using hs0))
    (by rw [pc, pcsOf_contains]; exact hp0)
    (by rw [pc, pcsOf_contains]; exact hp1) facts_dF
  · intro ins hi ev d' h
    rw [hdF ev d' h, dFS_keys]
    rw [pc] at hi
    rw [hi] at hev
    simp only [List.all_eq_true, Bool.not_eq_true', List.mem_flatMap] at hev ⊢
    exact fun r hr => hev r ⟨_, (key ev d' h).1, hr⟩
  · intro ev d' h
    rw [hdF ev d' h, dFS_keys]
    refine frameSetG_mono hB' ?_
    intro r hr
    exact List.mem_flatMap.mpr ⟨_, (key ev d' h).1, hr⟩
  · intro ev d' h x hx
    rw [hdF ev d' h] at hx
    change x ∈ dFS L d.c.site d.v
    rw [hs]
    exact hsub _ _ (key ev d' h).1 x hx

end
end PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
