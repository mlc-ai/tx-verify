-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Softmax.Data.Phase
public import Kernels.InklingRelDecode.Proof.Softmax.Data.Cross
import Kernels.InklingRelDecode.Proof.Lib.Segments
import Kernels.InklingRelDecode.Flow.Code

@[expose] public section

/-! # The first facts of the softmax: the scale word and the running maximum

From the barrier of pc 575 the thread runs to the bias preloads or the loop. On the way pc 601
computes the scale word (register 498) from the scale parameter (register 525) and pc 945 sets the
running maximum to `-inf`. The facts are given by position, the control machine names the stop. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
open PTX PTX.Proof PTX.Flow PTX.Flow.Code PTX.Assumption Control

set_option maxRecDepth 100000
noncomputable section
variable {e : Entry} {L : Launch} {g : Nat}

/-- No assumption has a local rule for a `mov.b32` of a literal outside the float sites. -/
theorem move_none {t : TState} (h1 : t.pc ≠ 2562) (h2 : t.pc ≠ 600) (h3 : t.pc ≠ 807)
    (m : MoveInstr) : ∀ a ∈ Assumptions.all, a.localRule L g t (.move m) = none := by
  intro a ha
  by_cases hd : a ∈ Assumptions.all.drop 2
  · exact Lib.other_rules_none h1 h2 h3 (t := t) (op := .move m) (fun c hc => nomatch hc) a hd
  · simp only [Assumptions.all, List.mem_cons, List.not_mem_nil, or_false, List.drop_succ_cons,
      List.drop_zero] at ha hd
    rcases ha with rfl | rfl | ha'
    · exact idealReal_localRule_none fun f hf => by simp [FloatForm.ofOp] at hf
    · exact approxExact_localRule_none fun f hf => by simp [ApproxForm.ofOp] at hf
    · exact absurd ha' hd

/-- The running maximum's start at pc 945. -/
theorem init_at : OAt kernel Assumptions.all L g 945 [.base (.movImm 1914 4286578688)] :=
  ⟨⟨by decide +kernel, Kernels.InklingRelDecode.Proof.segFree (by decide +kernel),
    fun s hs => move_none (L := L) (g := g) (t := s) (by omega) (by omega) (by omega) _⟩, trivial⟩

/-- The positions that follow the writes of pcs 601 and 945 hold their facts. -/
def iniKeys (pc : Nat) : List Nat :=
  if pc ≤ 601 then [525] else if pc ≤ 945 then [525, 498] else if pc ≤ 948 then [525, 498, 1914]
  else if pc ≤ 999 then [525, 498] else [525, 498, 1914]

def iniSpec (pc : Nat) : Bool := decide (pc = 601 ∨ pc = 945)

/-- The values: the parameter, the scale word and `-inf`. -/
def iniV (L : Launch) (r : Nat) : Value :=
  if r = 498 then scaleW L else if r = 1914 then b32 4286578688 else scaleVal L

/-- The scale word as one step. -/
theorem scale_segd :
    SegD kernel Assumptions.all L g 1 601 (factsFrom [525] (iniV L)) 602
      (factsFrom [525, 498] (xFinal (iniV L) [Lib.scaleItem])) (xCond (iniV L) [Lib.scaleItem]) :=
  SegD.xouts (K := kernel) (A := Assumptions.all) (L := L) (g := g) (items := [Lib.scaleItem])
    (liveS := [525]) (liveT := [525, 498]) (V := iniV L) (Lib.scale_at (L := L) (g := g)).code
    (by decide +kernel) (by simp [xReq, XItem.req, Lib.scaleItem]) (by decide +kernel)
    (Lib.scale_at (L := L) (g := g)).rules (by decide +kernel)

/-- The running maximum's start as one step. -/
theorem init_segd :
    SegD kernel Assumptions.all L g 1 945 (factsFrom [525, 498] (iniV L)) 946
      (factsFrom [525, 498, 1914] (xFinal (iniV L) [.base (.movImm 1914 4286578688)]))
      (xCond (iniV L) [.base (.movImm 1914 4286578688)]) :=
  SegD.xouts (K := kernel) (A := Assumptions.all) (L := L) (g := g)
    (items := [.base (.movImm 1914 4286578688)]) (liveS := [525, 498]) (liveT := [525, 498, 1914])
    (V := iniV L) (init_at (L := L) (g := g)).code (by decide +kernel)
    (by simp [xReq, XItem.req, OItem.req]) (by decide +kernel)
    (init_at (L := L) (g := g)).rules (by decide +kernel)

theorem scale_vals (r : Nat) (hr : r = 525 ∨ r = 498) :
    xFinal (iniV L) [Lib.scaleItem] r = iniV L r := by
  rcases hr with rfl | rfl
  · exact Lib.xFinal_other (by decide)
  · have : xFinal (iniV L) [Lib.scaleItem] 498 = Lib.scaleWord (scaleVal L) :=
      Lib.xFinal_congr (S := [525]) (items := [Lib.scaleItem]) (by decide)
        (fun r hr => by simp at hr; subst hr; simp [iniV]) 498
        (Or.inl (by simp [xWrites, XItem.writes, Lib.scaleItem]))
    rw [this]
    simp [iniV, scaleW]

theorem init_vals (r : Nat) (hr : r = 525 ∨ r = 498 ∨ r = 1914) :
    xFinal (iniV L) [.base (.movImm 1914 4286578688)] r = iniV L r := by
  rcases hr with rfl | rfl | rfl
  · exact Lib.xFinal_other (by decide)
  · exact Lib.xFinal_other (by decide)
  · simp [xFinal, XItem.upd, XItem.vals, OItem.vals, Function.update, iniV, b32]

theorem ini_spec {ivs : List (Nat × Nat)} (h602 : inIvs ivs 601 = true → inIvs ivs 602 = true)
    (h946 : inIvs ivs 945 = true → inIvs ivs 946 = true) :
    ∀ pc, iniSpec pc = true → inIvs ivs pc = true → ∀ t t1 : TState, t.pc = pc →
      TabAt iniKeys (fun _ => false) (iniV L) (iniV L) t → Tau kernel Assumptions.all L g t t1 →
      ((inIvs ivs t1.pc || evAtB kernel t1.pc) = true ∧
        TabAt iniKeys (fun _ => false) (iniV L) (iniV L) t1) ∨
        Machine.Dead (K := kernel) (A := Assumptions.all) (L := L) (g := g) t1 := by
  intro pc hsp hin t t1 hpc hT ht1
  obtain ⟨hsub, hacc, hH⟩ := hT
  have hfault : t.fault = none := by
    unfold Tau out at ht1
    cases hf : t.fault with
    | none => rfl
    | some f => rw [hf] at ht1; cases ht1
  simp only [iniSpec, decide_eq_true_eq] at hsp
  rcases hsp with rfl | rfl
  · have hF : Holds t.regs (factsFrom [525] (iniV L)) := by
      rw [hpc] at hH
      simpa [phi, iniKeys] using hH
    rcases SegD.tau_one (scale_segd (L := L) (g := g)) ⟨hpc, hsub, hacc, hfault, hF⟩ ht1 with
      hu | hd
    · refine .inl ⟨by rw [hu.1]; simp [h602 (hpc ▸ hin)], hu.2.1, hu.2.2.1, ?_⟩
      have hp : t1.pc = 602 := hu.1
      have hk : iniKeys t1.pc = [525, 498] := by rw [hp]; rfl
      refine holds_of_pointwise fun r hr => ?_
      rw [hk] at hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      show t1.regs r = some (iniV L r)
      rw [← scale_vals r (by omega)]
      obtain ⟨-, -, -, -, hur⟩ := id hu
      exact holds_mem hur (mem_factsFrom (by simp; omega))
    · exact .inr hd
  · have hF : Holds t.regs (factsFrom [525, 498] (iniV L)) := by
      rw [hpc] at hH
      simpa [phi, iniKeys] using hH
    rcases SegD.tau_one (init_segd (L := L) (g := g)) ⟨hpc, hsub, hacc, hfault, hF⟩ ht1 with
      hu | hd
    · refine .inl ⟨by rw [hu.1]; simp [h946 (hpc ▸ hin)], hu.2.1, hu.2.2.1, ?_⟩
      have hp : t1.pc = 946 := hu.1
      have hk : iniKeys t1.pc = [525, 498, 1914] := by rw [hp]; rfl
      refine holds_of_pointwise fun r hr => ?_
      rw [hk] at hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      show t1.regs r = some (iniV L r)
      rw [← init_vals r (by omega)]
      obtain ⟨-, -, -, -, hur⟩ := id hu
      exact holds_mem hur (mem_factsFrom (by simp; omega))
    · exact .inr hd

/-- The facts a stop after the first code holds, from the table's at its position. -/
theorem conv_ini {d' : D}
    (hd : d'.c.site = .pre 0 ∨ d'.c.site = .nxt 0 ∨ d'.c.site = .waitS ∨ d'.c.site = .epilogue)
    (hm : d'.c.site ≠ .pre 0 → d'.v.m = b32 4286578688) {R : Nat → Option Value}
    (h : Holds R (phi iniKeys (fun _ => false) (iniV L) (iniV L) d'.c.site.pc)) :
    Holds R (dF L d') := by
  have key : ∀ r, r ∈ iniKeys d'.c.site.pc → r = 525 ∨ r = 498 ∨ r = 1914 → R r = some (iniV L r) :=
    fun r hr _ => holds_mem h (mem_factsFrom (val := iniV L) hr)
  have loop : (d'.c.site = .nxt 0 ∨ d'.c.site = .waitS) → Holds R (dF L d') := by
    intro h1
    have hm1 := hm (by rcases h1 with h | h <;> rw [h] <;> decide)
    have hdF : dF L d' = [(498, scaleW L), (1914, d'.v.m)] := by
      rcases h1 with h | h <;> simp [dF, dFS, inRound, h]
    have hk : ∀ r, r = 498 ∨ r = 1914 → R r = some (iniV L r) := fun r hr =>
      key r (by rcases h1 with h | h <;> rw [h] <;> rcases hr with rfl | rfl <;> decide) (by omega)
    rw [hdF, hm1]
    exact ⟨(hk 498 (by simp)).trans (by simp [iniV]), (hk 1914 (by simp)).trans (by simp [iniV]),
      trivial⟩
  rcases hd with h1 | h1 | h1 | h1
  · simp only [dF, dFS, h1]
    refine holds_of_mem fun r x hm' => ?_
    simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hm'
    rcases hm' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact key 525 (by rw [h1]; decide) (by simp) |>.trans (by simp [iniV, scaleVal])
    · exact key 498 (by rw [h1]; decide) (by simp) |>.trans (by simp [iniV])
  · exact loop (.inl h1)
  · exact loop (.inr h1)
  · simp only [dF, dFS, h1]
    trivial

theorem loopSite_mem (e : Entry) (t i : Nat) :
    loopSite e t i = .nxt 0 ∨ loopSite e t i = .waitS ∨ loopSite e t i = .epilogue := by
  unfold loopSite
  split_ifs <;> simp

theorem data_bar0 {d : D} (hs : d.c.site = .bar0) : DataStep (code e L g) (dF L) d := by
  have pc : (code e L g).pc d = 575 := by
    change d.c.site.pc = 575
    rw [hs]
    rfl
  intro t ev u d' ins hat hi hc' hf hn
  rw [pc] at hc' hf
  rw [Flow.code_bar_19] at hc'
  obtain rfl := Option.some.inj hc'
  obtain rfl := Option.some.inj hf.2
  have hn' := hn
  obtain ⟨c', hnc, rfl⟩ := succ_inv hn
  simp only [Control.next, hs, Option.some.injEq] at hnc
  subst hnc
  have hreg : Holds t.regs (dFS L d.c.site d.v) := atD_dF hat
  have hpc : (PTX.next t).pc = 576 := by
    have h1 := hat.1
    simp only [PTX.next]
    omega
  have hT : TabAt iniKeys (fun _ => false) (iniV L) (iniV L) (PTX.next t) := by
    refine ⟨hat.2.1.trans rfl, hat.2.2.1.trans rfl, ?_⟩
    rw [hpc]
    rw [hs] at hreg
    refine holds_of_pointwise fun r hr => ?_
    have hk : iniKeys 576 = [525] := rfl
    rw [hk] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr
    exact holds_mem hreg (by simp [dFS, entryFact, iniV, scaleVal])
  refine goal_tab (ivs := [(576, 423), (1049, 208), (2560, 5)]) (by decide +kernel)
    (hseg_ivs (by decide +kernel))
    (ini_spec (fun _ => by decide +kernel) (fun _ => by decide +kernel))
    (by rw [hpc]; decide +kernel) hT (q := _) (stops_pc hat hi (by rw [pc]; exact Flow.code_bar_19)
      (by rw [pc]; exact hf) hn') (fun R h => conv_ini ?_ ?_ h)
  · by_cases hp : preEnabled e (g % L.block) = true
    · simp [hp]
    · simp only [hp, Bool.false_eq_true, ↓reduceIte, loopSite]
      split_ifs <;> simp
  · intro hne
    by_cases hp : preEnabled e (g % L.block) = true
    · simp [hp] at hne
    · simp only [hp, Bool.false_eq_true, ↓reduceIte, loopSite] at hne ⊢
      simp only [record, hs]
      split_ifs at hne ⊢ <;> simp_all

theorem data_pre63 {d : D} (hs : d.c.site = .pre 63) : DataStep (code e L g) (dF L) d := by
  have pc : (code e L g).pc d = 806 := by
    change d.c.site.pc = 806
    rw [hs]
    rfl
  intro t ev u d' ins hat hi hc' hf hn
  rw [pc] at hc' hf
  have hc0 := hc'
  rw [Flow.code_806] at hc'
  obtain rfl := Option.some.inj hc'
  obtain ⟨x, bs, rfl, rfl⟩ := fires_load (a := _) rfl rfl hf
  have hn' := hn
  obtain ⟨c', hnc, rfl⟩ := succ_inv hn
  simp only [Control.next, hs, Option.some.injEq] at hnc
  subst hnc
  have hsub : t.sub = 0 := hat.2.1.trans rfl
  cases hv : rebuild 3 bs with
  | error f => exact .inr (Machine.dead_of_fault (f := f) (by simp [afterLoad, hv]))
  | ok v =>
    have hu : afterLoad t [326] bs =
        { setRegs t [326] (t.acc ++ [v]) with pc := t.pc + 1, sub := 0, acc := [] } := by
      simp [afterLoad, hv, hsub]
    simp only [MemAccess.regs] at hf ⊢
    have hl : List.filterMap id [some 326] = [326] := rfl
    rw [hl] at hf ⊢
    rw [hu] at hf ⊢
    have hreg : Holds t.regs (dFS L d.c.site d.v) := atD_dF hat
    have hpc : t.pc + 1 = 807 := by
      have h1 := hat.1
      omega
    have hT : TabAt iniKeys (fun _ => false) (iniV L) (iniV L)
        { setRegs t [326] (t.acc ++ [v]) with pc := t.pc + 1, sub := 0, acc := [] } := by
      refine ⟨rfl, rfl, ?_⟩
      show Holds _ (phi iniKeys (fun _ => false) (iniV L) (iniV L) (t.pc + 1))
      rw [hpc]
      rw [hs] at hreg
      refine holds_of_pointwise fun r hr => ?_
      have hk : iniKeys 807 = [525, 498] := rfl
      rw [hk] at hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      show (setRegs t [326] (t.acc ++ [v])).regs r = some (iniV L r)
      rw [EventFrame.setRegs_regs_of_not_mem (by simp; omega)]
      rcases hr with rfl | rfl
      · exact holds_mem hreg (by simp [dFS, entryFact, iniV, scaleVal])
      · exact holds_mem hreg (by simp [dFS, iniV])
    refine goal_tab (ivs := [(806, 193), (1049, 208), (2560, 5)]) (by decide +kernel)
      (hseg_ivs (by decide +kernel))
      (ini_spec (fun h => by revert h; decide +kernel) (fun h => by revert h; decide +kernel))
      (by show (inIvs _ (t.pc + 1) || evAtB kernel (t.pc + 1)) = true
          rw [hpc]; decide +kernel) hT (q := _)
      (stops_pc hat hi (by rw [pc]; exact hc0) (by rw [pc]; exact hf) hn')
      (fun R h => conv_ini ?_ ?_ h)
    · exact .inr (loopSite_mem _ _ _)
    · intro _
      simp only [record, hs]
      rcases loopSite_mem e (g % L.block) d.c.i with h | h | h <;> simp [h, loopB]

end
end PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
