-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Softmax.Strict.Adv
public import Kernels.InklingRelDecode.Proof.Softmax.Steps.Rescale
public import Kernels.InklingRelDecode.Proof.Softmax.Steps.Butterfly
public import Lemmas.Flow.SegQFX
public import Lemmas.Flow.StepsQFOp
public import Lemmas.Flow.TypedDeclI
import Lemmas.Flow.TypedFloatH
import Kernels.InklingRelDecode.Proof.Lib.ShuffleOperand
import Lemmas.Isa.Tmpl
import Kernels.InklingRelDecode.Flow.Code.Part035
import Kernels.InklingRelDecode.Flow.Code.Part034

@[expose] public section

/-! # The strict steps of the row reductions' shuffles: the minimum after a butterfly

The minimum of the operand a butterfly sent and the word it received is an exact piece: its result
is the fact `Lib.minWord` of the two words, a datum. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Strict
open PTX PTX.Proof PTX.Flow PTX.Flow.TyG PTX.Flow.Havoc PTX.Assumption
open PTX.Kernels.InklingRelDecode.Gen.TypedLateQt

set_option maxRecDepth 100000

variable {L : Launch} {g : Nat}

/-- **The minimum of two registers of data** is a strict segment: its facts hold the minimum. -/
theorem segQ_minE {R : TState → Prop} {pc dm src dst : Nat} {a w : Value}
    {F G : List (Nat × Value)}
    (hc : kernel.code[pc]? = some ⟨none, MinCore.minOp dm [src, dst]⟩)
    (emu : Assumptions.emuSites.contains pc = false) (h1 : pc ≠ 2562) (h2 : pc ≠ 600)
    (h3 : pc ≠ 807) (hsa : (src, a) ∈ F) (hsb : (dst, w) ∈ F)
    (ha : (lateQt pc).lookup src = some .dat32) (hb : (lateQt pc).lookup dst = some .dat32)
    (hq : afterF lateQt pc [(dm, .dat32)] = true)
    (hG : ∀ p ∈ G, p = (dm, Lib.minWord a w) ∨ (p ∈ F ∧ p.1 ≠ dm)) :
    SegQ kernel Assumptions.all L g
      (fun t => QTF lateQt t ∧ TauAll kernel Assumptions.all L g R t) pc F (pc + 1) G := by
  refine SegQ.local1x hc rfl fun t ht ⟨hQ, hT⟩ => ?_
  have hty : TypedF (lateQt pc) t := by simpa [QTF, ht.1] using hQ
  obtain ⟨xa, hxa, hda⟩ := hty src _ ha
  obtain ⟨xb, hxb, hdb⟩ := hty dst _ hb
  obtain ⟨-, -, -, -, hreg⟩ := id ht
  have ra := holds_mem hreg hsa
  have rb := holds_mem hreg hsb
  obtain rfl := Option.some.inj (hxa.symm.trans ra)
  obtain rfl := Option.some.inj (hxb.symm.trans rb)
  obtain ⟨x, hm, hdx⟩ := PTX.Flow.TyG.minE_total hda hdb
  have hex := Control.min_at (L := L) (g := g) (t := t) (dm := dm) ht.1 emu h1 h2 h3 ra rb
  rw [hm] at hex
  obtain ⟨hw1, hw2⟩ := wr1 (t := t) (d := dm) (tg := .dat32) ⟨x, rfl, hdx⟩
  refine ⟨_, hex, by simp [PTX.next, setReg, ht.1], rfl, rfl, rfl, holds_of_forall fun p hp => ?_,
    fun hu => ⟨QTF.after1 hQ ht.1 (by simp [PTX.next, setReg, ht.1]) hw1 hw2 hq,
      fun v hv => hT v (.head hu hv)⟩⟩
  rcases hG p hp with rfl | ⟨hF, hne⟩
  · simp [PTX.next, setReg, Lib.minWord, hm]
    rfl
  · simpa [PTX.next, setReg, Function.update_of_ne hne] using holds_mem hreg hF

/-- A butterfly shuffle reads the register it sends: the event's operand is the fact. -/
theorem hop_bfly {A : List Assumption} {t u : TState} {e : Event} {pc r src : Nat} {n : Int}
    {m : ShflMode} {av : Value} {bv cv : Nat} {recv : Value} {ok : Bool}
    (hf : Fires pc (eventTmpl A L g t (.warp ⟨.shfl .bfly, some (.int .b 32), [some r],
      [.reg src, .imm n, .imm 31], some (.imm (-1))⟩)) e (some u))
    (hk : e.kind = .shfl m av bv cv recv ok) : t.regs src = some av := by
  simp only [eventTmpl] at hf
  rcases warpTmpl_shfl (L := L) (g := g) (t := t) (mode := .bfly) (ty := some (.int .b 32))
    (d := r) (ps := []) (a := .reg src) (b := .imm n) (c := .imm 31) (mask := .imm (-1)) with h | h
  · rw [h] at hf
    exact (Lib.shfl_operand (m := truncBits 32 (BitVec.ofInt 64 n)) rfl rfl hf hk).1
  · rw [h] at hf
    simp [Fires] at hf

variable {e : Control.Entry} {i : Nat} {v : Control.Carry} {w : Data.Vals}

/-- **A butterfly of the row sum or maximum**: the shuffle carries the operand it sent (a fact of
the site) and the received word (a datum) into the held words; the minimum that follows is exact.
The sites `s` to `z` are two pcs apart. -/
theorem sstep_fold {s z : Site} {pc r src dm : Nat} {n : Int} {a0 : Value} (hs : s.pc = pc)
    (hz : z.pc = pc + 2) (hbs : Control.SiteBody s = true) (hbz : Control.SiteBody z = true)
    (hc : kernel.code[pc]? = some ⟨none, .warp ⟨.shfl .bfly, some (.int .b 32), [some r],
      [.reg src, .imm n, .imm 31], some (.imm (-1))⟩⟩)
    (hm : kernel.code[pc + 1]? = some ⟨none, MinCore.minOp dm [src, r]⟩)
    (hn : ∀ m b c recv ok, Control.next e L g ⟨s, i, v⟩ ⟨pc, .shfl m a0 b c recv ok⟩ =
      some (some ⟨z, i, {v with word := a0, peer := recv}⟩))
    (hrec : ∀ ev, Data.record L ⟨⟨s, i, v⟩, w⟩ ev z = w)
    (hsrc : (src, a0) ∈ (Data.code e L g).facts ⟨⟨s, i, v⟩, w⟩)
    (hbf : pc ∈ [1838, 2234, 2242, 2244, 2246, 2248, 2253, 2255])
    (hfree : r ∉ Control.ctlLive pc ∧ r ∉ Data.dKeys s ∧ dm ∉ Data.dKeys z)
    (hdF : ∀ w, Data.dFS L z w = Data.dFS L s w)
    (hemu : Assumptions.emuSites.contains (pc + 1) = false ∧ pc + 1 ≠ 2562 ∧ pc + 1 ≠ 600 ∧
      pc + 1 ≠ 807)
    (hq : afterF lateQt pc [(r, .dat32)] = true)
    (hmin : (lateQt (pc + 1)).lookup src = some .dat32 ∧ (lateQt (pc + 1)).lookup r = some .dat32 ∧
      afterF lateQt (pc + 1) [(dm, .dat32)] = true ∧ dm ∈ Control.minRegs)
    (hcover : ∀ r' ∈ Control.ctlLive z.pc, r' = dm ∨ (r' ∈ Control.ctlLive pc ∧
      r' ∉ Control.wordRegs)) (ev : Event) :
    (Data.code e L g).StepForQP (QTF lateQt) (TauAll kernel Assumptions.all L g (LateR' L g))
      LWf ⟨⟨s, i, v⟩, w⟩ ev := by
  subst hs
  obtain ⟨hfr1, hfr2, hdmz⟩ := hfree
  refine Code.StepForQP.ofInv fun hinv => Code.shflOpFP (C := Data.code e L g)
    (d := ⟨⟨s, i, v⟩, w⟩) (f := fun x => ⟨⟨z, i, {v with word := a0, peer := x}⟩, w⟩)
    (r := r) (src := src) (a0 := a0) (tr := .dat32) (Pv := Dat32) hc
    (facts_ne hfr1 hfr2) hsrc (fun hf hk => hop_bfly hf hk) ?_ (fun x hx => ⟨x, rfl, hx⟩)
    ?_ rfl rfl hq (fun x hx => ⟨rfl, rfl, Control.body_inv hinv hbs hbz, ?_⟩) ev
  · exact fun _ he hpc m av bv cv recv ok hk => he.bfly (hpc ▸ hbf) m av bv cv recv ok hk
  · intro m bv cv recv ok _
    change Data.succ e L g _ _ = _
    unfold Data.succ
    rw [hn m bv cv recv ok]
    simp only [Option.map_some, Option.map_some, hrec]
  · have hzp : (Data.code e L g).pc ⟨⟨z, i, {v with word := a0, peer := x}⟩, w⟩ = s.pc + 1 + 1 :=
      hz
    rw [hzp]
    obtain ⟨hem, h2562, h600, h807⟩ := hemu
    obtain ⟨hta, htb, htq, hdm⟩ := hmin
    refine segQ_minE (R := LateR' L g) hm hem h2562 h600 h807
      (List.mem_cons_of_mem _ hsrc) (List.mem_cons_self ..) hta htb htq ?_
    intro p hp
    rcases List.mem_append.mp hp with h | h
    · obtain ⟨r', hr', rfl⟩ := List.mem_map.mp h
      rcases hcover r' (hz ▸ hr') with rfl | ⟨hl, hw'⟩
      · left
        exact congrArg (Prod.mk r') (Control.val_min (e := e) (L := L) (g := g) _ hdm)
      · right
        refine ⟨List.mem_cons_of_mem _ (List.mem_append_left _ ?_), ?_⟩
        · rw [← Control.val_frame (e := e) (L := L) (g := g) (i := i) (c := v)
            (c' := {v with word := a0, peer := x}) hw' rfl s z]
          exact mem_factsFrom hl
        · rintro rfl
          exact hw' (by simp [Control.wordRegs, hdm])
    · right
      refine ⟨List.mem_cons_of_mem _ (List.mem_append_right _ ?_), ?_⟩
      · change p ∈ Data.dFS L z w at h
        rw [hdF] at h
        exact h
      · intro hp1
        have hk : p.1 ∈ Data.dKeys z := by
          rw [← Data.dFS_keys L z w]
          exact List.mem_map_of_mem h
        exact hdmz (hp1 ▸ hk)

theorem sstep_shfl7 (ev : Event) :
    (Data.code e L g).StepForQP (QTF lateQt) (TauAll kernel Assumptions.all L g (LateR' L g))
      LWf ⟨⟨.shfl7, i, v⟩, w⟩ ev :=
  sstep_fold (s := .shfl7) (z := .shfl8) (r := 1535) (src := 507) (dm := 1536) (n := 8)
    (a0 := Lib.alphaVal (Data.scaleW L) w.m w.mx 507) (pc := 2242) rfl rfl rfl rfl
    Flow.code_2242 Flow.code_2243 (fun _ _ _ _ _ => rfl) (fun _ => rfl)
    (List.mem_append_right _ (by simp [Data.dF, Data.dFS, Data.inRound, Data.alphaFacts]))
    (by decide) ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩ (fun _ => rfl)
    (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) ev

theorem sstep_shfl8 (ev : Event) :
    (Data.code e L g).StepForQP (QTF lateQt) (TauAll kernel Assumptions.all L g (LateR' L g))
      LWf ⟨⟨.shfl8, i, v⟩, w⟩ ev :=
  sstep_fold (s := .shfl8) (z := .shfl9) (r := 1537) (src := 1536) (dm := 1538) (n := 4)
    (a0 := Control.valueOf e L g ⟨.shfl8, i, v⟩ 1536) (pc := 2244) rfl rfl rfl rfl
    Flow.code_2244 Flow.code_2245 (fun _ _ _ _ _ => rfl) (fun _ => rfl)
    (List.mem_append_left _ (mem_factsFrom (by dsimp only; decide +kernel)))
    (by decide) ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩ (fun _ => rfl)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ev

theorem sstep_shfl9 (ev : Event) :
    (Data.code e L g).StepForQP (QTF lateQt) (TauAll kernel Assumptions.all L g (LateR' L g))
      LWf ⟨⟨.shfl9, i, v⟩, w⟩ ev :=
  sstep_fold (s := .shfl9) (z := .shfl10) (r := 1539) (src := 1538) (dm := 1540) (n := 2)
    (a0 := Control.valueOf e L g ⟨.shfl9, i, v⟩ 1538) (pc := 2246) rfl rfl rfl rfl
    Flow.code_2246 Flow.code_2247 (fun _ _ _ _ _ => rfl) (fun _ => rfl)
    (List.mem_append_left _ (mem_factsFrom (by dsimp only; decide +kernel)))
    (by decide) ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩ (fun _ => rfl)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ev

theorem sstep_shfl10 (ev : Event) :
    (Data.code e L g).StepForQP (QTF lateQt) (TauAll kernel Assumptions.all L g (LateR' L g))
      LWf ⟨⟨.shfl10, i, v⟩, w⟩ ev :=
  sstep_fold (s := .shfl10) (z := .store10) (r := 1541) (src := 1540) (dm := 1534) (n := 1)
    (a0 := Control.valueOf e L g ⟨.shfl10, i, v⟩ 1540) (pc := 2248) rfl rfl rfl rfl
    Flow.code_2248 Flow.code_2249 (fun _ _ _ _ _ => rfl) (fun _ => rfl)
    (List.mem_append_left _ (mem_factsFrom (by dsimp only; decide +kernel)))
    (by decide) ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩ (fun _ => rfl)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ev

theorem val_1542 (e : Control.Entry) (L : Launch) (g : Nat) (d : Control.D) :
    Control.valueOf e L g d 1542 = d.held.word := by
  simp [Control.valueOf]

theorem sstep_shfl11 (ev : Event) :
    (Data.code e L g).StepForQP (QTF lateQt) (TauAll kernel Assumptions.all L g (LateR' L g))
      LWf ⟨⟨.shfl11, i, v⟩, w⟩ ev :=
  sstep_fold (s := .shfl11) (z := .shfl12) (r := 1543) (src := 1542) (dm := 1544) (n := 2)
    (a0 := Control.valueOf e L g ⟨.shfl11, i, v⟩ 1542) (pc := 2253) rfl rfl rfl rfl
    Flow.code_2253 Flow.code_2254 (fun _ _ _ _ _ => by rw [val_1542]; rfl) (fun _ => rfl)
    (List.mem_append_left _ (mem_factsFrom (by dsimp only; decide +kernel)))
    (by decide) ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩ (fun _ => rfl)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ev

end PTX.Kernels.InklingRelDecode.Proof.Softmax.Strict
