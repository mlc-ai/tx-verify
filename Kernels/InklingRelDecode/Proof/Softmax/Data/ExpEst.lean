-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Softmax.Data.Alpha
public import Kernels.InklingRelDecode.Proof.Softmax.Data.ExpFam
public import Kernels.InklingRelDecode.Proof.Softmax.Data.ExpWindow
public import Lemmas.Flow.SegFrameR
import Kernels.InklingRelDecode.Flow.Code

@[expose] public section

/-! # The exponent window from the shuffle of pc 1838

After the shuffle of pc 1838 the rescale run (pcs 1839 to 1846) and the exponent window (pcs 1847
to 2233) run to the shuffle of pc 2234. The registers the window reads are the rescale run's, the
negated scale and the first window's (`kXin`): their values are `xV` of the state, which the
window turns into the exponentials of `xF`. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
open PTX PTX.Proof PTX.Flow PTX.Flow.Code PTX.EventFrame Control

set_option maxRecDepth 100000
noncomputable section
variable {e : Entry} {L : Launch} {g : Nat}

/-- The registers that the exponent window reads and the rescale run does not write. -/
def kHx : List Nat := scoreRegs ++ [179, 180, 499]

/-- The rescale run's inputs, with the carried registers' values `vH`. -/
def alphaW (L : Launch) (m sent recv : Value) (vH : Nat → Value) (r : Nat) : Value :=
  if r ∈ kHx then vH r else alphaV L m sent recv r

theorem kE0_cls : ∀ r ∈ kE0, r = 168 ∨ r = 498 ∨ r = 1914 ∨ r = 1523 ∨ r ∈ kHx := by
  decide +kernel

theorem kHx_not : ∀ r ∈ [168, 498, 1914, 1523, 1520, 1521, 507, 1522], r ∉ kHx := by
  decide +kernel

theorem kHx_free : ∀ r ∈ kHx, r ∉ xWrites Lib.alphaItems := by decide +kernel

theorem xKeys_sub : ∀ r ∈ xKeys, r ∈ kE3 := by decide +kernel

/-- **The rescale run with the carried registers.** -/
theorem alpha_run_k (m sent recv : Value) (vH : Nat → Value) :
    SegU kernel Assumptions.all L g 1839
      (factsFrom ([1520, 1521, 1914, 498] ++ kHx) (alphaW L m sent recv vH)) 1847
      (factsFrom ([498, 1914, 1522, 168, 507, 1523] ++ kHx)
        (xFinal (alphaW L m sent recv vH) Lib.alphaItems)) :=
  SegU.of_items Lib.alpha_at (by decide +kernel) (by decide +kernel) (req_alpha _)
    (by decide +kernel)

theorem alphaW_four (m sent recv : Value) (vH : Nat → Value) {r : Nat}
    (hr : r = 168 ∨ r = 498 ∨ r = 1914 ∨ r = 1523) :
    xFinal (alphaW L m sent recv vH) Lib.alphaItems r =
      Lib.alphaVal (scaleW L) m (Lib.mxWord m sent recv) r := by
  have hn := kHx_not
  have h1 : alphaW L m sent recv vH 1914 = m := by simp [alphaW, alphaV, hn 1914 (by simp)]
  have h2 : alphaW L m sent recv vH 1520 = sent := by simp [alphaW, alphaV, hn 1520 (by simp)]
  have h3 : alphaW L m sent recv vH 1521 = recv := by simp [alphaW, alphaV, hn 1521 (by simp)]
  have h4 : alphaW L m sent recv vH 498 = scaleW L := by simp [alphaW, alphaV, hn 498 (by simp)]
  rcases hr with rfl | rfl | rfl | rfl
  · exact alpha_fin h1 h2 h3 h4 (Or.inl rfl)
  · rw [Lib.xFinal_other (by decide), h4, alphaVal_c]
  · rw [Lib.xFinal_other (by decide), h1, alphaVal_m]
  · exact alpha_fin h1 h2 h3 h4 (Or.inr (Or.inr rfl))

theorem alphaW_kx (m sent recv : Value) (vH : Nat → Value) {r : Nat} (hr : r ∈ kHx) :
    xFinal (alphaW L m sent recv vH) Lib.alphaItems r = vH r := by
  rw [Lib.xFinal_other (kHx_free r hr)]
  simp [alphaW, hr]

/-- The window's input registers are among the facts the rescale run leaves. -/
theorem alpha_sub (m sent recv : Value) (vH : Nat → Value) {V : Nat → Value}
    (hV : ∀ r ∈ kE0, V r = if r = 168 ∨ r = 498 ∨ r = 1914 ∨ r = 1523 then
      Lib.alphaVal (scaleW L) m (Lib.mxWord m sent recv) r else vH r) :
    ∀ x ∈ factsFrom kE0 V, x ∈ factsFrom ([498, 1914, 1522, 168, 507, 1523] ++ kHx)
      (xFinal (alphaW L m sent recv vH) Lib.alphaItems) := fun x hx => by
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hx
  have hval : V r = xFinal (alphaW L m sent recv vH) Lib.alphaItems r := by
    rw [hV r hr]
    by_cases h4 : r = 168 ∨ r = 498 ∨ r = 1914 ∨ r = 1523
    · simp only [h4, ↓reduceIte]
      exact (alphaW_four m sent recv vH h4).symm
    · have hk : r ∈ kHx := by
        rcases kE0_cls r hr with h | h | h | h | h
        · exact absurd (Or.inl h) h4
        · exact absurd (Or.inr (Or.inl h)) h4
        · exact absurd (Or.inr (Or.inr (Or.inl h))) h4
        · exact absurd (Or.inr (Or.inr (Or.inr h))) h4
        · exact h
      simp only [h4, ↓reduceIte]
      exact (alphaW_kx m sent recv vH hk).symm
  have hmem : r ∈ [498, 1914, 1522, 168, 507, 1523] ++ kHx := by
    rcases kE0_cls r hr with h | h | h | h | h
    · simp [h]
    · simp [h]
    · simp [h]
    · simp [h]
    · exact List.mem_append_right _ h
  rw [hval]
  exact mem_factsFrom hmem

/-- The facts at the shuffle's successor give the rescale run's inputs. -/
theorem alpha_start (m sent recv : Value) (vH : Nat → Value) :
    ∀ R, Holds R ([(1520, sent), (1521, recv), (1914, m), (498, scaleW L)] ++ factsFrom kHx vH) →
      Holds R (factsFrom ([1520, 1521, 1914, 498] ++ kHx) (alphaW L m sent recv vH)) := by
  intro R h
  obtain ⟨⟨h1, h2, h3, h4, -⟩, h5⟩ := (holds_append _ _ _).mp h
  refine holds_of_pointwise fun r hr => ?_
  rcases List.mem_append.mp hr with hr | hr
  · have hn := kHx_not
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · simpa [alphaW, alphaV, hn 1520 (by simp)] using h1
    · simpa [alphaW, alphaV, hn 1521 (by simp)] using h2
    · simpa [alphaW, alphaV, hn 1914 (by simp)] using h3
    · simpa [alphaW, alphaV, hn 498 (by simp)] using h4
  · simpa [alphaW, hr] using holds_mem h5 (mem_factsFrom hr)

/-- **From the rescale run's start to the exponentials**, for the registers the window reads. -/
theorem alpha_reach_x (m sent recv : Value) (vH : Nat → Value) {V : Nat → Value}
    (hE : ExpIn V) (hV : ∀ r ∈ kE0, V r = if r = 168 ∨ r = 498 ∨ r = 1914 ∨ r = 1523 then
      Lib.alphaVal (scaleW L) m (Lib.mxWord m sent recv) r else vH r) :
    Reach kernel Assumptions.all L g 1839
      ([(1520, sent), (1521, recv), (1914, m), (498, scaleW L)] ++ factsFrom kHx vH)
      (factsFrom xKeys (vE3 V)) := by
  have p2 := SegU.sub_start (F' := factsFrom ([498, 1914, 1522, 168, 507, 1523] ++ kHx)
      (xFinal (alphaW L m sent recv vH) Lib.alphaItems))
    (exp_window (L := L) (g := g) hE) (alpha_sub (L := L) m sent recv vH hV)
  have p3 : Reach kernel Assumptions.all L g 2234 (factsFrom kE3 (vE3 V))
      (factsFrom xKeys (vE3 V)) :=
    reach_frameSetG (S := []) Lib.rulesFrame (by rw [factsFrom_keys]; decide +kernel)
      (fun _ h => nomatch h) (by decide +kernel) (fun R h => holds_factsFrom_mono h xKeys_sub)
  exact Reach.weaken_start (SegU.reach_then (SegU.comp
    (alpha_run_k (L := L) (g := g) m sent recv vH) p2) p3) (alpha_start (L := L) m sent recv vH)

theorem kHx_cls : ∀ r ∈ kHx, r = 499 ∨ r ∈ kXin := by decide +kernel

/-- The registers the window reads that the first window leaves (and the negated scale). -/
def vHs (e : Entry) (L : Launch) (g : Nat) (d : D) : Nat → Value :=
  fun r => if r = 499 then derV e L g 499 else vFin (w1V e L g d) r

/-- **The state after the shuffle of pc 1838**: the window's start facts, from the facts of the
site before it. -/
theorem shfl5_at {d : D} (hs : d.c.site = .shfl5) {t u : TState} {ev : Event} {ins : Instr}
    (hat : (codeS e L g).AtD d t) (hc' : kernel.code[1838]? = some ins)
    (hf : Fires 1838 (eventTmpl Assumptions.all L g t ins.op) ev (some u)) :
    ∃ mode sent bv cv recv ok, ev = ⟨1838, .shfl mode sent bv cv recv ok⟩ ∧
      At u 1839 ([(1520, sent), (1521, recv), (1914, d.v.m), (498, scaleW L)] ++
        factsFrom kHx (vHs e L g d)) := by
  rw [Flow.code_shfl_5] at hc'
  obtain rfl := Option.some.inj hc'
  obtain ⟨sent, bv, cv, recv, ok, hr, rfl, rfl⟩ := fires_shfl_src (p := none) hf
  refine ⟨_, sent, bv, cv, recv, ok, rfl, ?_⟩
  obtain ⟨hpc, hsub, hacc, hft, hreg⟩ := hat
  have hF := facts_dF _ ((holds_append _ _ _).mp hreg).1
  have h1914 : t.regs 1914 = some d.v.m := holds_mem hF (by simp [dF, dFS, hs])
  have h498 : t.regs 498 = some (scaleW L) := holds_mem hF (by simp [dF, dFS, hs])
  obtain ⟨-, hder, -, hw⟩ := atS_holds hreg
  have hw1f : Holds t.regs (factsFrom kXin (vFin (w1V e L g d))) := by
    have := ((holds_append _ _ _).mp ((holds_append _ _ _).mp hw).1).2
    simpa [w1F, hs] using this
  have hH : Holds t.regs (factsFrom kHx (vHs e L g d)) := by
    refine holds_of_pointwise fun r hr' => ?_
    rcases kHx_cls r hr' with rfl | hk
    · have hder' : Holds t.regs (factsFrom keysC (derV e L g)) := by simpa [derF, hs] using hder
      have := holds_mem hder' (mem_factsFrom (val := derV e L g) (show 499 ∈ keysC by decide))
      simpa [vHs] using this
    · have := holds_mem hw1f (mem_factsFrom (val := vFin (w1V e L g d)) hk)
      have hn : r ≠ 499 := by rintro rfl; exact absurd hk (by decide +kernel)
      simpa [vHs, hn] using this
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [PTX.next, setReg, hpc]
    rw [hs]
    rfl
  · simp [PTX.next, setReg, hsub]
  · simp [PTX.next, setReg, hacc]
  · simp [PTX.next, setReg, hft]
  · refine (holds_append _ _ _).mpr ⟨?_, ?_⟩
    · simp [PTX.next, setReg, Holds, Function.update_of_ne, h1914, h498, hr]
    · refine holds_of_pointwise fun r hr' => ?_
      have hne : r ≠ 1521 := by
        rintro rfl
        exact kHx_not 1521 (by simp) hr'
      have := holds_mem hH (mem_factsFrom (val := vHs e L g d) hr')
      simpa [PTX.next, setReg, Function.update_of_ne hne] using this

/-- **The successor of the shuffle's state** is at the next site with the window's registers
`xV` those of the rescale run on the words of the shuffle. -/
theorem xV_shfl5 {d d' : D} (hs : d.c.site = .shfl5) {mode : ShflMode}
    {sent recv : Value} {bv cv : Nat} {ok : Bool}
    (hn : succ e L g d ⟨1838, .shfl mode sent bv cv recv ok⟩ = some (some d')) :
    d'.c.site = .shfl6 ∧ m0 d' = d.v.m ∧ d'.v.mx = Lib.mxWord d.v.m sent recv ∧
      ∀ r ∈ kE0, xV e L g d' r = if r = 168 ∨ r = 498 ∨ r = 1914 ∨ r = 1523 then
        Lib.alphaVal (scaleW L) d.v.m (Lib.mxWord d.v.m sent recv) r else vHs e L g d r := by
  obtain ⟨c', hnc, hd'⟩ := succ_inv hn
  simp only [Control.next, hs, Option.some.injEq] at hnc
  subst hnc
  have hm0 : m0 d' = d.v.m := by rw [hd']; simp [m0, record, hs]
  have hmx : d'.v.mx = Lib.mxWord d.v.m sent recv := by rw [hd']; simp [record, hs]
  have hw1 : w1V e L g d' = w1V e L g d := by rw [hd']; simp [w1V, canon, m0, record, hs]
  exact ⟨by rw [hd'], hm0, hmx, fun r _ => by simp only [xV, hm0, hmx, hw1, vHs]⟩

open Classical in
/-- **The exponentials after the shuffle of pc 1838**: the window's registers are the state's
(`xV`), and the window leaves the exponentials (`xF`) when they are typed. -/
theorem x_shfl5 {d : D} (hs : d.c.site = .shfl5) : DataStep (codeS e L g) (xF e L g) d := by
  have pc : (codeS e L g).pc d = 1838 := by
    change d.c.site.pc = 1838
    rw [hs]
    rfl
  intro t ev u d' ins hat hi hc' hf hn
  rw [pc] at hc' hf
  obtain ⟨mode, sent, bv, cv, recv, ok, rfl, hAt⟩ := shfl5_at hs hat hc' hf
  obtain ⟨hsite, -, -, hV⟩ := xV_shfl5 hs hn
  by_cases hE : ExpIn (xV e L g d')
  · rw [xF_round (by rw [hsite]; rfl) hE]
    exact alpha_reach_x (L := L) (g := g) d.v.m sent recv (vHs e L g d) hE hV _ hAt
  · exact .inl fun _ _ _ => by rw [xF_no hE]; trivial

end
end PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
