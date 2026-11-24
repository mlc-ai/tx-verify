-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.ScFence
public import Kernels.InklingRelDecode.Proof.Interface.ScNum
public import Kernels.InklingRelDecode.Proof.Interface.ScRead

@[expose] public section

/-!
# The allocation's store of the Tensor Memory base word

`AllocWordZero`: the allocation's store writes the zero word. `allocWr_anchor`: the CTA's thread 0
(lane 0 of warp 0) makes the store before its barrier-0 arrival of ordinal 0 (`exists_allocWr`).
Both are used by the read of the base word (`base_read_w`, `BaseWRead.lean`).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode PTX.Kernels.InklingRelDecode.Proof.Ledger
open PTX.Kernels.InklingRelDecode.Proof.Bar PTX.Kernels.InklingRelDecode.Proof.BarOrd

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **The allocation's store writes the zero word**: the address `tcgen05.alloc` of the 512
columns stores is column 0. -/
def AllocWordZero (Q : Params) (L : Launch) (X : Execution) : Prop :=
  ∀ {g k pc : Nat} {a : Acc} {bs : List Byte} {tm : Value},
    X.get (g, k) = some ⟨pc, .wr a bs⟩ →
      St Q L X g k = some (some (.d (.dstart ⟨.allocWr, tm⟩))) → bs = (b32 0).toBytes

/-- The default-partition states after the allocation's store. -/
def AfterAlloc : TSt → Prop
  | .d (.dstart d) => d.site ≠ .alloc ∧ d.site ≠ .allocWr
  | .d (.pro _) => True
  | .d (.sm _) => True
  | .d (.epi _) => True
  | _ => False

/-- A step into a state after the allocation's store comes from the store or from such a state,
for lane 0 (which goes from `alloc` to `allocWr`). -/
theorem next_afterAlloc {g : Nat} (hlane : laneOf L g = 0) {s s' : TSt} {e : Event}
    (hn : (threadCode L g Q).next s e = some (some s')) (hs : AfterAlloc s') :
    AfterAlloc s ∨ ∃ d : DStart.D, s = .d (.dstart d) ∧ d.site = .allocWr := by
  cases s with
  | w s =>
    obtain ⟨a, -, rfl⟩ := map_map_eq_some_some (show (WComp.next L g s e).map (Option.map TSt.w) =
      some (some s') from hn)
    exact hs.elim
  | d s =>
    obtain ⟨a, ha, rfl⟩ := map_map_eq_some_some (show (DComp.next L g Q s e).map
      (Option.map TSt.d) = some (some s') from hn)
    cases s with
    | dstart d =>
      obtain ⟨site, tm⟩ := d
      cases site
      · -- `alloc`: lane 0 goes to `allocWr`
        exfalso
        change DComp.dstartNext L g Q ⟨.alloc, tm⟩ _ = _ at ha
        unfold DComp.dstartNext at ha
        obtain ⟨d', hd', hs'⟩ := map_map_eq_some_some ha
        simp only [DStart.next, hlane, ↓reduceIte, Option.some.injEq] at hd'
        subst hd'
        simp only at hs'
        subst hs'
        simp [AfterAlloc] at hs
      · exact .inr ⟨_, rfl, rfl⟩
      all_goals exact .inl (by simp [AfterAlloc])
    | pro d => left; trivial
    | sm d => left; trivial
    | epi d => left; trivial

theorem init_notAfterAlloc {g : Nat} (hl : g % L.block < 32) : ¬ AfterAlloc (code L Q g).init := by
  have hd : g % L.block < 128 := by omega
  show ¬ AfterAlloc (if g % L.block < 128 then TSt.d (DComp.code L g Q).init
    else .w (WComp.code L g Q).init)
  simp only [hd, ite_true]
  simp [AfterAlloc, DStart.D.start, hl]

/-- **A state after the allocation's store has the store's state earlier in its run**, for lane 0
of warp 0. -/
theorem exists_allocWr {g : Nat} (hl : g % L.block < 32) (hlane : laneOf L g = 0) :
    ∀ k s, St Q L X g k = some (some s) → AfterAlloc s →
      ∃ j < k, ∃ d : DStart.D, St Q L X g j = some (some (.d (.dstart d))) ∧
        d.site = .allocWr := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro s hσ hs
    by_cases hinit : s = (code L Q g).init
    · subst hinit
      exact absurd hs (init_notAfterAlloc hl)
    · obtain ⟨k0, e, s0, hlt, he, hs0, hn⟩ := stateAt_pred hσ hinit
      rcases next_afterAlloc hlane hn hs with h | ⟨d, rfl, hd⟩
      · obtain ⟨j, hj, d, hd, hsite⟩ := ih k0 hlt s0 hs0 h
        exact ⟨j, by omega, d, hd, hsite⟩
      · exact ⟨k0, hlt, d, hs0, hd⟩

theorem bar0_not_ub {pc : Nat} {m : BarMode} :
    ∀ pc' f, (⟨pc, .bar 0 none m⟩ : Event) ≠ ⟨pc', .ub f⟩ := by
  intro pc' f h
  cases h

/-- **The allocation's store before the barrier-0 arrival of ordinal 0 of lane 0 of warp 0**, and
its event. -/
theorem allocWr_anchor (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hS : ∀ g < L.threads, (threadCode L g Q).Sound)
    (hT : ∀ g < L.threads, (threadCode L g Q).TmplOk) {g0 i0 pc0 : Nat} (hg0 : g0 < L.threads)
    (hl : g0 % L.block < 32) (hlane : laneOf L g0 = 0) (hf : X.IsBarrier (g0, i0) 0 none pc0)
    (hc : ((X.tr g0).take i0).countP (Execution.isBarId 0) = 0)
    (hprev : i0 = 0 ∨ ∃ k', i0 = k' + 1 ∧ TT Q L X (g0, k')) :
    ∃ j1 < i0, ∃ tm pc1 col, St Q L X g0 j1 = some (some (.d (.dstart ⟨.allocWr, tm⟩))) ∧
      X.get (g0, j1) = some ⟨pc1, .wr { loc := ⟨.shared, g0 / L.block, L.sharedBase⟩, size := 4 }
        (b32 col).toBytes⟩ := by
  have he0 : X.get (g0, i0) = some ⟨pc0, .bar 0 none .sync⟩ := hf
  have hli : i0 < (X.tr g0).length := (List.getElem?_eq_some_iff.mp he0).1
  obtain ⟨s0, hσ0⟩ := state_of_prev hS hX he0 bar0_not_ub hprev
  obtain ⟨hlb1, hlb2⟩ := ordinal_inv hX hS i0 s0 hli.le hσ0
  have hlb : tLb s0 = 0 := by omega
  have hdef : g0 % L.block < 128 := by omega
  have hd0 : s0.isD := (cls_inv i0 s0 hli.le hσ0).mpr hdef
  have hinc : tInc s0 = 1 := by
    rcases start_event hX hS he0 hσ0 (by omega) with ⟨h1, -⟩ | ⟨-, h2⟩
    · exact h1
    · exact absurd rfl (h2 0 none .sync)
  have hafter : AfterAlloc s0 := by
    cases s0 with
    | w s => exact hd0.elim
    | d x =>
      cases x with
      | dstart d =>
        obtain ⟨site, tm⟩ := d
        cases site <;> simp_all [tLb, tInc, dLb, dInc, AfterAlloc]
      | pro d => trivial
      | sm d => trivial
      | epi d => trivial
  obtain ⟨j1, hj1, d1, hσ1, hs1⟩ := exists_allocWr hl hlane i0 s0 hσ0 hafter
  obtain ⟨site, tm⟩ := d1
  simp only at hs1
  subst hs1
  have hj1' : j1 < (X.tr g0).length := by omega
  obtain ⟨e1, he1⟩ : ∃ e1, X.get (g0, j1) = some e1 := ⟨_, List.getElem?_eq_getElem hj1'⟩
  obtain ⟨u, hF⟩ := fired_cont_at hX hS hT hg0 he1 hσ1 (by simp [ExitState])
  have hb : L.block % 32 = 0 := by rw [hpre.block]
  obtain ⟨col, -, he2⟩ := DStart.shape_allocWr hb (ProA.sharedOk_of_pre hpre) (fired_dstart hF) rfl
  exact ⟨j1, hj1, tm, _, col, hσ1, by rw [he1, he2]⟩

end
end PTX.Kernels.InklingRelDecode.Proof.Interface
