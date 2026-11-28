-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Softmax.Data.ExpKinds
public import Kernels.InklingRelDecode.Proof.Softmax.Data.LateKinds
public import Kernels.InklingRelDecode.Proof.Softmax.Data.ExpLib
public import Kernels.InklingRelDecode.Proof.Softmax.Data.DeclLib
import Lemmas.Flow.Widen

@[expose] public section

/-! # The kinds of the exponentials' run, with the sums of pairs

`kRun` accepts no sum of two pairs by a role's reading (`add2NL`); `ekRun` adds it for two pairs of
numbers. At each unrounded sum of the run both sources have those kinds (`eSites`), so the sum is
not declined. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
open PTX PTX.Flow PTX.Proof PTX.Assumption PTX.Kernels.InklingRelDecode.Proof.Iface

noncomputable section

/-- The kinds after an item: `kItem`, and the sum of two pairs of numbers. -/
def ekItem (K : Nat → Kd) : XItem → Option (Nat → Kd)
  | .fn _ d [a, b] _ => match K a, K b with
    | .pr x, .pr y => if x.le .fl && y.le .fl then some (Function.update K d (.pr .fl)) else none
    | _, _ => none
  | .fn _ d [a, b, _] _ => match K a, K b with
    | .s x, .s y => if x.le .fl && y.le .fl then some (Function.update K d (.s .fl)) else none
    | _, _ => none
  | .fn .. => none
  | it => kItem K it

def ekRun (K : Nat → Kd) : List XItem → Option (Nat → Kd)
  | [] => some K
  | it :: its => (ekItem K it).bind fun K' => ekRun K' its

/-- The role readings of a two-source item are the sum of two pairs. -/
def FnOkE : XItem → Prop
  | .fn _ _ [a, b] f => b ≠ a ∧ f = fF add2NL [.reg a, .reg b]
  | .fn _ d [a, b, p] f => b ≠ a ∧ p ≠ a ∧ p ≠ b ∧ f = coreF (.int ⟨.selp, .float .f32, false,
      [some d], [.reg a, .reg b, .reg p]⟩) [a, b, p]
  | _ => True

def ekOut (K : Nat → Kd) (items : List XItem) : Nat → Kd := (ekRun K items).getD K

theorem pr_mono_le {a b : SK} {v : Value} (h : a.le b = true) (hv : (Kd.pr a).Has v) :
    (Kd.pr b).Has v := ⟨hv.1, SK.mono h hv.2.1, SK.mono h hv.2.2⟩

theorem ekItem_sound {K K' : Nat → Kd} {V : Nat → Value} {it : XItem}
    (h : ekItem K it = some K') (hV : ∀ r, (K r).Has (V r)) (hf : FnOkE it) :
    ∀ r, (K' r).Has (it.upd V r) := by
  cases it with
  | base b => exact (kItem_sound h hV trivial).2
  | fn op d srcs f =>
    match srcs, h, hf with
    | [a, b], h, ⟨hb, hfe⟩ =>
      subst hfe
      have ha := hV a
      have hb' := hV b
      rcases hka : K a with _ | _ | ka | ka <;> rcases hkb : K b with _ | _ | kb | kb <;>
        simp only [ekItem, hka, hkb, reduceCtorEq] at h
      by_cases hc : ka.le .fl && kb.le .fl
      · simp only [hc, ↓reduceIte, Option.some.injEq] at h
        subst h
        rw [Bool.and_eq_true] at hc
        rw [hka] at ha
        rw [hkb] at hb'
        rw [upd_one V _ (d := d) (v := okVal (.bits 32 0) ((fF add2NL [.reg a, .reg b])
          [V a, V b])) rfl]
        exact has_update hV (add2_out hb (pr_mono_le hc.1 ha) (pr_mono_le hc.2 hb'))
      · simp only [hc, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at h
    | [a, b, p], h, ⟨hba, hpa, hpb, hfe⟩ =>
      subst hfe
      have ha := hV a
      have hb' := hV b
      rcases hka : K a with _ | _ | ka | ka <;> rcases hkb : K b with _ | _ | kb | kb <;>
        simp only [ekItem, hka, hkb, reduceCtorEq] at h
      by_cases hc : ka.le .fl && kb.le .fl
      · simp only [hc, ↓reduceIte, Option.some.injEq] at h
        subst h
        rw [Bool.and_eq_true] at hc
        rw [hka] at ha
        rw [hkb] at hb'
        rw [upd_one V _ (d := d) (v := okVal (.bits 32 0) (coreF (.int ⟨.selp, .float .f32, false,
          [some d], [.reg a, .reg b, .reg p]⟩) [a, b, p] [V a, V b, V p])) rfl]
        exact has_update hV (selp2_has (k := .fl) rfl hba hpa hpb (fun _ => SK.mono hc.1 ha)
          (SK.mono hc.2 hb'))
      · simp only [hc, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at h
    | [], h, _ => simp [ekItem] at h
    | [_], h, _ => simp [ekItem] at h
    | _ :: _ :: _ :: _ :: _, h, _ => simp [ekItem] at h

theorem ekRun_sound : ∀ {K K' : Nat → Kd} {V : Nat → Value} {items : List XItem},
    ekRun K items = some K' → (∀ r, (K r).Has (V r)) → (∀ it ∈ items, FnOkE it) →
    ∀ r, (K' r).Has (xFinal V items r)
  | K, K', V, [], h, hV, _ => by
    simp only [ekRun, Option.some.injEq] at h
    subst h
    exact hV
  | K, K', V, it :: its, h, hV, hf => by
    simp only [ekRun] at h
    obtain ⟨K1, h1, h2⟩ := Option.bind_eq_some_iff.mp h
    exact ekRun_sound (V := it.upd V) h2 (ekItem_sound h1 hV (hf it (by simp)))
      fun x hx => hf x (by simp [hx])

theorem ekRun_take : ∀ {items : List XItem} {K K' : Nat → Kd}, ekRun K items = some K' →
    ∀ j, ∃ K'', ekRun K (items.take j) = some K''
  | [], _, _, h, j => ⟨_, by simpa using h⟩
  | it :: its, K, K', h, j => by
    cases j with
    | zero => exact ⟨K, rfl⟩
    | succ j =>
      obtain ⟨K1, h1, h2⟩ := Option.bind_eq_some_iff.mp (by simpa only [ekRun] using h)
      obtain ⟨K2, h3⟩ := ekRun_take h2 j
      exact ⟨K2, by simp only [List.take_succ_cons, ekRun, h1, Option.bind_some, h3]⟩

/-- A source register of a kind, written before the item or read from the start. -/
def eSrc (K : Nat → Kd) (dom ws : List Nat) (a : Nat) (pr : Bool) : Bool :=
  (ws.contains a || dom.contains a) &&
    match K a with | .pr x => pr && x.le .fl | .s x => !pr && x.le .fl | _ => false

/-- The unrounded sum at an item has the two-pair or the two-number kinds on its sources. -/
def eDecl (K : Nat → Kd) (dom ws : List Nat) : Op → Bool
  | .float f => !declineOp (.float f) ||
    match f.srcs with
    | [.reg a, .reg b] =>
      (arith2 .add 2 f (.reg a) (.reg b) && eSrc K dom ws a true &&
        eSrc K dom ws b true) ||
      (arith2 .add 1 f (.reg a) (.reg b) && eSrc K dom ws a false && eSrc K dom ws b false)
    | _ => false
  | _ => true

def eSites (K : Nat → Kd) (items : List XItem) (dom : List Nat) (s0 : Nat) : Bool :=
  (List.range items.length).all fun j =>
    match kernel.code[s0 + j]? with
    | some ⟨_, op⟩ => eDecl (ekOut K (items.take j)) dom (xWrites (items.take j)) op
    | none => true

theorem e_src {K1 : Nat → Kd} {V : Nat → Value} {t : TState} {ws dom : List Nat} {a : Nat}
    {pr : Bool} (hreg : ∀ r ∈ ws ++ dom, t.regs r = some (V r)) (hk : ∀ r, (K1 r).Has (V r))
    (h : eSrc K1 dom ws a pr = true) :
    t.regs a = some (V a) ∧ ((pr = true ∧ (Kd.pr .fl).Has (V a)) ∨
      (pr = false ∧ SK.fl.Has (V a))) := by
  simp only [eSrc, Bool.and_eq_true, Bool.or_eq_true, List.contains_iff_mem] at h
  obtain ⟨hm, h⟩ := h
  refine ⟨hreg a (by rcases hm with hm | hm <;> simp [hm]), ?_⟩
  have hv := hk a
  rcases hKa : K1 a with _ | _ | x | x <;> rw [hKa] at hv h <;> simp only [Bool.and_eq_true] at h
  · cases h
  · cases h
  · obtain ⟨hp, hx⟩ := h
    simp only [Bool.not_eq_true'] at hp
    exact .inr ⟨hp, SK.mono hx hv⟩
  · obtain ⟨hp, hx⟩ := h
    exact .inl ⟨hp, pr_mono_le hx hv⟩


/-- The exponentials' run: pcs 2089 to 2233. -/
def ex2All : List XItem := Gen.ex2_items0 ++ (Gen.ex2_items1 ++ (Gen.ex2_items2 ++
  (Gen.ex2_items3 ++ Gen.ex2_items4)))

/-- The kinds its start registers have: the shifted scores and the selected singles. -/
def kE20 : Nat → Kd := fun r => if r ∈ xRegs then .s .ni else if r ∈ swOuts then .s .fl else .no

theorem ex2_ek : (ekRun kE20 ex2All).isSome = true := by decide +kernel
theorem ex2_sites : eSites kE20 ex2All runE2.live 2089 = true := by decide +kernel
theorem ex2_reads : xReadsB runE2.live ex2All = true := by decide +kernel
theorem ex2_local : xLocalB ex2All = true := by decide +kernel
theorem ex2_req (V : Nat → Value) : xReq V ex2All = true := by rfl
theorem ex2_len : ex2All.length = 145 := by decide +kernel
theorem ex2_at (L : Launch) (g : Nat) : OAt kernel Assumptions.all L g 2089 ex2All :=
  OAt.append (Gen.ex2_at0 L g) (OAt.append (Gen.ex2_at1 L g) (OAt.append (Gen.ex2_at2 L g)
    (OAt.append (Gen.ex2_at3 L g) (Gen.ex2_at4 L g))))

theorem ex2_fnok : ∀ it ∈ ex2All, FnOkE it := by
  simp only [ex2All, Gen.ex2_items0, Gen.ex2_items1, Gen.ex2_items2, Gen.ex2_items3,
    Gen.ex2_items4, List.forall_mem_append, List.forall_mem_cons, FnOkE, and_self,
    List.not_mem_nil, false_imp_iff, implies_true]
  repeat' trivial

/-- **The unrounded sums of the exponentials' run are not declined**, at a state after a prefix of
its items. -/
theorem e2_decl_core {L : Launch} {g : Nat} {t : TState} {W : Nat → Value} {j : Nat}
    (hW : ∀ r, (kE20 r).Has (W r)) (hj : j < 145) (hpc : t.pc = 2089 + j)
    (hregs : ∀ r ∈ xWrites (ex2All.take j) ++ runE2.live,
      t.regs r = some (xFinal W (ex2All.take j) r))
    {i : Instr} (hc : kernel.code[t.pc]? = some i) (hd : declineOp i.op = true) :
    execIdealFloat L g t i.op ≠ none := by
  obtain ⟨K', hK'⟩ := Option.isSome_iff_exists.mp ex2_ek
  obtain ⟨K1, h1⟩ := ekRun_take hK' j
  have hs := List.all_eq_true.mp ex2_sites j (List.mem_range.mpr (by rw [ex2_len]; exact hj))
  rw [← hpc, hc] at hs
  have hk := ekRun_sound h1 hW fun it hit => ex2_fnok it (List.mem_of_mem_take hit)
  obtain ⟨guard, op⟩ := i
  obtain ⟨f, rfl⟩ : ∃ f, op = .float f := by
    cases op <;> first | exact ⟨_, rfl⟩ | (simp [declineOp] at hd)
  simp only [eDecl, ekOut, h1, Option.getD_some, hd, Bool.not_true, Bool.false_or] at hs
  rcases hsr : f.srcs with _ | ⟨s1, _ | ⟨s2, _ | ⟨s3, tl⟩⟩⟩ <;> rw [hsr] at hs <;>
    try (simp at hs)
  cases s1 <;> cases s2 <;> try (simp at hs; done)
  rename_i a b
  simp only [Bool.or_eq_true, Bool.and_eq_true] at hs
  rcases hs with ⟨⟨h2, ha⟩, hb⟩ | ⟨⟨h2, ha⟩, hb⟩
  · obtain ⟨ra, hpa⟩ := e_src hregs hk ha
    obtain ⟨rb, hpb⟩ := e_src hregs hk hb
    obtain ⟨-, ⟨-, x0, hx0⟩, ⟨-, x1, hx1⟩⟩ := (hpa.resolve_right (by simp)).2
    obtain ⟨-, ⟨-, y0, hy0⟩, ⟨-, y1, hy1⟩⟩ := (hpb.resolve_right (by simp)).2
    exact ideal_add2 h2 (by rw [readERealPair_reg_val ra]; exact pairRead_of_reads hx0 hx1)
      (by rw [readERealPair_reg_val rb]; exact pairRead_of_reads hy0 hy1)
      (by rw [addEReal_coe]; simp) (by rw [addEReal_coe]; simp)
  · obtain ⟨ra, hpa⟩ := e_src hregs hk ha
    obtain ⟨rb, hpb⟩ := e_src hregs hk hb
    obtain ⟨x, hx, ⟨r, rfl⟩⟩ := rd_sk (k := .fl) rfl ra (hpa.resolve_left (by simp)).2
    obtain ⟨y, hy, ⟨s, rfl⟩⟩ := rd_sk (k := .fl) rfl rb (hpb.resolve_left (by simp)).2
    exact ideal_add1 h2 hx hy (by rw [addEReal_coe]; simp)

end
end PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
