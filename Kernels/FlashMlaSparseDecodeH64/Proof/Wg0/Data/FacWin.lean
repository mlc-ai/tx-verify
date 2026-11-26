-- SPDX-License-Identifier: Apache-2.0
-- domain: valid-rows
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.EldWin
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.Fac
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part018

@[expose] public section

/-! # The strict window after the fence before the zero-sum test (pcs 1188 to 1201)

The grid-dependency instruction (pc 1188), the zero-sum test (pcs 1189-1190, a value run), the
branch at pc 1191 on the test's predicate, the factor's run on a non-zero sum (pcs 1192-1196), the
descriptor address and the staging test (pcs 1197-1198, exact control under `Pre`), and the
factor pair (pcs 1199-1200). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data
open PTX PTX.Proof PTX.Flow PTX.Flow.Code PTX.Flow.Arith32 PTX.Kernels.FlashMlaSparseDecodeH64

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {g : Nat} {w : BitVec 64} {m : Mem0}

/-- The factor pair's run, with the constant it moves into register 1809 kept among its facts. -/
theorem e7S (L : Launch) (g : Nat) (V : Nat → Value) :
    SegD kernel Assumptions.all L g 2 1199 (Gen.e7_facts0 V) 1201
      ((1809, Gen.e7_v1200 V) :: Gen.e7_facts1 V) (Gen.e7_cond V) :=
  SegD.outs_lit (items := Gen.e7_items0)
    ⟨⟨XItem.codeB_of Flow.code_1199 rfl, w0SegFree 1199, rule_move 1199 rfl⟩,
     ⟨XItem.codeB_of Flow.code_1200 rfl, w0SegFree 1200, XItem.core_mov (w0SegFree 1200)
         (noRuleW0 (op := Gen.e7_op1200) 1200 rfl) rfl⟩,
     trivial⟩
    rfl (by kernel_rfl) rfl (by kernel_rfl) (by kernel_rfl)

theorem e7_v1200_eq (V : Nat → Value) (c : Control.D) :
    Gen.e7_v1200 V = Control.valueOf P L g w { c with site := .old 0 } 1809 := by
  simp only [Gen.e7_v1200]
  rfl

/-- From the join (pc 1197) to the first output load, with the factor word `K`. -/
theorem facJoin (hp : Pre P L m) (d : Control.D) (V : Nat → Value) (pe K : Value)
    (c7 : Gen.e7_cond (lookupD [(2956, K)])) :
    ∃ n, Seg kernel Assumptions.all L g n 1197
      ((2956, K) :: (f_ew V pe ++ factsFrom (Control.ctlLive 1197) (Control.valueOf P L g w d)))
      1201 (Control.facts P L g w { d with site := .old 0 } ++
        Gen.e7_facts1 (lookupD [(2956, K)])) := by
  obtain ⟨n1, h1⟩ := Control.facSegS (w := w) hp d
  have h1' := Seg.frameSet (H := (2956, K) :: f_ew V pe) rulesFrame
    (S := [1197, 1198, 1199, 1200]) (by kernel_rfl) (fun _ _ => w0SegFree _) (by kernel_rfl) h1
  have h2 := (SegD.frame (H := factsFrom ((Control.ctlLive 1201).erase 1809)
    (Control.valueOf P L g w d)) rulesFrame (e7S L g (lookupD [(2956, K)])) rfl (by kernel_rfl)
    (by rw [factsFrom_keys]; kernel_rfl) fun _ _ => w0SegFree _).seg c7
  refine ⟨n1 + _, (h1'.weaken_start fun R h => ?_).comp
    ((h2.weaken_start fun R h => ?_).weaken_end fun R h => ?_)⟩
  · obtain ⟨hk, hf, hc⟩ : Holds R [(2956, K)] ∧ Holds R (f_ew V pe) ∧
        Holds R (factsFrom (Control.ctlLive 1197) (Control.valueOf P L g w d)) :=
      ⟨⟨h.1, trivial⟩, ((holds_append _ _ _).mp h.2).1, ((holds_append _ _ _).mp h.2).2⟩
    exact (holds_append _ _ _).mpr ⟨holds_factsFrom_mono hc (by decide +kernel),
      (holds_append _ _ _).mpr ⟨hk, hf⟩⟩
  · obtain ⟨hc, hd⟩ := (holds_append _ _ _).mp h
    refine (holds_append _ _ _).mpr ⟨⟨hd.1, trivial⟩, ?_⟩
    exact holds_factsFrom_mono hc (by decide +kernel)
  · obtain ⟨hw, hc'⟩ := (holds_append _ _ _).mp h
    have h4 := facts_of_erase (P := P) (L := L) (g := g) (w := w)
      (c := { d with site := .old 0 }) (r := 1809) (R := R)
      (by show 1809 ∈ Control.ctlLive 1201; decide +kernel)
      (by rw [← e7_v1200_eq (P := P) (L := L) (g := g) (w := w) _ d]; exact hw.1) hc'
    exact (holds_append _ _ _).mpr ⟨h4, hw.2⟩

/-- The condition of the window after the fence: the zero-sum test, the factor's run on a
non-zero sum, and the pair. -/
def facCond (V : Nat → Value) (pe : Value) : Prop :=
  Gen.e5_cond (lookupD (f_ew V pe)) ∧
    (predOf (Gen.e5_v1189 (lookupD (f_ew V pe))) = false → Gen.e6_cond (lookupD (f_ew V pe))) ∧
    Gen.e7_cond (lookupD [(2956, f_zj V pe)])

/-- **The window after the fence**: from the sum's facts to the first output load. -/
theorem facWin (hp : Pre P L m) (d : Control.D) (hs : d.site = .efa) (V : Nat → Value)
    (pe : Value) (c : facCond V pe) :
    ∃ n, Seg kernel Assumptions.all L g n 1188 (Control.facts P L g w d ++ f_ew V pe) 1201
      (Control.facts P L g w { d with site := .old 0 } ++ f_fac V pe) := by
  let W := lookupD (f_ew V pe)
  let Hc := factsFrom (Control.ctlLive 1197) (Control.valueOf P L g w d)
  obtain ⟨n0, h0⟩ := Control.gridSegS (w := w) (P := P) (L := L) (g := g) d
  have h0' := Seg.frameSet (H := f_ew V pe) rulesFrame (S := [1188, 1189, 1190, 1191, 1192,
    1193, 1194, 1195, 1196, 1197, 1198, 1199, 1200]) (by kernel_rfl) (fun _ _ => w0SegFree _)
    (by kernel_rfl) h0
  have h5 := (SegD.frame (H := f_ew V pe ++ Hc) rulesFrame (Gen.e5_run L g W) rfl
    (by kernel_rfl) (by rw [List.map_append, factsFrom_keys]; kernel_rfl)
    fun _ _ => w0SegFree _).seg c.1
  have hpc : d.site.pc = 1187 := by rw [hs]; rfl
  have pre := (h0'.weaken_start fun R (h : Holds R (Control.facts P L g w d ++ f_ew V pe)) => by
      obtain ⟨hc, hd⟩ := (holds_append _ _ _).mp h
      unfold Control.facts at hc
      rw [hpc] at hc
      exact (holds_append _ _ _).mpr ⟨holds_factsFrom_mono hc (by decide +kernel), hd⟩).comp
    (h5.weaken_start fun R (h : Holds R (factsFrom (Control.ctlLive 1189)
        (Control.valueOf P L g w d) ++ f_ew V pe)) => by
      obtain ⟨hc, hd⟩ := (holds_append _ _ _).mp h
      exact (holds_append _ _ _).mpr ⟨holds_lookupD (live := [482]) hd (by kernel_rfl),
        (holds_append _ _ _).mpr ⟨hd, holds_factsFrom_mono hc (by decide +kernel)⟩⟩)
  obtain ⟨q, hq⟩ : ∃ q, Gen.e5_v1189 W = .pred q := ⟨_, rfl⟩
  have hq' : predOf (Gen.e5_v1189 W) = q := by rw [hq]; rfl
  have h5f : Gen.e5_facts1 W = [(120, .pred q), (2956, Gen.e5_v1190 W)] := by
    unfold Gen.e5_facts1; rw [hq]
  have hz : f_zj V pe = if q then Gen.e5_v1190 W else Gen.e6_v1196 W := by
    unfold f_zj; rw [hq']
  have hF : (120, Value.pred q) ∈ Gen.e5_facts1 W ++ (f_ew V pe ++ Hc) := by
    rw [h5f]; simp
  rw [h5f] at pre
  cases q
  · have hz' : f_zj V pe = Gen.e6_v1196 W := by rw [hz]; rfl
    have h6 := (SegD.frame (H := f_ew V pe ++ Hc) rulesFrame (Gen.e6_run L g W) rfl
      (by kernel_rfl) (by rw [List.map_append, factsFrom_keys]; kernel_rfl)
      fun _ _ => w0SegFree _).seg (c.2.1 hq')
    obtain ⟨n7, h7⟩ := facJoin (w := w) (g := g) hp d V pe (Gen.e6_v1196 W)
      (by rw [← hz']; exact c.2.2)
    refine ⟨_, pre.comp ((Seg.bra (target := 1197) (p := 120) (pick := false) Flow.code_1191
      (by rw [← h5f]; exact hF) (fun t _ a ha => bra_rule t a ha) (w0SegFree 1191)).comp
      ((h6.weaken_start fun R h => ?_).comp
        ((h7.weaken_start fun R h => ?_).weaken_end fun R h => ?_)))⟩
    · obtain ⟨-, -, hr⟩ := h
      have hr' : Holds R (f_ew V pe ++ Hc) := hr
      exact (holds_append _ _ _).mpr ⟨holds_lookupD (live := [481, 482, 2880])
        ((holds_append _ _ _).mp hr').1 (by kernel_rfl), hr'⟩
    · obtain ⟨-, -, -, -, h2956, hr⟩ := h
      exact ⟨h2956, hr⟩
    · simpa only [f_fac, hz'] using h
  · have hz' : f_zj V pe = Gen.e5_v1190 W := by rw [hz]; rfl
    obtain ⟨n7, h7⟩ := facJoin (w := w) (g := g) hp d V pe (Gen.e5_v1190 W)
      (by rw [← hz']; exact c.2.2)
    refine ⟨_, pre.comp ((Seg.bra (target := 1197) (p := 120) (pick := true) Flow.code_1191
      (by rw [← h5f]; exact hF) (fun t _ a ha => bra_rule t a ha) (w0SegFree 1191)).comp
      ((h7.weaken_start fun R h => ?_).weaken_end fun R h => ?_))⟩
    · obtain ⟨-, h2956, hr⟩ := h
      exact ⟨h2956, hr⟩
    · simpa only [f_fac, hz'] using h

/-- **The strict step at pc 1187** (the fence before the zero-sum test). -/
theorem sk_1187 (hp : Pre P L m) (d : D) (hs : d.c.site = .efa) (hok : d.ok = true)
    (hc : facCond (lookupD (f_car (scX L) d.b.m d.b.l d.b.mx d.b.sk)) d.b.pe) (e : Event) :
    (code P L g w).StepFor d e := by
  refine skW_nx (pc := 1187) (pc' := 1201) (by rw [hs]; rfl) rfl
    (c' := { d.c with site := .old 0 }) (b' := d.b) (by rw [hs]; decide)
    (by rw [hs]; exact Flow.code_1187)
    (fun {t e u} hf => by
      rw [hs] at hf
      exact Code.fires_tcPlain_next (.inl rfl) hf) (by rw [hs]; decide) hok
    (fun e => by simp [Control.succ, hs]) (by simp [succOk, hs])
    (fun _ => by simp [record, hs]) (fun h => h)
    (fun h => by simp [Control.elems, h]) ?_ e
  have h := facWin (w := w) (g := g) hp d.c hs _ d.b.pe hc
  have e1 : wF (scX L) d.c.site d.b = f_ew (lookupD (f_car (scX L) d.b.m d.b.l d.b.mx d.b.sk))
      d.b.pe := by rw [hs]; rfl
  rw [e1]
  exact h

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data
