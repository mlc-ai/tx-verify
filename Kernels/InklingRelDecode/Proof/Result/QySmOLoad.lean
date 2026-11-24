-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Result.QyLoad
public import Kernels.InklingRelDecode.Proof.Interface.SwStO
public import Kernels.InklingRelDecode.Proof.Result.QxQk

@[expose] public section

/-!
# The checks of the S load and the rescale load (`Interface.Lk.SmSLoadOk`, `SmOLoadOk`)

The softmax machine follows every word the rescale load returns (`Sm.next ldO`) and is dead
(`none`) at the wait after it where a product by `alpha` faults (`Sm.D.owOk`). `smOLoad_of`: on
every consistent execution no followed `waitLdO` state has such a word. The state before it is
the load's (`Sv.prev_waitLdO`); the load's read source of each register is the PV MMA at step 7 of
the iteration (`oLoadSrcF`), whose result at the cell is an `f32` number (`Qx.ResultF32`,
`Qx.ldSource_result`), and the register holds it (`TcMma.LoadReadOk`). `alpha` reads as the real
`alr` (`Sm.RealSt.al`, by `Sm.Inv.re` and `Interface.Lk.SmReal`), so each product is the `f32`
number `alr · x` (`Sm.mulE_alpha`).

The machine is also dead (`none`) at the S load where a word it returned is not four bytes.
`smSLoad_of`: no followed `ldS` state has such a word; the load's read source of each register is
the QK MMA at step 7 of the iteration (`sLoadSrcF`), whose result at the cell is an `f32` number.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Qy
open PTX PTX.Proof PTX.Flow TcMma PTX.Kernels.InklingRelDecode.Proof
open PTX.Kernels.InklingRelDecode.Proof.Sr
open PTX.Kernels.InklingRelDecode.Proof.Interface (St ThreadFacts)
open PTX.Kernels.InklingRelDecode.Proof.Interface.Lk (DecAgree)

noncomputable section

/-- **Only `ldS` leads to `waitLd`**, by the load's event, which puts its words into `sv`. -/
theorem prev_waitLd {L : Launch} {g : Nat} {d d' : Sm.D} {e : Event}
    (hn : Sm.next L g d e = some (some d')) (h : d'.site = .waitLd) :
    d.site = .ldS ∧ ∃ (a : Nat) (vals : List Value) (sh : TcShape)
      (hv : vals.length = 64 ∧ ∀ x ∈ vals, x.bytes = 4),
      e.kind = .tc (.ld a vals sh) ∧ d' = { d with site := .waitLd, sv := Sm.svOf vals hv.2 } := by
  unfold Sm.next at hn
  repeat' split at hn
  all_goals first
    | (simp only [Option.some.injEq, reduceCtorEq] at hn; done)
    | (simp only [Option.some.injEq] at hn; subst hn; simp_all; done)
    | (simp only [Option.some.injEq] at hn; subst hn; simp [Sm.D.afterSum] at h)
    | (have := Sv.afterSetup_site hn; rcases this with h' | h' <;> simp_all)
    | (have := Sv.toBar20_site hn; simp_all)

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

variable (hpre : Pre Q L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
  (hf : ThreadFacts Q L mem0 X) (hR : Interface.RoleReads L X)
  (hb : Interface.BaseWordRead L X) (hn : Interface.NumWordRead Q L X)
  (hnc : ∀ e cp, ¬ X.CpIssue e cp) (hns : ∀ e s, ¬ X.ShiftIssue e s)
  (G : SrPkg L kernel Assumptions.all mem0 X) (hG : ∀ c, G.p0 c = Hs.p0Of L c)
  (st : Pr.MmaStates Q L G) (ht : Tmem1.Tmem1Facts L X 0) (hl : SO.TmemLife L X)
  (hz : Rs.SmBaseZero Q L X) (hD : ∀ c j, DecAgree Q L X c j) (hMB : Mma.MmaBcast L X)
include hpre hX hf hR hb hn hnc hns G hG st ht hl hz hD hMB

/-- **The words of the rescale load are `f32` numbers**: at a softmax state at `ldO` whose load
event returned `vals`, each of the 64 words is an `f32` number. -/
theorem ldO_words (hres : Qx.ResultF32 L X) {g k pc a : Nat} {d : Sm.D} {vals : List Value}
    {sh : TcShape} (hg : g < L.threads) (hσ : St Q L X g k = some (some (.d (.sm d))))
    (hs : d.site = .ldO) (he : X.get (g, k) = some ⟨pc, .tc (.ld a vals sh)⟩) :
    ∀ j < 64, ∃ x : ℝ, vals[j]? = some (.float .f32 x) := by
  obtain ⟨hsh, hlen, -⟩ := Interface.Lk.tcld_event hpre hX hf hg he
  subst hsh
  obtain ⟨m, pcm, dst, sp, acc, mask, dm, P, hml, -, hem, -, -, -, hrs⟩ :=
    oLoadSrcF hpre hX hf hR hb hn hnc hns G hG st ht hl hz hD hMB hg hσ hs he
  intro j hj
  obtain ⟨x, hx⟩ := Qx.ldSource_result hX hres hml hem he (hrs j hj)
  have hLC : LoadCell L X (g, k) j (tcDataCell L g (.s16x32bx2 64) a j) :=
    ⟨a, vals, .s16x32bx2 64, ⟨pc, he⟩, by omega, rfl⟩
  obtain ⟨word, hword, hwc2⟩ :=
    hX.tcRead.1 (g, k) _ _ _ j m _ _ ⟨pc, he⟩ hLC (hrs j hj) (.inl hx)
  rcases hwc2 with ⟨-, rfl⟩ | ⟨hb2, -⟩
  · exact ⟨x, hword⟩
  · simp [Value.bytes, FloatFmt.bytes] at hb2

/-- **The words of the S load are `f32` numbers**: at a softmax state at `ldS` whose load event
returned `vals`, each of the 64 words is an `f32` number (the load's read source of each register
is the QK MMA at step 7 of the iteration, `sLoadSrcF`, whose result there is an `f32` number). -/
theorem ldS_words (hres : Qx.ResultQk Q L X) {g k pc a : Nat} {d : Sm.D} {vals : List Value}
    {sh : TcShape} (hg : g < L.threads) (hσ : St Q L X g k = some (some (.d (.sm d))))
    (hs : d.site = .ldS) (he : X.get (g, k) = some ⟨pc, .tc (.ld a vals sh)⟩) :
    ∀ j < 64, ∃ x : ℝ, vals[j]? = some (.float .f32 x) := by
  obtain ⟨hsh, hlen, -⟩ := Interface.Lk.tcld_event hpre hX hf hg he
  subst hsh
  obtain ⟨m, pcm, dst, sp, acc, mask, dm, P, hml, -, hem, hσm, hsm, -, -, hrs⟩ :=
    sLoadSrcF hpre hX hf hR hb hn hnc hns G hG st ht hl hz hD hMB hg hσ hs he
  intro j hj
  obtain ⟨x, hx⟩ := Qx.ldSource_result_at hX
    (fun he1 hd1 _ _ _ hw1 => hres m.2 hml he1 hσm hsm hd1 hw1) hem he (hrs j hj)
  have hLC : LoadCell L X (g, k) j (tcDataCell L g (.s16x32bx2 64) a j) :=
    ⟨a, vals, .s16x32bx2 64, ⟨pc, he⟩, by omega, rfl⟩
  obtain ⟨word, hword, hwc2⟩ :=
    hX.tcRead.1 (g, k) _ _ _ j m _ _ ⟨pc, he⟩ hLC (hrs j hj) (.inl hx)
  rcases hwc2 with ⟨-, rfl⟩ | ⟨hb2, -⟩
  · exact ⟨x, hword⟩
  · simp [Value.bytes, FloatFmt.bytes] at hb2

/-- **`Interface.Lk.SmSLoadOk`**: at a followed `ldS` every word the load returned has four
bytes. -/
theorem smSLoad_of (hres : Qx.ResultF32 L X) : Interface.Lk.SmSLoadOk Q L X := by
  intro g k pc a d vals sh hg hσ hs he x hx
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hx
  obtain ⟨-, hlen, -⟩ := Interface.Lk.tcld_event hpre hX hf hg he
  obtain ⟨y, hy⟩ := ldS_words hpre hX hf hR hb hn hnc hns G hG st ht hl hz hD hMB
    (Qx.resultQk_of_f32 hres) hg hσ hs he j (by omega)
  rw [List.getElem?_eq_getElem hj] at hy
  rw [Option.some.inj hy]
  rfl

/-- **`Interface.Lk.SmScoreOk`**: at a followed `waitLd` no instruction of the score stage's first
half faults: the S words are `f32` numbers (`ldS_words`), so the stage's outcomes are its numbers
(`Sm.s1Ok_real`). -/
theorem smScore_of (hres : Qx.ResultF32 L X) : Interface.Lk.SmScoreOk Q L X := by
  intro g k d hg hk hσ hs
  rcases Sv.pred_sm hk hσ with ⟨dt, rfl⟩ | ⟨k0, d0, e, rfl, he, hσ0, hnx⟩
  · simp [SmEntry.d0] at hs
  obtain ⟨hs0, a, vals, sh, hv, hke, rfl⟩ := prev_waitLd hnx hs
  obtain ⟨pc, kd⟩ := e
  simp only at hke
  subst hke
  have he' : X.get (g, k0) = some ⟨pc, .tc (.ld a vals sh)⟩ := he
  have hw := ldS_words hpre hX hf hR hb hn hnc hns G hG st ht hl hz hD hMB
    (Qx.resultQk_of_f32 hres) hg hσ0 hs0 he'
  refine Sm.s1Ok_real fun j hj => ?_
  obtain ⟨x, hx⟩ := hw j hj
  refine ⟨x, ?_⟩
  show (Sm.svOf vals hv.2 j).1 = _
  have hj' : j < vals.length := by rw [hv.1]; exact hj
  simp only [Sm.svOf, hj', ↓reduceDIte]
  rw [List.getElem?_eq_getElem hj'] at hx
  exact Option.some.inj hx

/-- **`Interface.Lk.SmOLoadOk`**: no followed `waitLdO` state has a product that faults. -/
theorem smOLoad_of (hres : Qx.ResultF32 L X) : Interface.Lk.SmOLoadOk Q L X := by
  intro g k d hg hk hσ hs
  rcases Sv.pred_sm hk hσ with ⟨dt, rfl⟩ | ⟨k0, d0, e, rfl, he, hσ0, hnx⟩
  · simp [SmEntry.d0] at hs
  obtain ⟨hs0, a, vals, sh, hke, rfl⟩ := Sv.prev_waitLdO hnx hs
  obtain ⟨pc, kd⟩ := e
  simp only at hke
  subst hke
  have he' : X.get (g, k0) = some ⟨pc, .tc (.ld a vals sh)⟩ := he
  have hIv : Sm.Inv L g d0 := by
    obtain ⟨t, ins, o, -, hinv, -, -⟩ := Frame.fired_site hf.sound hX he' hσ0
    exact hinv.2
  have hw := ldO_words hpre hX hf hR hb hn hnc hns G hG st ht hl hz hD hMB hres hg hσ0 hs0 he'
  intro j hj
  obtain ⟨x, hx⟩ := hw j hj
  show (mulE false d0.stg.al (vals.getD j (b32 0))).toBool = true
  rw [List.getD_eq_getElem?_getD, hx, Option.getD_some,
    Sm.mulE_alpha hIv.four.al]
  rfl

end
end PTX.Kernels.InklingRelDecode.Proof.Qy
