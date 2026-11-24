-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Result.QySmOLoad
public import Kernels.InklingRelDecode.Proof.Interface.Lk5VChain

@[expose] public section

/-!
# The exchange of the row maximum receives score words (`Interface.Lk.SmMaxOk`)

The softmax machine follows every word the exchange of the row maximum returns (`Sm.next shfl5`):
on score words it records the real numbers (`Sm.D.afterMax`), on other words Core's outcomes
(`Sm.D.afterMaxT`, clearing the flag `Stg.re`). `smMaxOk_of`: on every consistent execution the
first case holds at every followed exchange:

* the 64 words of the columns are score words: the state before is the wait for the S load, whose
  words are the S load's, `f32` numbers (`ldS_words`); the words at the exchange are the score
  stage's words of them (`Sm.finT_eq`), score words (`Sm.fin_ScOk`) (`fsv_ok`);
* the received word is the partner lane's maximum (`Lk.sm_shfl_peer_d`), the value of the maximum
  of its score words, a score word (`recv_ok`);
* the running maximum is a score word: the thread's invariant gives it where the flag is set
  (`Sm.Inv`, `Sm.RealSt.m`), and the flag is set at every state, by induction along the thread:
  only the exchange on other words clears it (`Sm.re_next`), and the exchanges before received
  score words (`re_all`).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Qy
open PTX PTX.Proof PTX.Flow TcMma PTX.Kernels.InklingRelDecode.Proof
open PTX.Kernels.InklingRelDecode.Proof.Sr
open PTX.Kernels.InklingRelDecode.Proof.Interface (St ThreadFacts)
open PTX.Kernels.InklingRelDecode.Proof.Interface.Lk (DecAgree)

noncomputable section

/-- **Only `waitLd` leads to `shfl5`**, where the score stage's first half records the words. -/
theorem prev_shfl5 {L : Launch} {g : Nat} {d d' : Sm.D} {e : Event}
    (hn : Sm.next L g d e = some (some d')) (h : d'.site = .shfl5) :
    d.site = .waitLd ∧ d' = { d with site := .shfl5, stg := { d.stg with fsv := Sm.D.finT L g d } }
    := by
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

/-- **The words of the columns at a followed exchange of the row maximum are score words.** -/
theorem fsv_ok (hres : Qx.ResultQk Q L X) {g k : Nat} {d : Sm.D} (hg : g < L.threads)
    (hk : k ≤ (X.tr g).length) (hσ : St Q L X g k = some (some (.d (.sm d))))
    (hs : d.site = .shfl5) : ∀ j < 64, Sm.ScoreWord (d.stg.fsv j).1 := by
  rcases Sv.pred_sm hk hσ with ⟨dt, rfl⟩ | ⟨k0, d0, e, rfl, he, hσ0, hnx⟩
  · simp [SmEntry.d0] at hs
  obtain ⟨hs0, rfl⟩ := prev_shfl5 hnx hs
  rcases Sv.pred_sm (by omega) hσ0 with ⟨dt, rfl⟩ | ⟨k1, d1, e1, rfl, he1, hσ1, hnx1⟩
  · simp [SmEntry.d0] at hs0
  obtain ⟨hs1, a, vals, sh, hv, hke, rfl⟩ := prev_waitLd hnx1 hs0
  obtain ⟨pc, kd⟩ := e1
  simp only at hke
  subst hke
  have he1' : X.get (g, k1) = some ⟨pc, .tc (.ld a vals sh)⟩ := he1
  have hw := ldS_words hpre hX hf hR hb hn hnc hns G hG st ht hl hz hD hMB hres hg hσ1 hs1 he1'
  have hS : ∀ j < 64, ∃ x, ((Sm.svOf vals hv.2) j).1 = .float .f32 x := by
    intro j hj
    obtain ⟨x, hx⟩ := hw j hj
    refine ⟨x, ?_⟩
    have hj' : j < vals.length := by rw [hv.1]; exact hj
    simp only [Sm.svOf, hj', ↓reduceDIte]
    rw [List.getElem?_eq_getElem hj'] at hx
    exact Option.some.inj hx
  intro j hj
  show Sm.ScoreWord ((Sm.D.finT L g { d1 with site := .waitLd, sv := Sm.svOf vals hv.2 }) j).1
  rw [Sm.finT_eq (L := L) (g := g) hS]
  exact Sm.fin_ScOk (L := L) (g := g) hS j hj

/-- **The word a followed exchange of the row maximum receives is a score word**: the partner's
maximum of its score words. -/
theorem recv_ok (hres : Qx.ResultQk Q L X) {g k : Nat} {d : Sm.D} {e : Event}
    (hg : g < L.threads) (he : X.get (g, k) = some e)
    (hσ : St Q L X g k = some (some (.d (.sm d)))) (hs : d.site = .shfl5)
    {m : ShflMode} {av : Value} {bv cv : Nat} {r : Value} {o : Bool}
    (hke : e.kind = .shfl m av bv cv r o) :
    Sm.ScoreWord r := by
  obtain ⟨recv, ok, x, j, d2, he', hw, -, hσ2, hs2, -, hrecv, -, hj, -⟩ :=
    Interface.Lk.sm_shfl_peer_d hpre hX hf hpre.block
      (fld := fun d => Sm.ownV fun k => (d.stg.fsv k).1) (k := 16)
      (by rw [hs]; exact Interface.Lk.shflShape_5 L) hg he hσ
  have hr : r = recv := by
    rw [he'] at hke
    exact (Interface.Lk.shflKind_recv hke).symm
  subst hr
  have hw2 := fsv_ok hpre hX hf hR hb hn hnc hns G hG st ht hl hz hD hMB hres hw.1.2.1 hj hσ2
    (hs2.trans hs)
  rw [hrecv]
  show Sm.ScoreWord (Sm.ownV fun k => (d2.stg.fsv k).1)
  rw [Sm.ownV_fsv hw2]
  exact Sm.scoreWord_erealValue (lt_top_iff_ne_top.mp (Sm.cmaxW_lt_top hw2 _))

/-- **The flag of the real numbers is set at every softmax state of a thread.** -/
theorem re_all (hres : Qx.ResultQk Q L X) {g k : Nat} {d : Sm.D} (hg : g < L.threads)
    (hk : k ≤ (X.tr g).length) (hσ : St Q L X g k = some (some (.d (.sm d)))) :
    d.stg.re = true := by
  induction k using Nat.strong_induction_on generalizing d with
  | _ k ih =>
    rcases Sv.pred_sm hk hσ with ⟨dt, rfl⟩ | ⟨k0, d0, e, rfl, he, hσ0, hnx⟩
    · rfl
    have he' : X.get (g, k0) = some e := he
    have hre0 := ih k0 (by omega) (by omega) hσ0
    rw [Sm.re_next hnx (fun h5 m av bv cv r o hke => ?_)]
    · exact hre0
    have hI : Sm.Inv L g d0 := by
      obtain ⟨t, ins, o', -, hinv, -, -⟩ := Frame.fired_site hf.sound hX he' hσ0
      exact hinv.2
    exact ⟨(hI.re hre0).m, recv_ok hpre hX hf hR hb hn hnc hns G hG st ht hl hz hD hMB hres hg he'
      hσ0 h5 hke, fsv_ok hpre hX hf hR hb hn hnc hns G hG st ht hl hz hD hMB hres hg (by omega)
      hσ0 h5⟩

/-- **`Interface.Lk.SmMaxOk`**: every followed exchange of the row maximum receives score words,
with score words of its own and a running maximum that is a score word. -/
theorem smMaxOk_of (hres : Qx.ResultQk Q L X) : Interface.Lk.SmMaxOk Q L X := by
  intro g k d e hg he hσ hs m av bv cv r o hke
  have hk : k ≤ (X.tr g).length := Interface.event_le he
  have hI : Sm.Inv L g d := by
    obtain ⟨t, ins, o', -, hinv, -, -⟩ := Frame.fired_site hf.sound hX he hσ
    exact hinv.2
  exact ⟨(hI.re (re_all hpre hX hf hR hb hn hnc hns G hG st ht hl hz hD hMB hres hg hk hσ)).m,
    recv_ok hpre hX hf hR hb hn hnc hns G hG st ht hl hz hD hMB hres hg he hσ hs hke,
    fsv_ok hpre hX hf hR hb hn hnc hns G hG st ht hl hz hD hMB hres hg hk hσ hs⟩

end
end PTX.Kernels.InklingRelDecode.Proof.Qy
