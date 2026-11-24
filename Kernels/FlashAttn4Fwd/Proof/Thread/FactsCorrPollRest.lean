-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsCorrBars
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsCorrOAcc
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsCorrTcAgree
public import Lemmas.Protocol.NamedBarMember
public import Lemmas.Protocol.NamedBarArrive

@[expose] public section

/-! # The correction part of `Cross.PollRest`

Two lanes `g`, `h` of a correction warp poll one position, `g` in an earlier round than `h`.

* At the tail's wait no lane has a successful poll there before (`corr_tail_round0`: such a poll
  leads to the end barrier's arrival, which a tail state has not made), so both rounds are zero.
* At the O-full and staging-free waits of item `i` the round is `i` (`corr_round_item`), so `h` is
  at a later item `i' > i`. Both are past the last sync of stage 0's statistics barrier of their
  items: `g` has made `G = (n + 1) (i + 1)` syncs of it, `h` more. The sync of `h` with ordinal
  `G` is before its poll and passed, so `g` has its sync of ordinal `G` too (every participant of
  a passed generation arrived, `Sources.member_arrival_any`; a lane that exited made all its
  syncs, `Cross.barExit_corr`). That sync of `g` is after its poll, and it is a witness of the
  return of `h`'s sync, which precedes `h`'s poll in the execution-dependency order
  (`arrive_sync_depBefore`).

The barrier's group and sources are a premise (`StatsGroup`: the statistics barriers' shape and
sources, `Stats.shape` and `Stats.sources`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- The group of stage 0's statistics barrier of each correction warp. -/
def StatsGroup (L : Launch) (X : Execution) : Prop :=
  ∀ k < 4, ∃ p : Finset Nat, NamedBar.Shape L (some 64) p (statsId 0 k) ∧
    NamedBar.Sources L X (some 64) p (statsId 0 k) ∧ 8 + k ∈ p

namespace Correction

end Correction

section
variable (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
  (ht : Frame.Tracked (code L) X)
include hpre hX ht

/-- At an O-full or staging-free wait, the round is the item. -/
theorem corr_round_item {g k : Nat} {d : Correction.D} (hw : 8 ≤ warpOf L g)
    (hw' : warpOf L g < 12) (hc : Correction.Counts L g d ((X.tr g).take k))
    (hi : Correction.Inv L g d)
    (hs : d.site = .oWait 0 ∨ d.site = .oWait 1 ∨ d.site = .fWait 0 ∨ d.site = .fWait 1) :
    pollRound d.site.pc ((X.tr g).take k) = d.i := by
  rcases hs with hs | hs | hs | hs
  · rw [hs, corr_round_eq hpre hX ht hw hw' (.inl ⟨rfl, rfl⟩)]
    have := hc.oFull 0 (by decide)
    simp only [Correction.oPos, hs] at this
    simpa using this
  · rw [hs, corr_round_eq hpre hX ht hw hw' (.inr (.inl ⟨rfl, rfl⟩))]
    have := hc.oFull 1 (by decide)
    simp only [Correction.oPos, hs] at this
    simpa using this
  · rw [hs, corr_round_eq hpre hX ht hw hw' (.inr (.inr ⟨rfl, rfl⟩))]
    have := hc.oFree 0 (by decide)
    simp only [Correction.fPos, hs] at this
    simpa using this
  · rw [hs]
    exact corr_round_f1 hpre hX ht hw hw' hc hi hs

/-- At the tail's wait, the thread has no successful poll there before. -/
theorem corr_tail_round0 {g k : Nat} {d : Correction.D} (hw : 8 ≤ warpOf L g)
    (hw' : warpOf L g < 12)
    (hσ : Frame.stateAt (code L) X g k = some (some (.inr (.corr d))))
    (hc : Correction.Counts L g d ((X.tr g).take k)) (hs : d.site = .tailWait)
    (hk : k < (X.tr g).length) :
    pollRound Correction.Site.tailWait.pc ((X.tr g).take k) = 0 := by
  by_contra hne
  obtain ⟨j, hjk, e, hej, hq, -⟩ :=
    exists_nth (okPollAt Correction.Site.tailWait.pc) (X.tr g) (n := 0) (k := k)
      (by unfold pollRound at hne; omega)
  have he : X.get (g, j) = some e := hej
  obtain ⟨epc, ek⟩ := e
  cases ek <;> simp only [okPollAt, Bool.false_eq_true] at hq
  rename_i m p ok acq sc
  cases ok <;> simp only [Bool.false_eq_true, beq_iff_eq] at hq
  subst hq
  obtain ⟨d2, hσ2, -, -, hpc2, hs2⟩ := corr_wait hpre hX ht hw hw' he
  have h2 : d2.site = .tailWait := by
    rcases hs2 with ⟨st, hsd, -⟩ | ⟨st, hsd, -⟩ | ⟨hsd, -⟩
    · exact absurd (corr_wait_pc_inj (s := d2.site) (by fin_cases st <;> simp [hsd])
        (by simp) hpc2) (by rw [hsd]; simp)
    · exact absurd (corr_wait_pc_inj (s := d2.site) (by fin_cases st <;> simp [hsd])
        (by simp) hpc2) (by rw [hsd]; simp)
    · exact hsd
  have hsucc := corr_succ he hσ2
  have hσ3 : Frame.stateAt (code L) X g (j + 1) =
      some (some (.inr (.corr { d2 with site := .barEnd }))) := by
    have : Frame.stateAt (code L) X g (j + 1) = _ := hsucc
    rw [this]
    obtain ⟨site, i, tt, aw, a, o⟩ := d2
    simp only at h2
    subst h2
    rfl
  rcases Nat.lt_or_eq_of_le (Nat.succ_le_of_lt hjk) with hlt | heq
  · obtain ⟨e1, he1⟩ : ∃ e1, X.get (g, j + 1) = some e1 :=
      ⟨_, List.getElem?_eq_getElem (show j + 1 < (X.tr g).length by omega)⟩
    rcases corr_origin hpre hX ht he1 hw hw' (corr_noUb hpre hX hσ3 he1) with
      ⟨p0, hp0, -⟩ | ⟨d4, t, ins, o, hσ4, -, -, -, -, -, hev⟩
    · rw [hσ3] at hp0; cases hp0
    rw [hσ3] at hσ4
    simp only [Option.some.injEq, Sum.inr.injEq, Role.corr.injEq] at hσ4
    subst hσ4
    obtain ⟨epc1, ek1⟩ := e1
    have hk1 : ek1 = .bar 2 (some 416) .arrive := by
      by_cases hx : ek1 = .exit
      · subst hx
        obtain ⟨d5, hσ5, -, -, hs5⟩ := corr_exit_state hpre hX ht hw hw' he1
        rw [hσ3] at hσ5
        simp only [Option.some.injEq, Sum.inr.injEq, Role.corr.injEq] at hσ5
        rw [← hσ5] at hs5
        cases hs5
      · exact (hev hx).2
    subst hk1
    have h2a := hc.bar2.2
    simp only [Correction.bar2Arrive, hs] at h2a
    have hpos : 0 < barEvents 2 416 .arrive ((X.tr g).take k) := by
      unfold barEvents
      refine List.countP_pos_iff.mpr ⟨⟨epc1, .bar 2 (some 416) .arrive⟩, ?_, by simp [barIs]⟩
      exact List.mem_iff_getElem?.mpr ⟨j + 1, by rw [List.getElem?_take]; simp [hlt]; exact he1⟩
    omega
  · subst heq
    rw [hσ3] at hσ
    simp only [Option.some.injEq, Sum.inr.injEq, Role.corr.injEq] at hσ
    rw [← hσ] at hs
    cases hs

omit hpre hX ht in
/-- **`bar.arrive` → `bar.sync` dependency.** An arrival of either form of one thread and a
passed `bar.sync` of another thread of the same CTA with the same ordinal: the arrival is a witness
of the `bar.sync`'s return (`Witness.of_ctaBarCounted`), which precedes the later events of its
thread. -/
theorem arrive_sync_depBefore {K : Kernel} {A : List Assumption} {count : Option Nat}
    {p : Finset Nat} {id : Nat} (hX : Consistent L K A mem0 X)
    (hS : NamedBar.Sources L X count p id) (hG : NamedBar.Shape L count p id)
    {g h i j after pc pc' : Nat} {cnt cnt' : Option Nat} {m : BarMode}
    (hsame : SameCta L g h) (he : X.get (g, i) = some ⟨pc, .bar id cnt m⟩)
    (hf : X.IsBarrier (h, j) id cnt' pc') (hpassed : j + 1 < (X.tr h).length)
    (hordinal : ((X.tr g).take i).countP (Execution.isBarId id) =
      ((X.tr h).take j).countP (Execution.isBarId id))
    (hafter : j < after) (hlen : after < (X.tr h).length) :
    DepBefore L K X (g, i) (h, after) := by
  have hke := hS.arrive_key_of_credit hX hG he hsame.1 hsame.2.2.symm hf hpassed
    hordinal.symm
  obtain ⟨key, hkf, hdone⟩ := ctaBarDone_of_returned hX hf hpassed
  have hkey := hS.arrival_key hX hG hf (CtaBarK.arrival hkf)
  simp only at hkey hke
  rw [hkey, ← hordinal] at hkf hdone
  obtain ⟨ic, hc⟩ := hdone
  have hw := Witness.of_ctaBarCounted hkf hc hke hsame.2.2
  exact .tail (.single (.inl (DepStep.of_witness L hw)))
    (.inl (DepStep.of_resumes L (Resumes.of_blocking (b := false) hf rfl ⟨rfl, hafter, hlen⟩)))

/-- **The correction part of `Cross.PollRest`**: two lanes of a correction warp polling at one
position in different rounds are ordered through stage 0's statistics barrier. -/
theorem Cross.PollRest_corr (hgrp : StatsGroup L X) {g h k k' pc p p' : Nat} {m m' : Loc}
    {ok ok' acq acq' : Bool} {sc sc' : MbarScope} (hw : 8 ≤ warpOf L g)
    (hw' : warpOf L g < 12) (hs : SameWarp L g h)
    (he : X.get (g, k) = some ⟨pc, .wait m p ok acq sc⟩)
    (he' : X.get (h, k') = some ⟨pc, .wait m' p' ok' acq' sc'⟩)
    (hr : pollRound pc ((X.tr g).take k) < pollRound pc ((X.tr h).take k')) :
    ∃ a, k < a ∧ DepBefore L kernel X (g, a) (h, k') := by
  have hwh : warpOf L h = warpOf L g := hs.2.symm
  have hk' : k' < (X.tr h).length := (List.getElem?_eq_some_iff.mp he').1
  obtain ⟨d, hσ, hc, hi, hpc, hsd⟩ := corr_wait hpre hX ht hw hw' he
  obtain ⟨d', hσ', hc', hi', hpc', hsd'⟩ := corr_wait hpre hX ht (by omega) (by omega) he'
  have h5 : ∀ {d : Correction.D}, ((∃ st : Fin 2, d.site = .oWait st ∧ True) ∨
      (∃ st : Fin 2, d.site = .fWait st ∧ True) ∨ d.site = .tailWait) →
      d.site = .oWait 0 ∨ d.site = .oWait 1 ∨ d.site = .fWait 0 ∨ d.site = .fWait 1 ∨
        d.site = .tailWait := by
    intro d hd
    rcases hd with ⟨st, hsd, -⟩ | ⟨st, hsd, -⟩ | hsd <;> (try fin_cases st) <;> simp [hsd]
  have hs5 := h5 (by
    rcases hsd with ⟨st, hsd, -⟩ | ⟨st, hsd, -⟩ | ⟨hsd, -⟩
    · exact .inl ⟨st, hsd, trivial⟩
    · exact .inr (.inl ⟨st, hsd, trivial⟩)
    · exact .inr (.inr hsd))
  have hs5' := h5 (d := d') (by
    rcases hsd' with ⟨st, hsd, -⟩ | ⟨st, hsd, -⟩ | ⟨hsd, -⟩
    · exact .inl ⟨st, hsd, trivial⟩
    · exact .inr (.inl ⟨st, hsd, trivial⟩)
    · exact .inr (.inr hsd))
  have hss := corr_wait_pc_inj hs5 hs5' (hpc.trans hpc'.symm)
  -- the tail: both rounds are zero
  by_cases htl : d.site = .tailWait
  · have := corr_tail_round0 hpre hX ht (g := h) (by omega) (by omega) hσ' hc' (hss ▸ htl) hk'
    rw [← hpc', ← hss, htl] at hr
    omega
  have hs4 : d.site = .oWait 0 ∨ d.site = .oWait 1 ∨ d.site = .fWait 0 ∨ d.site = .fWait 1 := by
    rcases hs5 with h | h | h | h | h
    exacts [.inl h, .inr (.inl h), .inr (.inr (.inl h)), .inr (.inr (.inr h)), absurd h htl]
  have r1 := corr_round_item hpre hX ht hw hw' hc hi hs4
  have r2 := corr_round_item hpre hX ht (g := h) (by omega) (by omega) hc' hi' (hss ▸ hs4)
  rw [← hpc, hss] at hr
  rw [hss] at r1
  rw [r1, r2] at hr
  -- the syncs of stage 0's statistics barrier
  have hitem : d'.i < Correction.items L h := hi'.item (by rcases hss ▸ hs4 with h | h | h | h <;>
    rw [h] <;> rfl)
  have hitems : Correction.items L h = Correction.items L g := (corr_items_eq hs).symm
  set n := Correction.trips L with hn
  set id := statsId 0 (warpOf L g - 8) with hid
  have hid2 : id ≠ 2 := by simp only [hid, statsId]; omega
  have hkg := corr_kOf hw hw'
  have hkh := corr_kOf (g := h) (show 8 ≤ warpOf L h by omega) (show warpOf L h < 12 by omega)
  have hsp : ∀ {d : Correction.D}, (d.site = .oWait 0 ∨ d.site = .oWait 1 ∨ d.site = .fWait 0 ∨
      d.site = .fWait 1) → Correction.syncPos L 0 d = n + 1 := by
    intro d hd
    rcases hd with h | h | h | h <;> simp [Correction.syncPos, h, hn]
  have hG : barOrd X g k id = (n + 1) * (d.i + 1) := by
    rw [corr_barOrd hpre hX ht hw hw' k hid2,
      show id = Correction.kOf L g + 3 + 4 * 0 by simp only [hid, statsId]; omega,
      hc.sync 0 (by decide), hsp hs4]
    ring
  have hG' : barOrd X h k' id = (n + 1) * (d'.i + 1) := by
    rw [corr_barOrd hpre hX ht (by omega) (by omega) k' hid2,
      show id = Correction.kOf L h + 3 + 4 * 0 by simp only [hid, statsId]; omega,
      hc'.sync 0 (by decide), hsp (hss ▸ hs4)]
    ring
  have hlt : (n + 1) * (d.i + 1) < (n + 1) * (d'.i + 1) :=
    Nat.mul_lt_mul_of_pos_left (by omega) (by omega)
  -- `h`'s sync of ordinal `G`, before its poll
  obtain ⟨x, hxk, ev, hev, hq, hcnt⟩ := exists_nth (Execution.isBarId id) (X.tr h)
    (n := (n + 1) * (d.i + 1)) (k := k') (by unfold barOrd at hG'; omega)
  have hxe : X.get (h, x) = some ev := hev
  obtain ⟨xpc, xk⟩ := ev
  cases xk <;> simp only [Execution.isBarId, Bool.false_eq_true] at hq
  rename_i xid xcnt xm
  simp only [beq_iff_eq] at hq
  subst hq
  obtain ⟨h2, -⟩ | ⟨rfl, rfl, -⟩ := corr_bar hpre hX ht (g := h) (show 8 ≤ warpOf L h by omega)
    (show warpOf L h < 12 by omega) hxe
  · exact absurd h2 hid2
  obtain ⟨pp, hshape, hsrc, hmem⟩ := hgrp (warpOf L g - 8) (by omega)
  rw [← hid] at hshape hsrc
  have hxb : X.IsBarrier (h, x) id (some 64) xpc := hxe
  have hpassed : x + 1 < (X.tr h).length := by omega
  have hcta : g / L.block = h / L.block := hs.1.2.2
  have hwp : (g % L.block) / 32 ∈ pp := by
    have : (g % L.block) / 32 = 8 + (warpOf L g - 8) := by simp only [warpOf] at hw ⊢; omega
    rw [this]; exact hmem
  -- `g`'s sync of ordinal `G`
  obtain ⟨ig, pcg, mg, hgig, hcg⟩ := NamedBar.Sources.member_arrival_any hX hsrc hshape hxb
    hpassed hcta hwp (fun ⟨j, pcx, hex⟩ => by
      have htot := (Cross.barExit_corr hpre hX ht hw hw' hex).2 0 (by decide)
      have hlt2 : (n + 1) * (d.i + 1) < (X.tr g).countP (Execution.isBarId id) := by
        rw [htot, ← hitems]
        exact Nat.mul_lt_mul_of_pos_left (by omega) (by omega)
      obtain ⟨y, -, ey, hey, hqy, hcy⟩ := exists_nth (Execution.isBarId id) (X.tr g)
        (n := (n + 1) * (d.i + 1)) (k := (X.tr g).length) (by rw [List.take_length]; exact hlt2)
      have hye : X.get (g, y) = some ey := hey
      obtain ⟨ypc, yk⟩ := ey
      cases yk <;> simp only [Execution.isBarId, Bool.false_eq_true] at hqy
      rename_i yid ycnt ym
      simp only [beq_iff_eq] at hqy
      subst hqy
      obtain ⟨h2, -⟩ | ⟨rfl, -, -⟩ := corr_bar hpre hX ht hw hw' hye
      · exact absurd h2 hid2
      exact ⟨y, ypc, ym, hye, by rw [hcy]; exact hcnt.symm⟩)
  obtain ⟨h2, -⟩ | ⟨-, hmg, -⟩ := corr_bar hpre hX ht hw hw' hgig
  · exact absurd h2 hid2
  subst hmg
  simp only at hcg
  rw [hcnt] at hcg
  -- it is after the poll
  have hkig : k < ig := by
    rcases Nat.lt_or_ge ig k with h1 | h1
    · have a1 := countP_take_succ (p := Execution.isBarId id) hgig (by simp [Execution.isBarId])
      have a2 := countP_take_mono (Execution.isBarId id) (X.tr g) (show ig + 1 ≤ k by omega)
      unfold barOrd at hG
      omega
    rcases Nat.lt_or_eq_of_le h1 with h2 | h2
    · exact h2
    · subst h2
      rw [he] at hgig
      cases hgig
  exact ⟨ig, by omega, arrive_sync_depBefore hX hsrc hshape hs.1 hgig hxb hpassed
    (by rw [hcg]; exact hcnt.symm) hxk hk'⟩

end

end
end PTX.Kernels.FlashAttn4Fwd.Proof
