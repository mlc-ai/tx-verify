-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsCorrSync
public import Kernels.FlashAttn4Fwd.Proof.Interface.TmemRoute
public import Lemmas.Flow.NthEv
public import Lemmas.Flow.Final
public import Lemmas.Flow.ElemAccess
public import Lemmas.Flow.CountTake
public import Kernels.FlashAttn4Fwd.Proof.Interface.OAcc

@[expose] public section

/-! # The correction warps' Tensor Memory loads and the routes of their credits

A correction thread's `tcgen05.ld` is a rescale load (`rld st j`) or a final load (`fld st j`)
of sixteen columns `256 + 128 st + 16 j …` of its warp's lanes, its `tcgen05.st` a rescale store
(`rst st j`) of the same sixteen columns (`corr_tld`, `corr_tst`). The P-ready arrivals of stage
`st` number the credits: the first one, one per loop trip after the stage's rescale, one per item
after its final part (`Counts.free`). A rescale of trip `t` of item `I` follows the stage's
statistics sync of ordinal `(n + 1) I + 1 + t` (`Counts.sync`), a final part of item `I` its
`I + 1`-th successful O-full poll of the stage (`Counts.oFull`); the routes `CorrSync` and
`CorrFinal` name those events (`exists_nthEv`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Proof PTX.Flow TcMma

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- The instruction at `pc` is a `tcgen05.st` of `n` sources. -/
def tcStLen (pc n : Nat) : Bool :=
  match kernel.code[pc]? with
  | some ⟨none, .tcSt _ ss⟩ => ss.length == n
  | _ => false

theorem tcStLen_spec {pc n : Nat} (h : tcStLen pc n = true) :
    ∃ ta ss, kernel.code[pc]? = some ⟨none, .tcSt ta ss⟩ ∧ ss.length = n := by
  unfold tcStLen at h
  split at h
  · rename_i ta ss hc
    exact ⟨ta, ss, hc, by simpa using h⟩
  · cases h

set_option maxHeartbeats 4000000 in
theorem rst_len (st : Fin 2) (j : Fin 8) : tcStLen (Correction.Site.rst st j).pc 16 = true := by
  simp only [Correction.Site.pc]
  fin_cases st <;> fin_cases j <;> decide +kernel

/-- The column of a cell at Tensor Memory address `tmem L g col`, word `p`. -/
theorem tmem_column (L : Launch) (g h col p : Nat) (hc : col < 512) :
    (tcDataCell32 L h (Correction.tmem L g col) p).column = col + p := by
  simp only [tcDataCell32, Correction.tmem]
  omega


/-- Stage `st`'s P-ready barrier of the pair's leader is the correction's leader barrier. -/
theorem pReadyBar_lead (L : Launch) (g st : Nat) :
    pReadyBar L (leadCta (ctaOf L g)) st = Correction.leadLoc L g (144 + 8 * st) := by
  simp only [pReadyBar, leadCta, Correction.leadLoc, Correction.sb, Nat.mul_comm]

theorem oFullBar_own (L : Launch) (g st : Nat) :
    oFullBar L (ctaOf L g) st = Correction.ownLoc L g (192 + 8 * st) := by
  simp only [oFullBar, Correction.ownLoc, Correction.sb]

theorem kvTiles_eq (L : Launch) : kvTiles L = Correction.trips L := rfl

/-- The statistics sync of stage `st` with `c` earlier ones, when there are more than `c`. -/
theorem corr_sync_nth {g i c : Nat} (st : Nat) (hw : 8 ≤ warpOf L g) (hw' : warpOf L g < 12)
    (h : c + 1 ≤ barEvents (Correction.kOf L g + 3 + 4 * st) 64 .sync ((X.tr g).take i)) :
    ∃ y pc, y < i ∧
      X.get (g, y) = some ⟨pc, .bar (statsId st (warpOf L g - 8)) (some 64) .sync⟩ ∧
      barEvents (Correction.kOf L g + 3 + 4 * st) 64 .sync ((X.tr g).take y) = c := by
  obtain ⟨y, e, hy, he, hp, hc⟩ := exists_nthEv (X := X) (g := g) h
  refine ⟨y, e.pc, hy, ?_, hc⟩
  have hkw := corr_kOf hw hw'
  obtain ⟨epc, k⟩ := e
  cases k <;> simp only [barIs, Bool.false_eq_true] at hp
  rename_i id cnt m
  cases cnt <;> simp only [Bool.false_eq_true, decide_eq_true_eq] at hp
  obtain ⟨rfl, rfl, rfl⟩ := hp
  rw [he]
  simp only [statsId, Option.some.injEq, Event.mk.injEq, Kind.bar.injEq, and_true, true_and]
  omega

/-- The successful poll of `m` with `c` earlier ones, when there are more than `c`. -/
theorem okPoll_nth {g i c : Nat} {m : Loc} (h : c + 1 ≤ okPolls m ((X.tr g).take i)) :
    ∃ j pc p acq sc, j < i ∧ X.get (g, j) = some ⟨pc, .wait m p true acq sc⟩ ∧
      okPolls m ((X.tr g).take j) = c := by
  obtain ⟨j, e, hj, he, hp, hc⟩ := exists_nthEv (X := X) (g := g) (p := okPoll m) h
  obtain ⟨epc, k⟩ := e
  cases k <;> simp only [okPoll, sourceWaitSuccess, Bool.false_eq_true] at hp
  rename_i m' p ok acq sc
  cases ok <;> simp only [Bool.false_eq_true, decide_eq_true_eq] at hp
  subst hp
  exact ⟨j, epc, p, acq, sc, hj, he, hc⟩

/-- Two credits of loop trips are equal only for one item and one trip. -/
theorem trip_credit_inj {n a b t t' : Nat} (ht : t + 1 < n) (ht' : t' + 1 < n)
    (h : n * a + (1 + t) = n * b + (1 + t')) : a = b ∧ t = t' := by
  rcases Nat.lt_trichotomy a b with hab | rfl | hab
  · have := Nat.mul_le_mul_left n (show a + 1 ≤ b by omega)
    rw [Nat.mul_add] at this; omega
  · omega
  · have := Nat.mul_le_mul_left n (show b + 1 ≤ a by omega)
    rw [Nat.mul_add] at this; omega

/-- A credit of a loop trip is not the credit of a final part. -/
theorem trip_credit_ne {n a b t : Nat} (ht : t + 1 < n) : n * a + n ≠ n * b + (1 + t) := by
  intro h
  rcases Nat.lt_or_ge a b with hab | hab
  · have := Nat.mul_le_mul_left n (show a + 1 ≤ b by omega)
    rw [Nat.mul_add] at this; omega
  · have := Nat.mul_le_mul_left n hab
    omega

theorem nzVote_isVote {pc : Nat} (x : Event) (h : Correction.nzVote pc x = true) :
    Correction.isVoteAt pc x = true := by
  obtain ⟨epc, k⟩ := x
  cases k <;> simp_all [Correction.nzVote, Correction.isVoteAt]

section
variable (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
  (ht : Frame.Tracked (code L) X)
include hpre hX ht

/-- **A correction thread's `tcgen05.ld`** loads sixteen columns of one stage's accumulator, at a
rescale load or a final load. -/
theorem corr_tld {g i pc a : Nat} {vals : List Value} (hw : 8 ≤ warpOf L g)
    (hw' : warpOf L g < 12) (he : X.get (g, i) = some ⟨pc, .tc (.ld a vals .s32x32b)⟩) :
    ∃ (d : Correction.D) (st : Fin 2) (j : Fin 8),
      Frame.stateAt (code L) X g i = some (some (.inr (.corr d))) ∧
      Correction.Counts L g d ((X.tr g).take i) ∧ Correction.Inv L g d ∧
      (d.site = .rld st j ∨ d.site = .fld st j) ∧
      a = Correction.tmem L g (256 + 128 * st.val + 16 * j.val) ∧ vals.length = 16 := by
  rcases corr_origin hpre hX ht he hw hw' (fun _ _ h => by cases h) with ⟨p, -, hk⟩ |
    ⟨d, t, ins, o, hσ, hc, hi, hat, hcode, hf, hev⟩
  · cases hk
  obtain ⟨-, hk⟩ := hev (by simp)
  cases o with
  | none => exact absurd (fires_none_ends hf) (by simp [Ends])
  | some u =>
  have hlen : ∀ (st : Fin 2) (j : Fin 8), (d.site = .rld st j ∨ d.site = .fld st j) →
      vals.length = 16 := by
    intro st j hs
    have hr := holds_mem hat.2.2.2.2 (mem_factsFrom (List.mem_append_left _
      (show Correction.ldAddr st j ∈ Flow.live d.site.pc by
        rcases hs with hs | hs <;> rw [hs]
        · exact (Correction.ldAddr_live st j).1
        · exact (Correction.ldAddr_live st j).2)))
    rw [Correction.ldAddr_val] at hr
    have hat' : At t d.site.pc (Correction.facts L g d) :=
      ⟨hat.1, by rw [hat.2.1]; rcases hs with hs | hs <;> rw [hs] <;> rfl, hat.2.2.1,
        hat.2.2.2.1, hat.2.2.2.2⟩
    rcases hs with hs | hs <;> rw [hs] at hcode hf hat'
    · obtain rfl := Option.some.inj (hcode.symm.trans (Correction.code_rld st j))
      obtain ⟨vals', hl, he', -⟩ := Correction.load_core (Correction.tcLdWait_rld st j) hat' hr
        (Correction.tmem_lt L g _ (by omega)) hf
      injection he' with h1 h2
      injection h2 with h3
      injection h3 with h4 h5
      rw [h5, hl]
      exact (Correction.rldRegs_ok ⟨8 * st.val + j.val, by omega⟩).1
    · obtain rfl := Option.some.inj (hcode.symm.trans (Correction.code_fld st j))
      obtain ⟨vals', hl, he', -⟩ := Correction.load_core (Correction.tcLdWait_fld st j) hat' hr
        (Correction.tmem_lt L g _ (by omega)) hf
      injection he' with h1 h2
      injection h2 with h3
      injection h3 with h4 h5
      rw [h5, hl]
      exact (Correction.fldRegs_ok ⟨8 * st.val + j.val, by omega⟩).1
  obtain ⟨site, i', tt, aw, aa, o⟩ := d
  cases site
  case rld st j =>
    obtain ⟨vals', hk1⟩ := hk
    injection hk1 with h1
    injection h1 with h2 h3
    exact ⟨_, st, j, hσ, hc, hi, .inl rfl, h2, hlen st j (.inl rfl)⟩
  case fld st j =>
    obtain ⟨vals', hk1⟩ := hk
    injection hk1 with h1
    injection h1 with h2 h3
    exact ⟨_, st, j, hσ, hc, hi, .inr rfl, h2, hlen st j (.inr rfl)⟩
  all_goals exfalso
  all_goals simp at hk

/-- **A correction thread's `tcgen05.st`** stores sixteen columns of one stage's accumulator, at
a rescale store. -/
theorem corr_tst {g i pc a : Nat} {vals : List Value} (hw : 8 ≤ warpOf L g)
    (hw' : warpOf L g < 12) (he : X.get (g, i) = some ⟨pc, .tc (.st a vals .s32x32b)⟩) :
    ∃ (d : Correction.D) (st : Fin 2) (j : Fin 8),
      Frame.stateAt (code L) X g i = some (some (.inr (.corr d))) ∧
      Correction.Counts L g d ((X.tr g).take i) ∧ Correction.Inv L g d ∧
      d.site = .rst st j ∧
      a = Correction.tmem L g (256 + 128 * st.val + 16 * j.val) ∧ vals.length = 16 := by
  rcases corr_origin hpre hX ht he hw hw' (fun _ _ h => by cases h) with ⟨p, -, hk⟩ |
    ⟨d, t, ins, o, hσ, hc, hi, hat, hcode, hf, hev⟩
  · cases hk
  obtain ⟨-, hk⟩ := hev (by simp)
  obtain ⟨site, i', tt, aw, aa, o'⟩ := d
  cases site
  case rst st j =>
    obtain ⟨vals', hk1⟩ := hk
    injection hk1 with h1
    injection h1 with h2 h3
    refine ⟨_, st, j, hσ, hc, hi, rfl, h2, ?_⟩
    obtain ⟨ta, ss, hcs, hl⟩ := tcStLen_spec (rst_len st j)
    obtain rfl := Option.some.inj (hcode.symm.trans hcs)
    rw [fires_tcSt_len (fun _ h => by cases h) hf rfl, hl]
  all_goals exfalso
  all_goals simp at hk


/-- **`RouteFacts.corr_p`**: a correction arrival of credit `q` on stage `st`'s P-ready barrier
has `q + 1 ≤ n (I' + 1)` with `I'` its O-full polls of the stage, and is the first, a rescale's
(after its sync of the trip) or a final part's (after its O-full poll of the item). -/
theorem RouteFacts_corr_p {h i pc tx cnt st : Nat} {rel : Bool} {sc : MbarScope}
    (_hh : h < L.threads) (hw : 8 ≤ warpOf L h) (hw' : warpOf L h < 12) (hst : st < 2)
    (he : X.get (h, i) = some ⟨pc, .arrive (pReadyBar L (leadCta (ctaOf L h)) st) tx cnt rel sc⟩) :
    pArr L X h st i + 1 ≤
        kvTiles L * (okPolls (oFullBar L (ctaOf L h) st) ((X.tr h).take i) + 1) ∧
      (pArr L X h st i = 0 ∨ CorrSync L X h st i (pArr L X h st i + 1) ∨
        CorrFinal L X h st i (pArr L X h st i)) := by
  obtain ⟨-, -, d, -, hc, hi, -, hs⟩ := corr_arrive hpre hX ht hw hw' he
  have hT := corr_trips_pos hpre
  have hkw := corr_kOf hw hw'
  have hpa : pArr L X h st i = Correction.trips L * d.i + Correction.freePos L st d := by
    rw [pArr, pReadyBar_lead]; exact hc.free st hst
  have hof : okPolls (oFullBar L (ctaOf L h) st) ((X.tr h).take i) =
      d.i + Correction.oPos st d := by
    rw [oFullBar_own]; exact hc.oFull st hst
  rw [kvTiles_eq, hof]
  rcases hs with ⟨a, -, hm⟩ | ⟨st', -, hm⟩ | ⟨st', hsd, hm⟩
  · simp only [Correction.ownLoc, pReadyBar, leadCta, Correction.sb, Loc.mk.injEq] at hm; omega
  · simp only [Correction.ownLoc, pReadyBar, leadCta, Correction.sb, Loc.mk.injEq] at hm; omega
  rw [pReadyBar_lead] at hm
  simp only [Correction.leadLoc, Loc.mk.injEq] at hm
  obtain rfl : st = st'.val := by omega
  have htr := hi.trip
  have hst0 := hi.start
  have hsy := hc.sync st'.val st'.isLt
  have hoff := hc.oFull st'.val st'.isLt
  rw [← oFullBar_own] at hoff
  rcases hsd with hsd | ⟨b, hsd⟩
  · -- the first arrival
    obtain ⟨site, i', tt, aw, aa, o⟩ := d
    simp only at hsd hst0 hpa ⊢
    subst hsd
    obtain rfl := hst0 (.inr (.inr ⟨st', rfl⟩))
    refine ⟨?_, .inl ?_⟩ <;> rw [hpa] <;> fin_cases st' <;>
      simp [Correction.freePos, Correction.oPos] <;> omega
  obtain ⟨site, i', tt, aw, aa, o⟩ := d
  simp only at hsd htr hpa hsy hoff ⊢
  subst hsd
  cases b
  · -- a rescale's: after the stage's sync of the trip
    have ht1 := htr (by fin_cases st' <;> rfl)
    have hsy' : (Correction.trips L + 1) * i' + (1 + tt) + 1 ≤
        barEvents (Correction.kOf L h + 3 + 4 * st'.val) 64 .sync ((X.tr h).take i) := by
      rw [hsy]; fin_cases st' <;> simp [Correction.syncPos]
    obtain ⟨y, pcy, hy, hey, hcy⟩ := corr_sync_nth st'.val hw hw' hsy'
    refine ⟨?_, .inr (.inl ⟨y, pcy, hy, hey, ?_⟩)⟩
    · rw [hpa]; fin_cases st' <;> simp [Correction.freePos, Correction.oPos] <;> nlinarith
    · have hid : statsId st'.val (warpOf L h - 8) = Correction.kOf L h + 3 + 4 * st'.val := by
        simp only [statsId]; omega
      rw [hid, corr_barOrd hpre hX ht hw hw' y (by omega), hcy, hpa, genTiles, ← kvTiles_eq,
        kvTiles_eq]
      have hdiv : ((Correction.trips L + 1) * i' + (1 + tt)) / (Correction.trips L + 1) = i' := by
        rw [Nat.add_comm, Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt (by omega)]
        simp
      have hmod : ((Correction.trips L + 1) * i' + (1 + tt)) % (Correction.trips L + 1) =
          1 + tt := by
        rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
      rw [hdiv, hmod]
      fin_cases st' <;> simp [Correction.freePos] <;> omega
  · -- a final part's: after the stage's O-full poll of the item
    have hof' : i' + 1 ≤ okPolls (oFullBar L (ctaOf L h) st'.val) ((X.tr h).take i) := by
      rw [hoff]; fin_cases st' <;> simp [Correction.oPos]
    obtain ⟨j, pcj, p, acq, sc', hj, hej, hcj⟩ := okPoll_nth hof'
    refine ⟨?_, .inr (.inr ⟨j, pcj, p, acq, sc', hj, hej, ?_⟩)⟩
    · rw [hpa]; fin_cases st' <;> simp [Correction.freePos, Correction.oPos] <;> nlinarith
    · rw [hcj, hpa, kvTiles_eq]; fin_cases st' <;> simp [Correction.freePos] <;> nlinarith


/-- A rescale event of trip `t` of stage `st` follows the stage's sync of the trip. -/
theorem corr_sync_route {h i : Nat} {d : Correction.D} (st : Nat) (hst : st < 2)
    (hw : 8 ≤ warpOf L h) (hw' : warpOf L h < 12)
    (hc : Correction.Counts L h d ((X.tr h).take i)) (ht1 : d.t + 1 < Correction.trips L)
    (hsp : Correction.syncPos L st d = 2 + d.t) (hfp : Correction.freePos L st d = 1 + d.t) :
    CorrSync L X h st i (pArr L X h st i + 1) := by
  have hkw := corr_kOf hw hw'
  have hpa : pArr L X h st i = Correction.trips L * d.i + Correction.freePos L st d := by
    rw [pArr, pReadyBar_lead]; exact hc.free st hst
  have hsy' : (Correction.trips L + 1) * d.i + (1 + d.t) + 1 ≤
      barEvents (Correction.kOf L h + 3 + 4 * st) 64 .sync ((X.tr h).take i) := by
    rw [hc.sync st hst, hsp]; omega
  obtain ⟨y, pcy, hy, hey, hcy⟩ := corr_sync_nth st hw hw' hsy'
  refine ⟨y, pcy, hy, hey, ?_⟩
  have hid : statsId st (warpOf L h - 8) = Correction.kOf L h + 3 + 4 * st := by
    simp only [statsId]; omega
  rw [hid, corr_barOrd hpre hX ht hw hw' y (by omega), hcy, hpa, genTiles, kvTiles_eq]
  have hdiv : ((Correction.trips L + 1) * d.i + (1 + d.t)) / (Correction.trips L + 1) = d.i := by
    rw [Nat.add_comm, Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt (by omega)]
    simp
  have hmod : ((Correction.trips L + 1) * d.i + (1 + d.t)) % (Correction.trips L + 1) =
      1 + d.t := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
  rw [hdiv, hmod, hfp]
  omega

omit hpre hX ht in
/-- A final-part event of stage `st` follows the stage's O-full poll of the item. -/
theorem corr_final_route {h i : Nat} {d : Correction.D} (st : Nat) (hst : st < 2)
    (hc : Correction.Counts L h d ((X.tr h).take i)) (hop : Correction.oPos st d = 1)
    (hfp : Correction.freePos L st d = Correction.trips L) :
    CorrFinal L X h st i (pArr L X h st i) := by
  have hpa : pArr L X h st i = Correction.trips L * d.i + Correction.freePos L st d := by
    rw [pArr, pReadyBar_lead]; exact hc.free st hst
  have hof : d.i + 1 ≤ okPolls (oFullBar L (ctaOf L h) st) ((X.tr h).take i) := by
    rw [oFullBar_own, hc.oFull st hst, hop]
  obtain ⟨j, pcj, p, acq, sc', hj, hej, hcj⟩ := okPoll_nth hof
  refine ⟨j, pcj, p, acq, sc', hj, hej, ?_⟩
  rw [hcj, hpa, hfp, kvTiles_eq]
  nlinarith

/-- **`RouteFacts.corr_ld`**: a correction load reads sixteen columns of one stage's accumulator,
a rescale's (after its sync of the trip) or a final part's (after its O-full poll of the
item). -/
theorem RouteFacts_corr_ld {h i a : Nat} {vals : List Value} (_hh : h < L.threads)
    (hw : 8 ≤ warpOf L h) (hw' : warpOf L h < 12) (hld : X.TLd (h, i) a vals .s32x32b) :
    ∃ st < 2, 0 < vals.length ∧
      (∀ j < vals.length, InO st (tcDataCell32 L h a j)) ∧
      (CorrSync L X h st i (pArr L X h st i + 1) ∨ CorrFinal L X h st i (pArr L X h st i)) := by
  obtain ⟨pc, he⟩ := hld
  obtain ⟨d, st, j0, -, hc, hi, hs, rfl, hl⟩ := corr_tld hpre hX ht hw hw' he
  refine ⟨st.val, st.isLt, by omega, fun j hj => ?_, ?_⟩
  · rw [hl] at hj
    have hcol := tmem_column L h h (256 + 128 * st.val + 16 * j0.val) j (by omega)
    simp only [InO, hcol]
    omega
  · have htr := hi.trip
    obtain ⟨site, i', tt, aw, aa, o⟩ := d
    simp only at hs htr
    rcases hs with hs | hs <;> subst hs
    · exact .inl (corr_sync_route hpre hX ht st.val st.isLt hw hw' hc
        (htr (by fin_cases st <;> rfl)) (by fin_cases st <;> simp [Correction.syncPos])
        (by fin_cases st <;> simp [Correction.freePos]))
    · exact .inr (corr_final_route st.val st.isLt hc (by fin_cases st <;> simp [Correction.oPos])
        (by fin_cases st <;> simp [Correction.freePos]))


omit hpre hX ht in
/-- The cell of word `p` of a correction load or store fixes its stage and chunk. -/
theorem corr_cell_eq {h : Nat} {s1 s2 : Fin 2} {j1 j2 : Fin 8} {p p' : Nat} (hp : p < 16)
    (hp' : p' < 16)
    (he : tcDataCell32 L h (Correction.tmem L h (256 + 128 * s1.val + 16 * j1.val)) p =
      tcDataCell32 L h (Correction.tmem L h (256 + 128 * s2.val + 16 * j2.val)) p') :
    s1 = s2 ∧ j1 = j2 := by
  have h1 := tmem_column L h h (256 + 128 * s1.val + 16 * j1.val) p (by omega)
  have h2 := tmem_column L h h (256 + 128 * s2.val + 16 * j2.val) p' (by omega)
  rw [he] at h1
  rw [h1] at h2
  exact ⟨Fin.ext (by omega), Fin.ext (by omega)⟩

omit hpre hX ht in
/-- No nonzero vote of a stage between two events of one rescale of the stage. -/
theorem corr_nzVote_same {h i i' : Nat} {d d' : Correction.D} (st : Nat) (hst : st < 2)
    (hii : i ≤ i') (hc : Correction.Counts L h d ((X.tr h).take i))
    (hc' : Correction.Counts L h d' ((X.tr h).take i')) (hI : d.i = d'.i)
    (hv : Correction.votePos L st d = Correction.votePos L st d') :
    ((X.tr h).take i').countP (Correction.nzVote (Correction.votePc st)) =
      ((X.tr h).take i).countP (Correction.nzVote (Correction.votePc st)) := by
  have hseg := countP_take_sub_le (p := Correction.nzVote (Correction.votePc st))
    (q := Correction.isVoteAt (Correction.votePc st)) (fun x hx => nzVote_isVote x hx) (X.tr h) hii
  have hm := countP_take_mono (Correction.nzVote (Correction.votePc st)) (X.tr h) hii
  rw [hc.votes st hst, hc'.votes st hst, hI, hv] at hseg
  omega

/-- **`OAccFacts.corr_st_one`**: a correction thread stores each cell once per credit. -/
theorem OAccFacts_corr_st_one {h i i' a a' j j' st : Nat} {vals vals' : List Value}
    (_hh : h < L.threads) (hw : 8 ≤ warpOf L h) (hw' : warpOf L h < 12)
    (hs : X.TSt (h, i) a vals .s32x32b)
    (hs' : X.TSt (h, i') a' vals' .s32x32b) (hj : j < vals.length) (hj' : j' < vals'.length)
    (hcell : tcDataCell32 L h a j = tcDataCell32 L h a' j') (hin : InO st (tcDataCell32 L h a j))
    (hq : pArr L X h st i = pArr L X h st i') : i = i' := by
  obtain ⟨pc, he⟩ := hs
  obtain ⟨pc', he'⟩ := hs'
  obtain ⟨d, s1, j1, -, hc, hi, hs1, rfl, hl⟩ := corr_tst hpre hX ht hw hw' he
  obtain ⟨d', s2, j2, -, hc', hi', hs2, rfl, hl'⟩ := corr_tst hpre hX ht hw hw' he'
  rw [hl] at hj
  rw [hl'] at hj'
  obtain ⟨rfl, rfl⟩ := corr_cell_eq hj hj' hcell
  have hcol := tmem_column L h h (256 + 128 * s1.val + 16 * j1.val) j (by omega)
  simp only [InO, hcol] at hin
  obtain rfl : st = s1.val := by omega
  have htr := hi.trip
  have htr' := hi'.trip
  obtain ⟨site, I, t, aw, aa, o⟩ := d
  obtain ⟨site', I', t', aw', aa', o'⟩ := d'
  simp only at hs1 hs2 htr htr'
  subst hs1 hs2
  have ht1 := htr (by fin_cases s1 <;> rfl)
  have ht2 := htr' (by fin_cases s1 <;> rfl)
  have hp1 := hc.free s1.val s1.isLt
  have hp2 := hc'.free s1.val s1.isLt
  rw [pArr, pReadyBar_lead, hp1, pArr, pReadyBar_lead, hp2] at hq
  have hf : ∀ (k u : Nat) (ao : List Value) (aw : Value) (aa : ℝ),
      Correction.freePos L s1.val ⟨.rst s1 j1, k, u, aw, aa, ao⟩ = 1 + u := by
    intro k u ao aw aa; fin_cases s1 <;> simp [Correction.freePos]
  rw [hf, hf] at hq
  simp only at hq
  obtain ⟨rfl, rfl⟩ := trip_credit_inj ht1 ht2 hq
  -- two stores of one chunk of one rescale: the stores between them would need another vote
  have key : ∀ {x y : Nat} {dx dy : Correction.D}, x < y →
      dx = ⟨.rst s1 j1, I, t, aw, aa, o⟩ ∨ dx = ⟨.rst s1 j1, I, t, aw', aa', o'⟩ →
      dy = ⟨.rst s1 j1, I, t, aw, aa, o⟩ ∨ dy = ⟨.rst s1 j1, I, t, aw', aa', o'⟩ →
      Correction.Counts L h dx ((X.tr h).take x) →
      Correction.Counts L h dy ((X.tr h).take y) →
      (∃ pcx, X.get (h, x) = some ⟨pcx, .tc (.st (Correction.tmem L h
        (256 + 128 * s1.val + 16 * j1.val)) vals .s32x32b)⟩ ∨ X.get (h, x) = some ⟨pcx, .tc (.st
        (Correction.tmem L h (256 + 128 * s1.val + 16 * j1.val)) vals' .s32x32b)⟩) → False := by
    intro x y dx dy hxy hdx hdy hcx hcy ⟨pcx, hex⟩
    have hsame := corr_nzVote_same s1.val s1.isLt hxy.le hcx hcy
      (by rcases hdx with rfl | rfl <;> rcases hdy with rfl | rfl <;> rfl)
      (by rcases hdx with rfl | rfl <;> rcases hdy with rfl | rfl <;> rfl)
    have hSx := hcx.tcSt s1.val s1.isLt
    have hSy := hcy.tcSt s1.val s1.isLt
    have hstep : tcStsIn (Correction.oLo L h s1.val) (Correction.oHi L h s1.val)
        ((X.tr h).take (x + 1)) =
        tcStsIn (Correction.oLo L h s1.val) (Correction.oHi L h s1.val) ((X.tr h).take x) + 1 := by
      unfold tcStsIn
      rcases hex with hex | hex <;>
      · rw [countP_take_succ hex]
        simp [tcStAt, Correction.oLo, Correction.oHi, Correction.tmem]
        omega
    have hmono := countP_take_mono (tcStAt (Correction.oLo L h s1.val)
      (Correction.oHi L h s1.val)) (X.tr h) (show x + 1 ≤ y by omega)
    unfold tcStsIn at hSx hSy hstep
    rw [hsame] at hSy
    have hlx : Correction.stLack s1.val dx = 8 - j1.val := by
      rcases hdx with rfl | rfl <;> simp [Correction.stLack]
    have hly : Correction.stLack s1.val dy = 8 - j1.val := by
      rcases hdy with rfl | rfl <;> simp [Correction.stLack]
    rw [hlx] at hSx
    rw [hly] at hSy
    omega
  rcases Nat.lt_trichotomy i i' with hlt | heq | hlt
  · exact (key hlt (.inl rfl) (.inr rfl) hc hc' ⟨pc, .inl he⟩).elim
  · exact heq
  · exact (key hlt (.inr rfl) (.inl rfl) hc' hc ⟨pc', .inr he'⟩).elim

/-- **`OAccFacts.corr_ld_st`**: a correction thread loads a cell before it stores the cell in
the same credit. -/
theorem OAccFacts_corr_ld_st {h i i' a a' j j' st : Nat} {vals vals' : List Value}
    (_hh : h < L.threads) (hw : 8 ≤ warpOf L h) (hw' : warpOf L h < 12)
    (hl : X.TLd (h, i) a vals .s32x32b)
    (hs : X.TSt (h, i') a' vals' .s32x32b) (hj : j < vals.length) (hj' : j' < vals'.length)
    (hcell : tcDataCell32 L h a j = tcDataCell32 L h a' j') (hin : InO st (tcDataCell32 L h a j))
    (hq : pArr L X h st i = pArr L X h st i') : i < i' := by
  obtain ⟨pc, he⟩ := hl
  obtain ⟨pc', he'⟩ := hs
  obtain ⟨d, s1, j1, -, hc, hi, hs1, rfl, hl⟩ := corr_tld hpre hX ht hw hw' he
  obtain ⟨d', s2, j2, -, hc', hi', hs2, rfl, hl'⟩ := corr_tst hpre hX ht hw hw' he'
  rw [hl] at hj
  rw [hl'] at hj'
  obtain ⟨rfl, rfl⟩ := corr_cell_eq hj hj' hcell
  have hcol := tmem_column L h h (256 + 128 * s1.val + 16 * j1.val) j (by omega)
  simp only [InO, hcol] at hin
  obtain rfl : st = s1.val := by omega
  have htr := hi.trip
  have htr' := hi'.trip
  obtain ⟨site, I, t, aw, aa, o⟩ := d
  obtain ⟨site', I', t', aw', aa', o'⟩ := d'
  simp only at hs1 hs2 htr htr'
  subst hs2
  have ht2 := htr' (by fin_cases s1 <;> rfl)
  have hp1 := hc.free s1.val s1.isLt
  have hp2 := hc'.free s1.val s1.isLt
  rw [pArr, pReadyBar_lead, hp1, pArr, pReadyBar_lead, hp2] at hq
  have hf2 : Correction.freePos L s1.val ⟨.rst s1 j1, I', t', aw', aa', o'⟩ = 1 + t' := by
    fin_cases s1 <;> simp [Correction.freePos]
  rw [hf2] at hq
  simp only at hq
  rcases hs1 with rfl | rfl
  · have ht1 := htr (by fin_cases s1 <;> rfl)
    have hf1 : Correction.freePos L s1.val ⟨.rld s1 j1, I, t, aw, aa, o⟩ = 1 + t := by
      fin_cases s1 <;> simp [Correction.freePos]
    rw [hf1] at hq
    obtain ⟨rfl, rfl⟩ := trip_credit_inj ht1 ht2 hq
    rcases Nat.lt_trichotomy i i' with hlt | rfl | hlt
    · exact hlt
    · rw [he] at he'; cases he'
    · exfalso
      have hsame := corr_nzVote_same s1.val s1.isLt hlt.le hc' hc rfl
        (by fin_cases s1 <;> simp [Correction.votePos])
      have hLx := hc'.tcLd s1.val s1.isLt
      have hLy := hc.tcLd s1.val s1.isLt
      have hmono := countP_take_mono (tcLdAt (Correction.oLo L h s1.val)
        (Correction.oHi L h s1.val)) (X.tr h) hlt.le
      unfold tcLdsIn at hLx hLy
      rw [hsame] at hLy
      have h1 : Correction.ldLack s1.val ⟨.rst s1 j1, I, t, aw', aa', o'⟩ = 7 - j1.val := by
        simp [Correction.ldLack]
      have h2 : Correction.ldLack s1.val ⟨.rld s1 j1, I, t, aw, aa, o⟩ = 8 - j1.val := by
        simp [Correction.ldLack]
      have h3 : Correction.finPos s1.val ⟨.rst s1 j1, I, t, aw', aa', o'⟩ = 0 := by
        simp [Correction.finPos]
      have h4 : Correction.finPos s1.val ⟨.rld s1 j1, I, t, aw, aa, o⟩ = 0 := by
        simp [Correction.finPos]
      rw [h1, h3] at hLx
      rw [h2, h4] at hLy
      have := j1.isLt
      simp only at hLx hLy
      omega
  · exfalso
    have hf1 : Correction.freePos L s1.val ⟨.fld s1 j1, I, t, aw, aa, o⟩ = Correction.trips L := by
      fin_cases s1 <;> simp [Correction.freePos]
    rw [hf1] at hq
    exact trip_credit_ne ht2 hq

end

end
end PTX.Kernels.FlashAttn4Fwd.Proof
