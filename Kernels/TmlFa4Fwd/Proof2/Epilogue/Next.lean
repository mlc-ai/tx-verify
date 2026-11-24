-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof2.Epilogue.Ideal
public import Kernels.TmlFa4Fwd.Proof2.Epilogue.Shape

@[expose] public section

/-! # The output warp's transitions keep the reference values

A state that holds the reference values (`Fits`) and an event that returns what the reference
says (`Expect`: the launch word at a read, the source lane's value at a shuffle, the predicates
of all lanes at a ballot) lead to a state that holds them (`fits_next`), and never to a state the
machine gives up on (`next_ne`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof2.Epilogue
open PTX PTX.Proof PTX.Flow

noncomputable section

/-- What the reference says an event at state `d` of lane `g` returns. -/
def Expect (p : Params) (L : Launch) (g : Nat) (d : D) (ns : Nat) (e : Event) : Prop :=
  let ℓ := laneOf L g
  let c := g / L.block
  match d.site, e.kind with
  | .word k, .rd _ bs => ∀ r n0 v0, PassStart p L g k.late n0 v0 → ScanRound p c k r →
      ns = n0 + 7 * r → rebuild 3 bs = .ok (.bits 32 (qv p (req p k.late r ℓ)))
  | .q0, .rd _ bs => rebuild 3 bs = .ok (.bits 32 (qv p (chosen d)))
  | .q1, .rd _ bs => rebuild 3 bs = .ok (.bits 32 (qv p (addi (chosen d) 1)))
  | .down k, .shfl _ _ _ _ v _ => ∀ r n0 v0, PassStart p L g k.late n0 v0 → ScanRound p c k r →
      ns = n0 + 7 * r → v = .bits 32 (dnv p k.late r ℓ)
  | .up k j, .shfl _ _ _ _ v _ => ∀ r n0 v0, PassStart p L g k.late n0 v0 →
      ScanRound p c k r → ns = n0 + 7 * r + 1 + j.val →
      v = .bits 32 (psum p k.late r j.val (upSrc j.val ℓ))
  | .total k, .shfl _ _ _ _ v _ => ∀ r n0 v0, PassStart p L g k.late n0 v0 →
      ScanRound p c k r → ns = n0 + 7 * r + 6 → v = .bits 32 (T p k.late r)
  | .vote late, .vote _ _ b => ∀ R n0 v0, PassStart p L g late n0 v0 → End p c late R →
      ns = n0 + 7 * (R + 1) → ∀ i < 32, b.getLsbD i = predv p c late R i
  | .pre late, .shfl _ _ _ _ v _ => ∀ R n0 v0, PassStart p L g late n0 v0 → End p c late R →
      ns = n0 + 7 * (R + 1) →
      v = .bits 32 (psum p late R 5 ((addi (popc d.bal) (-1)).toNat % 32))
  | .tiles late, .shfl _ _ _ _ v _ => ∀ R n0 v0, PassStart p L g late n0 v0 →
      End p c late R → v = .bits 32 (tlv p late R ((popc d.bal).toNat % 32))
  | _, _ => True

variable {p : Params} {L : Launch} {g : Nat} {ent : Nat → Value} {ns nv : Nat}

theorem scanRound_first {c r : Nat} (h : ScanRound p c .first r) : r = 0 := by
  have := h.2; simp_all
theorem scanRound_second {c r : Nat} (h : ScanRound p c .second r) : r = 0 := by
  have := h.2; simp_all
theorem scanRound_loop {c r : Nat} (h : ScanRound p c .loop r) : r ≠ 0 := by
  have := h.2; simp_all
theorem scanRound_loop2 {c r : Nat} (h : ScanRound p c .loop2 r) : r ≠ 0 := by
  have := h.2; simp_all

theorem passStart_false {n0 v0 : Nat} : PassStart p L g false n0 v0 ↔ n0 = 3 ∧ v0 = 0 := by
  simp [PassStart]

/-- The prefix a state holds is the reference prefix of its round. -/
theorem prefixD_eq {late : Bool} {r : Nat} {d : D} (h : RoundVals p late (laneOf L g) r 5 d) :
    prefixD L g d = psum p late r 5 (laneOf L g) := by
  obtain ⟨htl, hu⟩ := h
  have h0 := hu 0 (by omega)
  have h1 := hu 1 (by omega)
  have h2 := hu 2 (by omega)
  have h3 := hu 3 (by omega)
  have h4 := hu 4 (by omega)
  simp only [uAt] at h0 h1 h2 h3 h4
  simp only [prefixD, prefixOf, psum, upd, htl, h0, h1, h2, h3, h4]
  norm_num

set_option maxHeartbeats 4000000 in
theorem fits_next_start {d d' : D} {e : Event} (hs : d.site = .start) (hF : Fits p L g d ns nv)
    (hn : (code p L g ent).next d e = some (some d')) : Fits p L g d' ns nv := by
  obtain ⟨s, w, dn, tl, u1, u2, u4, u8, u16, tot, grp, acc, gx, cur, bal, pv, nt, c0, c1⟩ := d
  subst hs
  simp only [Fits] at hF
  obtain ⟨rfl, rfl⟩ := hF
  simp only [code, succ, Option.some.injEq] at hn
  subst hn
  split <;> rename_i hb
  · refine ⟨0, 3, 0, by simp [PassStart, Scan.late], ⟨fun _ h => absurd h (Nat.not_lt_zero _),
      by simp⟩, rfl, rfl, fun h => absurd rfl h, ?_⟩
    simp [wv, reads, req, batchOf, Scan.late, hb]
  · refine ⟨0, 3, 0, by simp [PassStart, Scan.late], ⟨fun _ h => absurd h (Nat.not_lt_zero _),
      by simp⟩, rfl, rfl, fun h => absurd rfl h, ?_⟩
    simp_all [reads, req, batchOf, Scan.late]

set_option maxHeartbeats 4000000 in
theorem fits_next_word {d d' : D} {e : Event} {k : Scan} (hs : d.site = .word k)
    (hF : Fits p L g d ns nv) (hE : Expect p L g d ns e)
    (hn : (code p L g ent).next d e = some (some d')) : Fits p L g d' ns nv := by
  obtain ⟨s, w, dn, tl, u1, u2, u4, u8, u16, tot, grp, acc, gx, cur, bal, pv, nt, c0, c1⟩ := d
  subst hs
  obtain ⟨r, n0, v0, hP, hR, hns, hnv, hL, hrd⟩ := hF
  obtain ⟨pc, kind⟩ := e
  cases kind <;> simp only [code, succ, reduceCtorEq] at hn
  rename_i a bs
  simp only [Expect] at hE
  rw [hE r n0 v0 hP hR hns] at hn
  simp only [word32, Option.some.injEq] at hn
  subst hn
  exact ⟨r, n0, v0, hP, hR, hns, hnv, hL, by simp [wv, hrd]⟩

set_option maxHeartbeats 4000000 in
theorem fits_next_down {d d' : D} {e : Event} {k : Scan} (hs : d.site = .down k)
    (hF : Fits p L g d ns nv) (hE : Expect p L g d ns e)
    (hn : (code p L g ent).next d e = some (some d')) : Fits p L g d' (ns + 1) nv := by
  obtain ⟨s, w, dn, tl, u1, u2, u4, u8, u16, tot, grp, acc, gx, cur, bal, pv, nt, c0, c1⟩ := d
  subst hs
  obtain ⟨r, n0, v0, hP, hR, hns, hnv, hL, hw⟩ := hF
  obtain ⟨pc, kind⟩ := e
  cases kind <;> simp only [code, succ, reduceCtorEq] at hn
  rename_i mode a b c v ok
  simp only [Expect] at hE
  rw [hE r n0 v0 hP hR hns] at hn
  simp only [word32, Option.some.injEq] at hn
  subst hn
  refine ⟨r, n0, v0, hP, hR, by omega, hnv, hL, ?_, fun i hi => by omega⟩
  simp only at hw ⊢
  cases k
  · obtain rfl := scanRound_first hR
    simp [tlOf, tlv, skipv, skipFirst, hw, Scan.late]
  · have h0 := scanRound_loop hR
    obtain ⟨hg, -⟩ := hL h0
    simp only at hg
    subst hg
    simp [tlOf, tlv, skipv, skipLoop, hw, h0, req, reqOf, Scan.late]
  · obtain rfl := scanRound_second hR
    simp [tlOf, tlv, skipv, skipFirst, hw, Scan.late]
  · have h0 := scanRound_loop2 hR
    obtain ⟨hg, -⟩ := hL h0
    simp only at hg
    subst hg
    simp [tlOf, tlv, skipv, skipLoop, hw, h0, req, reqOf, Scan.late]

set_option maxHeartbeats 4000000 in
theorem fits_next_up {d d' : D} {e : Event} {k : Scan} {j : Fin 5} (hs : d.site = .up k j)
    (hF : Fits p L g d ns nv) (hE : Expect p L g d ns e)
    (hn : (code p L g ent).next d e = some (some d')) : Fits p L g d' (ns + 1) nv := by
  obtain ⟨s, w, dn, tl, u1, u2, u4, u8, u16, tot, grp, acc, gx, cur, bal, pv, nt, c0, c1⟩ := d
  subst hs
  obtain ⟨r, n0, v0, hP, hR, hns, hnv, hL, htl, hu⟩ := hF
  obtain ⟨pc, kind⟩ := e
  cases kind <;> simp only [code, succ, reduceCtorEq] at hn
  rename_i mode a b c v ok
  simp only [Expect] at hE
  rw [hE r n0 v0 hP hR hns] at hn
  fin_cases j <;> simp only [word32, Option.some.injEq, Fin.isValue] at hn <;> subst hn <;>
    simp only [Fin.isValue] at hns hu ⊢
  · exact ⟨r, n0, v0, hP, hR, by omega, hnv, hL, htl, fun i hi => by
      obtain rfl : i = 0 := by omega
      rfl⟩
  · exact ⟨r, n0, v0, hP, hR, by omega, hnv, hL, htl, fun i hi => by
      rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl
      · exact hu 0 (by omega)
      · rfl⟩
  · exact ⟨r, n0, v0, hP, hR, by omega, hnv, hL, htl, fun i hi => by
      rcases (show i = 0 ∨ i = 1 ∨ i = 2 by omega) with rfl | rfl | rfl
      · exact hu 0 (by omega)
      · exact hu 1 (by omega)
      · rfl⟩
  · exact ⟨r, n0, v0, hP, hR, by omega, hnv, hL, htl, fun i hi => by
      rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 by omega) with rfl | rfl | rfl | rfl
      · exact hu 0 (by omega)
      · exact hu 1 (by omega)
      · exact hu 2 (by omega)
      · rfl⟩
  · exact ⟨r, n0, v0, hP, hR, by omega, hnv, hL, htl, fun i hi => by
      rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 by omega) with rfl | rfl | rfl | rfl | rfl
      · exact hu 0 (by omega)
      · exact hu 1 (by omega)
      · exact hu 2 (by omega)
      · exact hu 3 (by omega)
      · rfl⟩

theorem fits_ite {c : Prop} [Decidable c] {a b : D} (ha : c → Fits p L g a ns nv)
    (hb : ¬ c → Fits p L g b ns nv) : Fits p L g (if c then a else b) ns nv := by
  by_cases h : c
  · simpa only [h, ↓reduceIte] using ha h
  · simpa only [h, ↓reduceIte] using hb h

/-- A scan round's total leads to the next round, the ballot or the return. -/
theorem fits_afterTotal {d : D} {k : Scan} {r n0 v0 : Nat}
    (hP : PassStart p L g k.late n0 v0) (hR : ScanRound p (g / L.block) k r)
    (hns : ns = n0 + 7 * r + 6) (hnv : nv = v0) (hL : LoopVals p k.late r d)
    (hRV : RoundVals p k.late (laneOf L g) r 5 d) :
    Fits p L g (afterTotal p L g k d (T p k.late r)) (ns + 1) nv := by
  obtain ⟨s, w, dn, tl, u1, u2, u4, u8, u16, tot, grp, acc, gx, cur, bal, pv, nt, c0, c1⟩ := d
  obtain ⟨htl, hu⟩ := hRV
  cases k with
  | first | second =>
    have hr := hR.2
    simp only [or_true, iff_true, reduceCtorEq, or_false] at hr
    subst hr
    simp only [afterTotal, scanExit, loopHead, Scan.late]
    refine fits_ite (fun h1 => fits_ite (fun h2 => ?_) (fun h2 => ?_))
      (fun h1 => fits_ite (fun h3 => fits_ite (fun h4 => ?_) (fun h4 => ?_))
        (fun h3 => fits_ite (fun h4 => ?_) (fun h4 => ?_)))
    · exact ⟨n0, v0, hP, 0, ⟨hR.1, by simp [cont, h1]⟩, .inl ⟨by simp [gxv, atTotal, h1, h2],
        by omega, hnv⟩⟩
    · exact ⟨0, n0, v0, hP, ⟨⟨hR.1, by simp [cont, h1]⟩, rfl, by simp [gxv, atTotal, h1],
        by simp [curv, atTotal, h1], by simp [gxv, atTotal, h1]; simpa using h2⟩,
        by omega, hnv, htl, hu⟩
    · exact ⟨n0, v0, hP, 0, ⟨hR.1, by simp [cont, G, h3]⟩,
        .inl ⟨by simp [gxv, atTotal, h1, G, h4], by omega, hnv⟩⟩
    · exact ⟨0, n0, v0, hP, ⟨⟨hR.1, by simp [cont, G, h3]⟩, rfl, by simp [gxv, atTotal, h1, G],
        by simp [curv, atTotal, h1], by simp [gxv, atTotal, h1, G]; simpa using h4⟩,
        by omega, hnv, htl, hu⟩
    all_goals
      refine ⟨1, n0, v0, hP, ⟨fun r' hr' => ?_, by simp [loopOf]⟩,
        by omega, hnv, fun _ => ⟨rfl, rfl⟩, ?_⟩
      · obtain rfl : r' = 0 := by omega
        simp_all [cont, G, loopOf, Scan.late]
      · simp_all [wv, reads, req, G, reqOf, loopOf, Scan.late]
  | loop | loop2 =>
    have hr := hR.2
    simp only [or_self, iff_false, reduceCtorEq] at hr
    obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
    obtain ⟨hg, ha⟩ := hL (by omega)
    simp only at hg ha
    subst hg ha
    simp only [afterTotal, scanExit, loopHead, Scan.late]
    refine fits_ite (fun h1 => fits_ite (fun h2 => fits_ite (fun h3 => ?_) (fun h3 => ?_))
        (fun h2 => fits_ite (fun h4 => ?_) (fun h4 => ?_)))
      (fun h1 => fits_ite (fun h3 => ?_) (fun h3 => ?_))
    · exact ⟨n0, v0, hP, r' + 1, ⟨hR.1, by simp [cont, h1, G, h2]⟩,
        .inl ⟨by simp [gxv, atTotal, h1, G, h3], by omega, hnv⟩⟩
    · exact ⟨r' + 1, n0, v0, hP, ⟨⟨hR.1, by simp [cont, h1, G, h2]⟩, rfl,
        by simp [gxv, atTotal, h1, G], by simp [curv, atTotal, h1],
        by simp [gxv, atTotal, h1, G]; simpa using h3⟩, by omega, hnv, htl, hu⟩
    · refine ⟨r' + 2, n0, v0, hP, ⟨fun r'' hr'' => ?_, by simp [loopOf]⟩,
        by omega,
        hnv, fun _ => ⟨by simp [G, loopOf, Scan.late], by simp [A, loopOf, Scan.late]⟩,
        by simp [wv, reads, req, G, h4, loopOf, Scan.late]⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hr'' with h | rfl
      · exact hR.1 r'' h
      · simp_all [cont, G, loopOf, Scan.late]
    · refine ⟨r' + 2, n0, v0, hP, ⟨fun r'' hr'' => ?_, by simp [loopOf]⟩,
        by omega,
        hnv, fun _ => ⟨by simp [G, loopOf, Scan.late], by simp [A, loopOf, Scan.late]⟩,
        by simp_all [reads, req, G, reqOf, loopOf, Scan.late]⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hr'' with h | rfl
      · exact hR.1 r'' h
      · simp_all [cont, G, loopOf, Scan.late]
    · exact ⟨n0, v0, hP, r' + 1, ⟨hR.1, by simp [cont, h1]⟩,
        .inl ⟨by simp [gxv, atTotal, h1, h3], by omega, hnv⟩⟩
    · exact ⟨r' + 1, n0, v0, hP, ⟨⟨hR.1, by simp [cont, h1]⟩, rfl, by simp [gxv, atTotal, h1],
        by simp [curv, atTotal, h1], by simp [gxv, atTotal, h1]; simpa using h3⟩,
        by omega, hnv, htl, hu⟩

set_option maxHeartbeats 4000000 in
theorem fits_next_total {d d' : D} {e : Event} {k : Scan} (hs : d.site = .total k)
    (hF : Fits p L g d ns nv) (hE : Expect p L g d ns e)
    (hn : (code p L g ent).next d e = some (some d')) : Fits p L g d' (ns + 1) nv := by
  obtain ⟨s, w, dn, tl, u1, u2, u4, u8, u16, tot, grp, acc, gx, cur, bal, pv, nt, c0, c1⟩ := d
  subst hs
  obtain ⟨r, n0, v0, hP, hR, hns, hnv, hL, hRV⟩ := hF
  obtain ⟨pc, kind⟩ := e
  cases kind <;> simp only [code, succ, reduceCtorEq] at hn
  rename_i mode a b c v ok
  simp only [Expect] at hE
  rw [hE r n0 v0 hP hR hns] at hn
  simp only [word32, Option.some.injEq] at hn
  subst hn
  exact fits_afterTotal hP hR hns hnv hL hRV

set_option maxHeartbeats 4000000 in
theorem fits_next_vote {d d' : D} {e : Event} {late : Bool} (hs : d.site = .vote late)
    (hF : Fits p L g d ns nv) (hE : Expect p L g d ns e)
    (hn : (code p L g ent).next d e = some (some d')) : Fits p L g d' ns (nv + 1) := by
  obtain ⟨s, w, dn, tl, u1, u2, u4, u8, u16, tot, grp, acc, gx, cur, bal, pv, nt, c0, c1⟩ := d
  subst hs
  obtain ⟨R, n0, v0, hP, hEV, hns, hnv, hRV⟩ := hF
  obtain ⟨pc, kind⟩ := e
  cases kind <;> simp only [code, succ, reduceCtorEq] at hn
  rename_i mask a b
  simp only [Expect] at hE
  have hB : BalOf p (g / L.block) late R (BitVec.ofNat 64 b.toNat) :=
    ⟨b, hE R n0 v0 hP hEV.1 hns, rfl⟩
  simp only [Option.some.injEq] at hn
  subst hn
  refine fits_ite (fun h0 => ?_) (fun h0 => ?_)
  · have h1 : selN (BitVec.ofNat 64 b.toNat) = 1 := by simp only [selN, h0, ↓reduceIte]
    exact ⟨R, n0, v0, hP, hEV, by (try simp only); omega, by omega, hRV, hB,
      fun _ => by simp only [pvv, h0, ↓reduceIte]⟩
  · exact ⟨R, n0, v0, hP, hEV, hns, by omega, hRV, hB, by simpa using h0⟩

set_option maxHeartbeats 4000000 in
theorem fits_next_pre {d d' : D} {e : Event} {late : Bool} (hs : d.site = .pre late)
    (hF : Fits p L g d ns nv) (hE : Expect p L g d ns e)
    (hn : (code p L g ent).next d e = some (some d')) : Fits p L g d' (ns + 1) nv := by
  obtain ⟨s, w, dn, tl, u1, u2, u4, u8, u16, tot, grp, acc, gx, cur, bal, pv, nt, c0, c1⟩ := d
  subst hs
  obtain ⟨R, n0, v0, hP, hEV, hns, hnv, hRV, hB, h0⟩ := hF
  obtain ⟨pc, kind⟩ := e
  cases kind <;> simp only [code, succ, reduceCtorEq] at hn
  rename_i mode a b c v ok
  simp only [Expect] at hE
  rw [hE R n0 v0 hP hEV.1 hns] at hn
  simp only [word32, Option.some.injEq] at hn
  subst hn
  simp only at h0
  have h2 : selN bal = 2 := by simp [selN, h0]
  refine fits_ite (fun hl => ?_) (fun hl => ?_)
  · subst hl
    exact ⟨R, n0, v0, hP, hEV, by (try simp only); omega, hnv, hRV, hB,
      fun h => absurd h (by decide)⟩
  · simp only [Bool.not_eq_true] at hl
    subst hl
    exact ⟨R, n0, v0, hP, hEV, by (try simp only); omega, hnv, hRV, hB,
      fun _ => by simp only [pvv, h0, Bool.false_eq_true, ↓reduceIte]⟩

theorem coords_congr {d d' : D} (hc : d.cur = d'.cur) (ht : d.tot = d'.tot) (hp : d.pv = d'.pv)
    (hn : d.nt = d'.nt) : coords p L g d = coords p L g d' := by
  simp only [coords, hc, ht, hp, hn]

/-- The state after the first pass's tile count `x`: the request's first read if the chosen
request is one, else the return. -/
def tilesD (p : Params) (d : D) (x : BitVec 64) : D :=
  let c : D := { d with nt := x }
  if scmp .lt .s (chosen c) (paramW p.batch) then { c with site := .q0 }
  else { c with site := .exit false }

set_option maxHeartbeats 4000000 in
/-- **The first pass's choice**: after the reference tile count, the state holds the choice. -/
theorem fits_tilesD {d : D} (hs : d.site = .tiles false) (hF : Fits p L g d ns nv)
    (hx : ∀ R n0 v0, PassStart p L g false n0 v0 → End p (g / L.block) false R →
      x = ntv p false R d.bal) : Fits p L g (tilesD p d x) (ns + 1) nv := by
  obtain ⟨s, w, dn, tl, u1, u2, u4, u8, u16, tot, grp, acc, gx, cur, bal, pv, nt, c0, c1⟩ := d
  subst hs
  obtain ⟨R, n0, v0, hP, hEV, hns, hnv, hRV, hB, hpv⟩ := hF
  obtain rfl := hx R n0 v0 hP hEV.1
  simp only at hns hpv hEV hB
  obtain ⟨hEnd, htot, hgx, hcur, hgxB⟩ := hEV
  have hs := selN_pos bal
  obtain ⟨rfl, rfl⟩ := passStart_false.mp hP
  have hpv' := hpv trivial
  simp only at htot hgx hcur
  subst htot hgx hcur hpv'
  simp only [tilesD]
  refine fits_ite (fun h3 => ?_) (fun h3 => ?_)
  · refine ⟨R, bal, ⟨hEnd, hB, hgxB, ?_⟩, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
    · simpa only [chosen, chosenD, Bool.not_eq_true] using h3
    · omega
    · omega
  · refine ⟨3, 0, by simp [PassStart], R, hEnd, .inr ⟨bal, hB, hgxB, by omega,
      by omega, fun _ hPk => h3 ?_⟩⟩
    simpa only [chosen, chosenD] using hPk.2.2.2

set_option maxHeartbeats 4000000 in
theorem fits_next_tiles {d d' : D} {e : Event} {late : Bool} (hs : d.site = .tiles late)
    (hF : Fits p L g d ns nv) (hE : Expect p L g d ns e)
    (hn : (code p L g ent).next d e = some (some d')) : Fits p L g d' (ns + 1) nv := by
  cases late with
  | true =>
    obtain ⟨s, w, dn, tl, u1, u2, u4, u8, u16, tot, grp, acc, gx, cur, bal, pv, nt, c0, c1⟩ := d
    subst hs
    obtain ⟨R, n0, v0, hP, hEV, hns, hnv, hRV, hB, hpv⟩ := hF
    obtain ⟨pc, kind⟩ := e
    cases kind <;> simp only [code, succ, reduceCtorEq] at hn
    simp only [Expect] at hE
    rw [hE R n0 v0 hP hEV.1] at hn
    simp only [↓reduceIte, Option.some.injEq] at hn
    subst hn
    have hs := selN_pos bal
    exact ⟨n0, v0, hP, R, hEV.1, .inr ⟨bal, hB, hEV.2.2.2.2, by simp only at hns; omega,
      by omega, fun h => absurd h (by decide)⟩⟩
  | false =>
    obtain ⟨pc, kind⟩ := e
    cases kind <;> simp only [code, succ, hs, reduceCtorEq] at hn
    simp only [Expect, hs] at hE
    obtain ⟨R, n0, v0, hP, hEV, -⟩ := (by simpa only [Fits, hs] using hF : ∃ R n0 v0, _)
    rename_i mode a b c v ok
    rw [hE R n0 v0 hP hEV.1] at hn
    simp only [↓reduceIte, Option.map_eq_some_iff, Option.some.injEq, exists_eq_right,
      afterTiles] at hn
    split at hn
    · split at hn
      · simp only [Option.some.injEq] at hn
        subst hn
        exact fits_tilesD hs hF fun R' n0' v0' hP' hE' => by
          rw [hE'.unique hEV.1]; rfl
      · simp at hn
    · simp at hn

/-- **The second pass's start** after the first pass's choice. -/
theorem fits_pass2 {R : Nat} {bal : BitVec 64} {d : D} (hC : ChosenVals p L g R bal d ns nv) :
    Fits p L g (if scmp .gt .s (laneW L g) (paramW p.batch) = true then
      { d with site := .down .second, w := i32 0 } else { d with site := .word .second })
      ns nv := by
  obtain ⟨hPk, -, -, -, -, -, -, hns, hnv⟩ := hC
  have hP : PassStart p L g true ns nv := ⟨R, bal, hPk, by simpa using hns, by simpa using hnv⟩
  refine fits_ite (fun hb => ?_) (fun hb => ?_)
  · exact ⟨0, ns, nv, hP, ⟨fun _ h => absurd h (Nat.not_lt_zero _), by simp⟩, rfl, rfl,
      fun h => absurd rfl h, by simp [wv, reads, req, batchOf, Scan.late, hb]⟩
  · exact ⟨0, ns, nv, hP, ⟨fun _ h => absurd h (Nat.not_lt_zero _), by simp⟩, rfl, rfl,
      fun h => absurd rfl h, by simpa [reads, req, batchOf, Scan.late] using hb⟩

set_option maxHeartbeats 4000000 in
/-- The writeback's steps keep the first pass's choice; the last frees lead to the second pass. -/
theorem fits_next_write {d d' : D} {e : Event} (hs : ∃ R bal, ChosenVals p L g R bal d ns nv)
    (hsite : d.site ≠ .start ∧ (∀ k, d.site ≠ .word k) ∧ (∀ k, d.site ≠ .down k) ∧
      (∀ k j, d.site ≠ .up k j) ∧ (∀ k, d.site ≠ .total k) ∧ (∀ l, d.site ≠ .vote l) ∧
      (∀ l, d.site ≠ .pre l) ∧ (∀ l, d.site ≠ .tiles l) ∧ (∀ l, d.site ≠ .exit l))
    (hF : Fits p L g d ns nv) (hE : Expect p L g d ns e)
    (hn : (code p L g ent).next d e = some (some d')) : Fits p L g d' ns nv := by
  obtain ⟨s, w, dn, tl, u1, u2, u4, u8, u16, tot, grp, acc, gx, cur, bal', pv, nt, c0, c1⟩ := d
  obtain ⟨R, bal, hC⟩ := hs
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hsite
  obtain ⟨pc, kind⟩ := e
  cases s with
  | start => exact absurd rfl h1
  | word k => exact absurd rfl (h2 k)
  | down k => exact absurd rfl (h3 k)
  | up k j => exact absurd rfl (h4 k j)
  | total k => exact absurd rfl (h5 k)
  | vote l => exact absurd rfl (h6 l)
  | pre l => exact absurd rfl (h7 l)
  | tiles l => exact absurd rfl (h8 l)
  | exit l => exact absurd rfl (h9 l)
  | q0 =>
    cases kind <;> simp only [code, succ, reduceCtorEq] at hn
    rename_i a bs
    simp only [Expect] at hE
    rw [hE] at hn
    simp only [word32, Option.some.injEq] at hn
    subst hn
    exact ⟨R, bal, hC, rfl⟩
  | q1 =>
    obtain ⟨_, _, _, hc0⟩ := hF
    cases kind <;> simp only [code, succ, reduceCtorEq] at hn
    rename_i a bs
    simp only [Expect] at hE
    rw [hE] at hn
    simp only [word32, Option.some.injEq] at hn
    subst hn
    exact ⟨R, bal, hC, hc0, rfl⟩
  | ready st =>
    obtain ⟨_, _, _, hc0, hc1⟩ := hF
    cases kind <;> simp only [code, succ, reduceCtorEq, Option.some.injEq] at hn
    subst hn
    rename_i ok _ _
    cases ok
    · exact ⟨R, bal, hC, hc0, hc1⟩
    · exact ⟨R, bal, hC, hc0, hc1⟩
  | store st b =>
    obtain ⟨_, _, _, hc0, hc1⟩ := hF
    simp only [code, succ, Option.some.injEq] at hn
    subst hn
    fin_cases b <;> exact ⟨R, bal, hC, hc0, hc1⟩
  | commit st =>
    obtain ⟨_, _, _, hc0, hc1⟩ := hF
    fin_cases st <;> simp only [code, succ, Option.some.injEq] at hn <;> subst hn <;>
      exact ⟨R, bal, hC, hc0, hc1⟩
  | drain st =>
    obtain ⟨_, _, _, hc0, hc1⟩ := hF
    simp only [code, succ, Option.some.injEq] at hn
    subst hn
    exact ⟨R, bal, hC, hc0, hc1⟩
  | free st =>
    obtain ⟨_, _, _, hc0, hc1⟩ := hF
    fin_cases st
    · simp only [code, succ, Option.some.injEq] at hn
      subst hn
      exact ⟨R, bal, hC, hc0, hc1⟩
    · simp only [code, succ, Option.some.injEq] at hn
      subst hn
      exact fits_pass2 hC

set_option maxHeartbeats 4000000 in
/-- **The machine never gives up on a state that holds the reference values** when the event
returns what the reference says. -/
theorem next_ne {d : D} {e : Event} (hF : Fits p L g d ns nv) (hE : Expect p L g d ns e) :
    (code p L g ent).next d e ≠ some none := by
  obtain ⟨s, w, dn, tl, u1, u2, u4, u8, u16, tot, grp, acc, gx, cur, bal, pv, nt, c0, c1⟩ := d
  obtain ⟨pc, kind⟩ := e
  intro hn
  cases s with
  | word k | down k | up k _ | total k =>
    obtain ⟨r, n0, v0, hP, hR, hns, -⟩ := hF
    cases kind <;> simp only [code, succ, reduceCtorEq] at hn
    simp only [Expect] at hE
    rw [hE r n0 v0 hP hR hns] at hn
    simp [word32] at hn
  | pre l | tiles l =>
    obtain ⟨R, n0, v0, hP, hEV, hns, -⟩ := hF
    cases kind <;> simp only [code, succ, reduceCtorEq] at hn
    simp only [Expect] at hE
    first
      | (rw [hE R n0 v0 hP hEV.1 hns] at hn; simp [word32] at hn)
      | (rw [hE R n0 v0 hP hEV.1] at hn; cases l <;> simp at hn)
  | q0 | q1 =>
    cases kind <;> simp only [code, succ, reduceCtorEq] at hn
    simp only [Expect] at hE
    rw [hE] at hn
    simp [word32] at hn
  | ready st => cases kind <;> simp [code, succ] at hn
  | vote l => cases kind <;> simp [code, succ] at hn
  | store st b => simp [code, succ] at hn
  | commit st => fin_cases st <;> simp [code, succ] at hn
  | free st => fin_cases st <;> simp [code, succ] at hn
  | _ => simp [code, succ] at hn

/-- The shuffle and the full-mask ballot an event adds to the thread machine's counts. -/
abbrev sh (e : Event) : Nat := if Execution.isShfl e then 1 else 0
abbrev vt (e : Event) : Nat := if isFullVote e then 1 else 0

/-- An event is a shuffle at a shuffle site and a full-mask ballot at a ballot site. -/
theorem ev_counts {d : D} {e : Event} (hev : Ev p L g d e) :
    sh e = (if d.site.shfl then 1 else 0) ∧ vt e = (if d.site.ballot then 1 else 0) := by
  obtain ⟨pc, kind⟩ := e
  cases hs : d.site <;> simp only [Ev, hs] at hev
  case store => cases kind <;> first | exact ⟨rfl, rfl⟩ | exact absurd hev Bool.false_ne_true
  case word | q0 | q1 => rcases hev with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> exact ⟨rfl, rfl⟩
  case start => obtain ⟨_, _, _, rfl⟩ := hev; exact ⟨rfl, rfl⟩
  case down | up | total | pre | tiles => obtain ⟨_, _, rfl⟩ := hev; exact ⟨rfl, rfl⟩
  case vote => obtain ⟨_, rfl⟩ := hev; exact ⟨rfl, by simp only [vt, isFullVote_vote]; rfl⟩
  case ready => obtain ⟨_, rfl⟩ := hev; exact ⟨rfl, rfl⟩
  all_goals subst hev; exact ⟨rfl, rfl⟩

/-- **A state that holds the reference values steps to one** when the event returns what the
reference says, with the counts its event adds. -/
theorem fits_next {d d' : D} {e : Event} (hF : Fits p L g d ns nv) (hE : Expect p L g d ns e)
    (hev : Ev p L g d e) (hn : (code p L g ent).next d e = some (some d')) :
    Fits p L g d' (ns + sh e) (nv + vt e) := by
  obtain ⟨h1, h2⟩ := ev_counts hev
  rw [h1, h2]
  cases hs : d.site <;> simp only [Site.shfl, Site.ballot, Bool.false_eq_true, ↓reduceIte,
    Nat.add_zero]
  case start => exact fits_next_start hs hF hn
  case word k => exact fits_next_word hs hF hE hn
  case down k => exact fits_next_down hs hF hE hn
  case up k j => exact fits_next_up hs hF hE hn
  case total k => exact fits_next_total hs hF hE hn
  case vote l => exact fits_next_vote hs hF hE hn
  case pre l => exact fits_next_pre hs hF hE hn
  case tiles l => exact fits_next_tiles hs hF hE hn
  case exit l =>
    obtain ⟨s, w, dn, tl, u1, u2, u4, u8, u16, tot, grp, acc, gx, cur, bal, pv, nt, c0, c1⟩ := d
    subst hs
    simp [code, succ] at hn
  all_goals
    refine fits_next_write ?_ (by simp [hs]) hF hE hn
    simp only [Fits, hs] at hF
    first
      | exact hF
      | (obtain ⟨R, bal, h, -⟩ := hF; exact ⟨R, bal, h⟩)

end
end PTX.Kernels.TmlFa4Fwd.Proof2.Epilogue
