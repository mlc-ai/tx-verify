-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Common.ScriptFacts
public import Kernels.InklingRelDecode.Proof.Common.WorkerBalance
public import Kernels.InklingRelDecode.Proof.Common.EndTime

@[expose] public section

/-! # The collectives of the MMA warp

The startup's shuffle, then the halves of the loop (the QK half of iteration 0, then for each
later iteration its QK half while there are blocks left and its PV half), each with four
collectives (the barrier, the broadcast, the second barrier and the election), then the two final
collectives. `mmaCn lim n` is the pc of the `n`-th, `mmaSlot lim n` its time. -/

namespace PTX.Kernels.InklingRelDecode.Proof
open PTX PTX.Flow

/-- The four collective sites of a half (`true`: QK, `false`: PV). -/
def mmaFam (k : Bool) (q : Nat) : Mma.Site :=
  ((if k then [Mma.Site.qkBar, .qkShfl, .qkBar2, .qkElect]
    else [.pvBar, .pvShfl, .pvBar2, .pvElect])[q]?).getD .dispatch

/-- Half `H` of the loop is a QK half. -/
def mmaKind (lim H : Nat) : Bool := decide (H = 0 ∨ (H % 2 = 1 ∧ (H + 1) / 2 < lim))

/-- The site of the `n`-th collective of the loop. -/
def mmaHalf (lim n : Nat) : Mma.Site := mmaFam (mmaKind lim ((n - 1) / 4)) ((n - 1) % 4)

def mmaCn (lim n : Nat) : Option Nat :=
  if n = 0 then some 17 else if n ≤ 8 * lim then some (mmaHalf lim n).pc
  else if n = 8 * lim + 1 then some 2550 else if n = 8 * lim + 2 then some 2551 else none

def mmaSlot (lim n : Nat) : Nat :=
  if n = 0 then 24 else if n ≤ 8 * lim then
    Mma.slotTime (((n - 1) / 4 + 1) / 2) + (mmaHalf lim n).position
  else if n = 8 * lim + 1 then Lib.Slots.finish - 100 else Lib.Slots.finish - 96

/-- The half (`true`: QK) of a loop site and the collectives it has made of it. -/
def Mma.Site.fam : Mma.Site → Option (Bool × Nat)
  | .qkBar => some (true, 0) | .kvWait | .qkShfl => some (true, 1) | .qkBar2 => some (true, 2)
  | .qkElect => some (true, 3) | .qk _ | .qkCommit => some (true, 4)
  | .pvBar => some (false, 0) | .pWait | .pvShfl => some (false, 1) | .pvBar2 => some (false, 2)
  | .pvElect => some (false, 3) | .pv _ | .pvCommit1 | .pvCommit2 => some (false, 4)
  | _ => none

/-- The index of the half a loop site of iteration `i` is in. -/
def mmaHalfIdx (k : Bool) (i lim : Nat) : Nat :=
  if k then 2 * i - 1 else min (2 * i) (2 * lim - 1)

/-- The static facts of a loop site against its half's four collectives. -/
def famCheck (s : Mma.Site) : Bool :=
  match s.fam with
  | none => true
  | some (k, q) =>
    (!s.coll || (decide (q < 4) && mmaFam k q == s)) &&
    (s.coll || (List.range 4).all fun q' => decide (q' < q) ||
      decide (s.position < (mmaFam k q').position)) && (!k || decide (s.position < 14))

theorem famCheck_all (s : Mma.Site) : famCheck s = true := by
  cases s <;> first | decide +kernel | (rename_i j; revert j; decide +kernel)

theorem mma_pos_le (s : Mma.Site) : s.position ≤ 28 := by
  cases s <;> first | decide +kernel | (rename_i j; revert j; decide +kernel)

private theorem fam_coll : ∀ k q, q < 4 → (mmaFam k q).coll = true := by decide +kernel

theorem mmaCn_warp {lim n x : Nat} (h : mmaCn lim n = some x) : isWarpAt x = true := by
  unfold mmaCn at h
  split_ifs at h with h0 h1 h2 h3
  · cases h; decide +kernel
  · cases h; rw [mma_coll]; exact fam_coll _ _ (Nat.mod_lt _ (by omega))
  · cases h; decide +kernel
  · cases h; decide +kernel

private theorem kind_iff {lim H : Nat} : mmaKind lim H = true ↔
    (H = 0 ∨ (H % 2 = 1 ∧ (H + 1) / 2 < lim)) := by simp [mmaKind]

/-- **A site of the loop** of iteration `i` is at the script position of its half. -/
theorem mma_loop_facts {lim i : Nat} {s : Mma.Site} {k : Bool} {q : Nat}
    (hf : s.fam = some (k, q)) (hb : lim ≤ 2147483646)
    (hk : k = true → i < lim) (hv : k = false → 0 < i ∧ i ≤ lim) :
    ScriptFacts (mmaCn lim) (mmaSlot lim) (1 + 4 * mmaHalfIdx k i lim + q) s.pc
      (Mma.slotTime i + s.position) := by
  have chk := famCheck_all s
  have pb := mma_pos_le s
  simp only [famCheck, hf, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    decide_eq_true_eq, beq_iff_eq, List.all_eq_true, List.mem_range] at chk
  obtain ⟨⟨c1, c2⟩, c3⟩ := chk
  have hH : mmaHalfIdx k i lim < 2 * lim ∧ mmaKind lim (mmaHalfIdx k i lim) = k ∧
      (mmaHalfIdx k i lim + 1) / 2 = i := by
    cases k
    · obtain ⟨h1, h2⟩ := hv rfl
      simp only [mmaHalfIdx, Bool.false_eq_true, ↓reduceIte]
      refine ⟨by omega, ?_, by omega⟩
      simp only [mmaKind, decide_eq_false_iff_not]
      omega
    · have := hk rfl
      simp only [mmaHalfIdx, ↓reduceIte]
      refine ⟨by omega, ?_, by omega⟩
      simp only [mmaKind, decide_eq_true_eq]
      omega
  obtain ⟨hlt, hkind, hit⟩ := hH
  generalize mmaHalfIdx k i lim = H at *
  by_cases hc : s.coll = true
  · obtain ⟨hq, hsite⟩ := c1.resolve_left (by simp [hc])
    have n1 : 1 ≤ 1 + 4 * H + q := by omega
    have n2 : 1 + 4 * H + q ≤ 8 * lim := by omega
    have e1 : (1 + 4 * H + q - 1) / 4 = H := by omega
    have e2 : (1 + 4 * H + q - 1) % 4 = q := by omega
    have hh : mmaHalf lim (1 + 4 * H + q) = s := by
      simp only [mmaHalf, e1, e2, hkind, hsite]
    refine ⟨?_, fun _ => ?_, fun h => absurd h (by rw [mma_coll, hc]; simp)⟩
    · rw [mma_coll, hc]
      simp only [mmaCn, show ¬ 1 + 4 * H + q = 0 by omega, n2, hh, ↓reduceIte]
    · simp only [mmaSlot, show ¬ 1 + 4 * H + q = 0 by omega, n2, hh, e1, hit, ↓reduceIte]
  · have hf' : s.coll = false := by simpa using hc
    have wf : isWarpAt s.pc = false := by rw [mma_coll, hf']
    obtain ⟨hl⟩ : Nonempty (∀ q' < 4, q' < q ∨ s.position < (mmaFam k q').position) :=
      ⟨fun q' h => by simpa using c2.resolve_left (by simp [hf']) q' h⟩
    refine ⟨?_, fun h => absurd h (by simp [wf]), fun _ n hn hle => ?_⟩
    · simp only [wf, Bool.false_eq_true, false_iff]
      intro h
      have := mmaCn_warp h
      simp [wf] at this
    · have n0 : n ≠ 0 := by omega
      have st : ∀ x, Mma.slotTime x = 1100 + 400 * x := fun x => by
        simp [Mma.slotTime, Lib.Slots.mma, Lib.Slots.frame, Lib.Slots.stride]; omega
      have fin : Lib.Slots.finish = 1000 + 400 * 8589934596 := by
        simp [Lib.Slots.finish, Lib.Slots.frame, Lib.Slots.stride]
      by_cases hin : n ≤ 8 * lim
      · simp only [mmaSlot, n0, hin, ↓reduceIte, mmaHalf, st]
        generalize hH' : (n - 1) / 4 = H'
        generalize hq' : (n - 1) % 4 = q'
        have hq4 : q' < 4 := by omega
        have hHH : H ≤ H' := by omega
        have hH2 : H' < 2 * lim := by omega
        by_cases hsame : H' = H
        · subst hsame
          rw [hkind]
          have := (hl q' hq4).resolve_left (by omega)
          rw [← hit] at *
          omega
        · by_cases hi' : (H' + 1) / 2 = i
          · have kT : k = true := by
              cases k
              · simp only [mmaKind, decide_eq_false_iff_not] at hkind
                omega
              · rfl
            subst kT
            simp only [mmaKind, decide_eq_true_eq] at hkind
            have k' : mmaKind lim H' = false := by
              simp only [mmaKind, decide_eq_false_iff_not]; omega
            rw [k']
            have := c3.resolve_left (by simp)
            have : 14 ≤ (mmaFam false q').position := by
              have : ∀ q, q < 4 → 14 ≤ (mmaFam false q).position := by decide +kernel
              exact this q' hq4
            omega
          · omega
      · have hn12 : n = 8 * lim + 1 ∨ n = 8 * lim + 2 := by
          by_contra hne
          apply Option.isSome_iff_ne_none.mp hn
          simp [mmaCn, n0, hin, show n ≠ 8 * lim + 1 by omega, show n ≠ 8 * lim + 2 by omega]
        have hfin : Mma.slotTime i + s.position < Lib.Slots.finish - 100 := by
          rw [st, fin]; omega
        unfold mmaSlot
        split_ifs <;> omega

/-- The ledger's count at a site of the loop. -/
theorem mma_loop_count {d : Mma.D} {n : Cls → Nat} {k : Bool} {q : Nat}
    (hf : d.site.fam = some (k, q)) (hs : d.site.skipped = 0) (inv : Mma.Inv d)
    (p1 : n (.poll 2462) = (Mma.polls d).1) (p2 : n (.poll 2510) = (Mma.polls d).2)
    (fin : n (.atPc 2550) + n (.atPc 2551) = d.site.fin)
    (cnt : n .coll + Mma.remain d.site + n .skip = 1 + 4 * (n (.poll 2462) + n (.poll 2510)) +
      n (.atPc 2550) + n (.atPc 2551) + d.site.waiting) (sk : n .skip = 0) :
    n .coll = 1 + 4 * mmaHalfIdx k d.i d.limit + q := by
  obtain ⟨s, i, w⟩ := d
  cases s <;> simp only [Mma.Site.fam, reduceCtorEq, Option.some.injEq, Prod.mk.injEq] at hf <;>
    simp only [Mma.Inv, Mma.Site.fin, Mma.Site.waiting, Mma.remain, Mma.Site.skipped] at * <;>
    simp only [Mma.polls, mmaHalfIdx, Mma.D.limit] at * <;>
    obtain ⟨rfl, rfl⟩ := hf <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega

private theorem mmaCn_fin1 (lim : Nat) : mmaCn lim (8 * lim + 1) = some 2550 := by
  simp [mmaCn]

private theorem mmaCn_fin2 (lim : Nat) : mmaCn lim (8 * lim + 2) = some 2551 := by
  simp [mmaCn]

private theorem mmaSlot_fin1 (lim : Nat) : mmaSlot lim (8 * lim + 1) = Lib.Slots.finish - 100 := by
  simp [mmaSlot]

private theorem mmaSlot_fin2 (lim : Nat) : mmaSlot lim (8 * lim + 2) = Lib.Slots.finish - 96 := by
  simp [mmaSlot]

/-- What the ledger and the references say of the MMA lane's counts at a state. -/
def MmaCounts (d : Mma.D) (n : Cls → Nat) : Prop :=
  n (.poll 2462) = (Mma.polls d).1 ∧ n (.poll 2510) = (Mma.polls d).2 ∧
  n (.atPc 2550) + n (.atPc 2551) = d.site.fin ∧
  n .coll + Mma.remain d.site + n .skip = 1 + 4 * (n (.poll 2462) + n (.poll 2510)) +
    n (.atPc 2550) + n (.atPc 2551) + d.site.waiting ∧ n .skip = 0 ∧ d.site.skipped = 0

private theorem mma_off {lim c pc clk : Nat} (hpc : isWarpAt pc = false)
    (hlt : ∀ n, (mmaCn lim n).isSome = true → c ≤ n → clk < mmaSlot lim n) :
    ScriptFacts (mmaCn lim) (mmaSlot lim) c pc clk := by
  refine ⟨?_, fun h => by simp [hpc] at h, fun _ => hlt⟩
  simp only [hpc, Bool.false_eq_true, false_iff]
  intro e
  have := mmaCn_warp e
  simp [hpc] at this

theorem mmaSlot_big (lim : Nat) {n : Nat} (h : 1 ≤ n) : 1100 ≤ mmaSlot lim n := by
  simp only [mmaSlot, show ¬ n = 0 by omega, ↓reduceIte, Mma.slotTime, Lib.Slots.mma,
    Lib.Slots.frame, Lib.Slots.finish, Lib.Slots.stride]
  split_ifs <;> omega

private theorem fam_bounds {d : Mma.D} {k : Bool} {q : Nat} (hf : d.site.fam = some (k, q))
    (inv : Mma.Inv d) : (k = true → d.i < d.limit) ∧ (k = false → 0 < d.i ∧ d.i ≤ d.limit) ∧
      d.limit ≤ 2147483646 ∧ d.site.hasCount = true := by
  obtain ⟨s, i, w⟩ := d
  cases s <;> simp_all [Mma.Site.fam, Mma.Inv, Mma.D.limit, Mma.Site.hasCount]

private theorem mma_late {lim : Nat} {n : Cls → Nat} (pc clk : Nat) (hpc : isWarpAt pc = false)
    (e : n .coll = 3 + 8 * lim) :
    ScriptFacts (mmaCn lim) (mmaSlot lim) (n .coll) pc clk := by
  refine mma_off hpc fun m hm le => ?_
  simp [mmaCn, show m ≠ 0 by omega, show ¬ m ≤ 8 * lim by omega,
    show m ≠ 8 * lim + 1 by omega, show m ≠ 8 * lim + 2 by omega] at hm

private theorem mma_early {lim : Nat} {n : Cls → Nat} (pc clk : Nat) (hpc : isWarpAt pc = false)
    (hc : clk < 1100) (e : n .coll = 1) :
    ScriptFacts (mmaCn lim) (mmaSlot lim) (n .coll) pc clk :=
  mma_off hpc fun m _ le => by have := mmaSlot_big lim (n := m); omega

theorem mmaCn_lt {lim n : Nat} (h : (mmaCn lim n).isSome = true) : n < 3 + 8 * lim := by
  by_contra hn
  have : mmaCn lim n = none := by
    simp [mmaCn, show n ≠ 0 by omega, show ¬ n ≤ 8 * lim by omega,
      show n ≠ 8 * lim + 1 by omega, show n ≠ 8 * lim + 2 by omega]
  simp [this] at h

/-- **A dispatch state of the MMA's warp** against its script. -/
theorem mma_dispatch_facts {lo hi : Nat} {dd : Dispatch.D} {n : Cls → Nat} {clk : Nat}
    (ref : DispatchRef 7 lo hi dd n) (sk : n .skip = 0)
    (cnt : n .coll + n .skip = 1 + 4 * (n (.poll 2462) + n (.poll 2510)) + n (.atPc 2550) +
      n (.atPc 2551)) (hclk : dd.round = 0 → clk < 300) :
    ScriptFacts (mmaCn (Mma.runCount hi)) (mmaSlot (Mma.runCount hi)) (n .coll) dd.site.pc clk ∧
      (dd.site.pc = 2855 → ∀ j, (mmaCn (Mma.runCount hi) j).isSome = true → j < n .coll) := by
  have ok : ∀ s : Dispatch.Site, isWarpAt s.pc = false := fun s => by
    cases s <;> decide +kernel
  obtain ⟨al, -, r0, r1⟩ := ref
  refine ⟨?_, fun h j hj => ?_⟩
  · by_cases h : dd.round = 0
    · obtain ⟨a, b, c, d⟩ := r0 h
      exact mma_early _ _ (ok _) (by have := hclk h; omega) (by omega)
    · obtain ⟨a, b, c⟩ := (r1 h).2 rfl
      exact mma_late _ _ (ok _) (by omega)
  · obtain ⟨a, b, c⟩ := (r1 (dispatch_ret_round al h)).2 rfl
    have := mmaCn_lt hj
    omega

/-- **A state of the MMA loop's machine** against its script. -/
theorem mma_site_facts {hi : Nat} {d : Mma.D} {n : Cls → Nat} (ref : Mma.Ref hi d)
    (inv : Mma.Inv d) (cnt : MmaCounts d n) :
    ScriptFacts (mmaCn (Mma.runCount hi)) (mmaSlot (Mma.runCount hi)) (n .coll) d.site.pc
      (Mma.time d) := by
  obtain ⟨p1, p2, fin, led, sk, hs⟩ := cnt
  by_cases hf : d.site.fam.isSome = true
  · obtain ⟨⟨k, q⟩, hfam⟩ := Option.isSome_iff_exists.mp hf
    obtain ⟨hk, hv, hb, hc⟩ := fam_bounds hfam inv
    have hlim : d.limit = hi := Mma.ref_count ref hc
    have e : Mma.runCount hi = d.limit := by simp [Mma.runCount, hlim] at hb ⊢; omega
    have tm : Mma.time d = Mma.slotTime d.i + d.site.position := by
      obtain ⟨s, i, w⟩ := d
      cases s <;> first | rfl | simp [Mma.Site.fam] at hfam
    rw [e, tm, mma_loop_count hfam hs inv p1 p2 fin led sk]
    exact mma_loop_facts hfam hb hk hv
  · have hnone : d.site.fam = none := by simpa using hf
    obtain ⟨s, i, w⟩ := d
    have early := mma_early (n := n) (lim := Mma.runCount hi)
    have late := mma_late (n := n) (lim := Mma.runCount hi)
    have ok : ∀ s : Mma.Site, isWarpAt s.pc = s.coll := mma_coll
    cases s <;> try first | (simp [Mma.Site.fam] at hnone; done) |
      (simp [Mma.Site.skipped] at hs; done)
    all_goals simp only [Mma.polls, Mma.Site.fin, Mma.Site.waiting, Mma.remain, Mma.D.limit]
      at p1 p2 fin led
    · exact early _ _ (by rw [ok]; rfl) (by simp [Mma.time, Lib.Slots.enter]) (by omega)
    · exact early _ _ (by rw [ok]; rfl) (by simp [Mma.time]) (by omega)
    · exact early _ _ (by rw [ok]; rfl) (by simp [Mma.time, Lib.Slots.reuse]) (by omega)
    all_goals have hlim := Mma.ref_count ref (by simp [Mma.Site.hasCount])
    all_goals simp only [Mma.D.limit] at hlim
    all_goals rw [hlim] at p1 p2
    · rw [show n .coll = 8 * Mma.runCount hi + 1 by omega]
      refine ⟨?_, fun _ => ?_, fun h => absurd h (by rw [ok]; simp [Mma.Site.coll])⟩
      · rw [mmaCn_fin1]
        exact ⟨fun _ => rfl, fun _ => by rw [ok]; rfl⟩
      · rw [mmaSlot_fin1]; rfl
    · rw [show n .coll = 8 * Mma.runCount hi + 2 by omega]
      refine ⟨?_, fun _ => ?_, fun h => absurd h (by rw [ok]; simp [Mma.Site.coll])⟩
      · rw [mmaCn_fin2]
        exact ⟨fun _ => rfl, fun _ => by rw [ok]; rfl⟩
      · rw [mmaSlot_fin2]; rfl
    all_goals exact late _ _ (by rw [ok]; rfl) (by omega)

private theorem fam_pos : (∀ k, ∀ q < 4, ∀ q' < 4, q < q' →
      (mmaFam k q).position < (mmaFam k q').position) ∧
    (∀ q < 4, ∀ q' < 4, (mmaFam true q).position < (mmaFam false q').position) := by
  decide +kernel

private theorem slot_loop_le {lim n : Nat} (h : n ≤ 8 * lim) (n1 : 1 ≤ n) :
    mmaSlot lim n ≤ Mma.slotTime lim + 28 := by
  have := mma_pos_le (mmaHalf lim n)
  simp only [mmaSlot, show ¬ n = 0 by omega, h, ↓reduceIte, Mma.slotTime, Lib.Slots.mma,
    Lib.Slots.frame, Lib.Slots.stride]
  have : ((n - 1) / 4 + 1) / 2 ≤ lim := by omega
  omega

/-- **The slots of the script rise.** -/
theorem mmaSlot_mono (lim : Nat) (hlim : lim ≤ 2147483646) {a b : Nat} (hab : a < b)
    (hb : (mmaCn lim b).isSome = true) :
    mmaSlot lim a < mmaSlot lim b := by
  have hbl := mmaCn_lt hb
  by_cases a0 : a = 0
  · subst a0
    have := mmaSlot_big lim (n := b) (by omega)
    rw [show mmaSlot lim 0 = 24 by simp [mmaSlot]]
    omega
  have fin : Lib.Slots.finish = 1000 + 400 * 8589934596 := by
    simp [Lib.Slots.finish, Lib.Slots.frame, Lib.Slots.stride]
  have st : ∀ x, Mma.slotTime x = 1100 + 400 * x := fun x => by
    simp [Mma.slotTime, Lib.Slots.mma, Lib.Slots.frame, Lib.Slots.stride]; omega
  by_cases bl : b ≤ 8 * lim
  · have pa := mma_pos_le (mmaHalf lim a)
    have pb := mma_pos_le (mmaHalf lim b)
    simp only [mmaSlot, a0, show ¬ b = 0 by omega, bl, show a ≤ 8 * lim by omega, ↓reduceIte, st]
    unfold mmaHalf at pa pb ⊢
    generalize hHa : (a - 1) / 4 = Ha at *
    generalize hHb : (b - 1) / 4 = Hb at *
    have qa : (a - 1) % 4 < 4 := by omega
    have qb : (b - 1) % 4 < 4 := by omega
    by_cases hs : Ha = Hb
    · subst hs
      have := fam_pos.1 (mmaKind lim Ha) _ qa _ qb (by omega)
      omega
    · by_cases hi : (Ha + 1) / 2 = (Hb + 1) / 2
      · have kt : mmaKind lim Ha = true := by
          simp only [mmaKind, decide_eq_true_eq]; omega
        have kf : mmaKind lim Hb = false := by
          simp only [mmaKind, decide_eq_false_iff_not]; omega
        rw [kt, kf] at *
        have := fam_pos.2 _ qa _ qb
        omega
      · omega
  · have hb12 : b = 8 * lim + 1 ∨ b = 8 * lim + 2 := by omega
    by_cases al : a ≤ 8 * lim
    · have h1 := slot_loop_le al (by omega)
      rw [st] at h1
      have h2 : mmaSlot lim b = Lib.Slots.finish - 100 ∨ mmaSlot lim b = Lib.Slots.finish - 96 := by
        rcases hb12 with h | h <;> subst h
        · exact .inl (mmaSlot_fin1 lim)
        · exact .inr (mmaSlot_fin2 lim)
      rw [fin] at h2
      rcases h2 with h2 | h2 <;> rw [h2] <;> omega
    · have : a = 8 * lim + 1 ∧ b = 8 * lim + 2 := by omega
      obtain ⟨rfl, rfl⟩ := this
      rw [mmaSlot_fin1, mmaSlot_fin2, fin]
      omega

theorem mma_pc_ne (s : Mma.Site) : s.pc ≠ 2855 := by
  cases s <;> first | decide +kernel | (rename_i j; revert j; decide +kernel)

end PTX.Kernels.InklingRelDecode.Proof
