-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LdWarp.Fits
public import Kernels.TmlFa4Fwd.Proof.Loader.Export.AcqRing
public import Kernels.TmlFa4Fwd.Proof.Progress.MmaPoll
public import Kernels.TmlFa4Fwd.Proof.SmWarp.Export.Follow
public import Kernels.TmlFa4Fwd.Proof.Protocol.KV.Obj
public import Lemmas.Protocol.NoIncRing
public import Lemmas.Protocol.RecordCountPair
import Kernels.TmlFa4Fwd.Proof.Common.NoUb
import Kernels.TmlFa4Fwd.Proof.Common.Sound
import Kernels.TmlFa4Fwd.Proof.Epilogue.Position
import Kernels.TmlFa4Fwd.Proof.LdWarp.Src
import Kernels.TmlFa4Fwd.Proof.Loader.Export.ArrRing
import Kernels.TmlFa4Fwd.Proof.Lib.Prev
import Kernels.TmlFa4Fwd.Proof.Mma.Warp
import Kernels.TmlFa4Fwd.Proof.Protocol.Bar.Corr
import Kernels.TmlFa4Fwd.Proof.Protocol.Credit.Handoff
import Kernels.TmlFa4Fwd.Proof.Protocol.KV.Bound
import Kernels.TmlFa4Fwd.Proof.Loader.Export.Parity
import Kernels.TmlFa4Fwd.Proof.Loader.Export.TimeLag
import Kernels.TmlFa4Fwd.Proof.Protocol.Mbar.Init
import Kernels.TmlFa4Fwd.Proof.Mma.Export.Coll
import Kernels.TmlFa4Fwd.Proof.Protocol.Tmem.MmaNoUb
import Kernels.TmlFa4Fwd.Proof.Mma.Export.Ring
import Kernels.TmlFa4Fwd.Proof.Protocol.Ready.Arrive
import Kernels.TmlFa4Fwd.Proof.Protocol.KV.TileAgree
import Lemmas.Flow.Counter32
import Lemmas.Kernel.Progress.HandoffBlockers
import Lemmas.Kernel.Safety.StateInv
import Lemmas.Order.ElectLe
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The loader half of the MMA warp's poll premise: the lanes of warp 12

A lane of warp 12 has made no more elections than any other lane of the warp at the end of that
lane's trace (`ElectOrd.elections_le`, every election of the kernel has the full mask). Along the
pipeline each release of the K/V ring follows an election after its acquisition (`rel_le_acq`, a
check over the places), so the electing lane's commits to an empty slot are at most another
lane's successful polls of the full slot (`com_le_lane`). With `kv_phase` this bounds a K/V full
barrier's final phase by the polls of any lane of the warp plus one (`kv_bound_lane`).

The K/V poll (`kv_lag`) is the library's no-increment hand-off (`Sched.Lag.blk_noInc`) with the
schedule of the K/V hand-off: a loader lane short of packet `i` is before `Ld.bound p i`
(`Loader.ld_early`), which is before the poll of ring index `i` (`Mm.kv_time`), and an
exited loader lane has made every arrive-on of the tile, more than the poll's ring index
(`ld_end`, the tile agreement). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.TmlFa4Fwd.Proof.Mma (RefQ electAll pq ringRel ringAcq ringCount)
open PTX.Flow.Arith32 (addi)

noncomputable section
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-! ### Releases against acquisitions -/

theorem pq_lin (x q r : Nat) : pq x q r = pq x q 0 + if 20 ≤ x ∧ x < 60 then r else 0 := by
  unfold pq; split_ifs <;> omega

theorem electAll_lin (q r : Nat) : electAll q r = electAll q 0 + 8 * r := by
  simp only [electAll, pq_lin _ q r]; norm_num; omega

theorem ringRel_lin (q r : Nat) : ringRel q r = ringRel q 0 + 2 * r := by
  simp only [ringRel, pq_lin _ q r]; norm_num; omega

theorem ringAcq_lin (q r : Nat) : ringAcq q r = ringAcq q 0 + 2 * r := by
  simp only [ringAcq, pq_lin _ q r]; norm_num; omega

/-- The K/V polls' places. -/
abbrev KvPlace (q : Nat) : Prop := q = 2 ∨ q = 20 ∨ q = 29 ∨ q = 64

set_option maxRecDepth 200000 in
theorem rel_acq_table : ∀ qc < 101, ∀ q ∈ [2, 20, 29, 64],
    (ringRel qc 0 : Int) - ringAcq q 0 ≤ 2 * (-(((electAll q 0 : Int) - electAll qc 0) / 8)) := by
  decide

/-- **A lane with no more elections has released no more ring indices than another lane at a K/V
poll has acquired.** -/
theorem rel_le_acq {qc rc q r : Nat} (hqc : qc ≤ 100) (hq : KvPlace q)
    (h : electAll qc rc ≤ electAll q r) : ringRel qc rc ≤ ringAcq q r := by
  have ht := rel_acq_table qc (by omega) q (by rcases hq with rfl | rfl | rfl | rfl <;> simp)
  rw [electAll_lin qc rc, electAll_lin q r] at h
  rw [ringRel_lin qc rc, ringAcq_lin q r]
  omega

theorem ord_le (s : Mma.Site) : s.ord ≤ 100 := by
  cases s
  case wt k => revert k; decide
  case sh k => revert k; decide
  case eq b => revert b; decide
  case qk b x => revert b x; decide
  case ce c => revert c; decide
  case cm c => revert c; decide
  case ep b => revert b; decide
  case pv b j => revert b j; decide
  case mw b x => revert b x; decide
  all_goals (simp only [Mma.Site.ord]; try split) <;> omega

theorem commitAt_ring (q r : Nat) (j : Fin 3) :
    Mma.commitAt q r (56 + 8 * j.val) = ringCount (ringRel q r) j.val := by
  fin_cases j <;> simp [Mma.commitAt]

theorem acqAt_ring (q r : Nat) (j : Fin 3) :
    Mma.acqAt q r (32 + 8 * j.val) = ringCount (ringAcq q r) j.val := by
  fin_cases j <;> simp [Mma.acqAt]

/-! ### The electing lane's commits against another lane's polls -/

set_option maxHeartbeats 4000000 in
/-- **A lane of warp 12's commits to empty slot `j` are at most the successful polls of full slot
`j` that another lane of the warp, at a K/V poll at the end of its trace, has made.** -/
theorem com_rel (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) {c : Nat}
    (hc : c < L.threads) (hc12 : Prologue.warpIndex L c = 12) (hw : SameWarp L c g)
    {d : Mma.D} {n : Cls → Nat} {r : Nat} {w : Bool}
    (hσ : Frame.stateAt (thread p L) X g (X.tr g).length = some (some (Mma.minj p L g d n)))
    (hQ : RefQ p L g d.site.ord d.v (Mma.rc n) r w) (j : Fin 3) :
    ∃ qc rc, qc ≤ 100 ∧ electAll qc rc ≤ electAll d.site.ord r ∧
      (X.tr c).countP (commitsTo (obj L c (56 + 8 * j.val))) ≤ ringCount (ringRel qc rc) j.val := by
  have hReads := cuQReadsFromLaunch hp hX
  have hG := fun k => Mma.good hp hX hReads hc hc12 k
  have hlive := warp12_live hp hX hFw hc hc12
  obtain ⟨k, ⟨σ, n'⟩, hσc, -, hcnt⟩ := Frame.end_countP hX hc (fun k => (hG k).1) hlive
  rw [hcnt (commitsTo (obj L c (56 + 8 * j.val))) (fun _ => rfl)]
  have h1 : ((X.tr c).take k).countP (commitsTo (obj L c (56 + 8 * j.val))) =
      ((X.tr c).take k).countP (cls L c (.mma (.commit (obj L c (56 + 8 * j.val))))) := rfl
  rw [h1, count hσc]
  have hR := (hG k).2 _ hσc
  have h00 : electAll 0 0 = 0 := by decide
  rcases σ with s | ⟨i, d'⟩
  · exact ⟨0, 0, by omega, by omega, by rw [(hR.2.2.1 _).2]; exact Nat.zero_le _⟩
  cases i with
  | mma =>
    rcases d' with s0 | ⟨⟨⟩, d'⟩
    · exact ⟨0, 0, by omega, by omega, by rw [(hR.2.2.1 _).2]; exact Nat.zero_le _⟩
    have hub0 : n' .ub = 0 := by
      by_contra hne
      obtain ⟨j', -, ⟨pc, kind⟩, hf, hcl⟩ := exists_of_count hσc (Nat.pos_of_ne_zero hne)
      cases kind <;> simp [cls] at hcl
      exact Mma.mma_noUb hp hX hFw hc hc12 hf _ rfl
    obtain ⟨r', w', hQ', -⟩ := (hR hub0).1
    have hcom := hQ'.com (56 + 8 * j.val)
    rw [show n' (.mma (.commit (obj L c (56 + 8 * j.val)))) = _ from hcom, commitAt_ring]
    have he1 := mma_elections hX hσc hQ'
    have he2 := mma_elections hX hσ hQ
    have hle := ElectOrd.elections_le hX (fun h => elect_full hX h) hw k
    rw [he1, he2] at hle
    refine ⟨d'.site.ord, r', ord_le _, hle, ?_⟩
    cases w' <;> simp only [ite_true, Bool.false_eq_true, ite_false] <;> omega
  | _ => exact hR.elim

/-- **A lane of warp 12's commits to empty slot `j` are at most the successful polls of full slot
`j` that another lane of the warp, at a K/V poll at the end of its trace, has made.** -/
theorem com_le_lane (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) {c : Nat}
    (hc : c < L.threads) (hc12 : Prologue.warpIndex L c = 12) (hw : SameWarp L c g)
    {d : Mma.D} {n : Cls → Nat} {r : Nat} {w : Bool}
    (hσ : Frame.stateAt (thread p L) X g (X.tr g).length = some (some (Mma.minj p L g d n)))
    (hQ : RefQ p L g d.site.ord d.v (Mma.rc n) r w) (hq : KvPlace d.site.ord) (j : Fin 3) :
    (X.tr c).countP (commitsTo (obj L c (56 + 8 * j.val))) ≤
      ringCount (ringAcq d.site.ord r) j.val := by
  obtain ⟨qc, rc, hqc, hle, hcom⟩ := com_rel hp hX hFw hc hc12 hw hσ hQ j
  have := Mma.ringCount_mono (rel_le_acq hqc hq hle) j.val
  omega

/-- **The K/V bound for any lane of warp 12** at a K/V poll at the end of its trace: the full
barrier's final phase is at most that lane's successful polls of it plus one. -/
theorem kv_bound_lane (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) (hg : g < L.threads)
    (hg12 : Prologue.warpIndex L g = 12) {d : Mma.D} {n : Cls → Nat} {r : Nat} {w : Bool}
    (hσ : Frame.stateAt (thread p L) X g (X.tr g).length = some (some (Mma.minj p L g d n)))
    (hQ : RefQ p L g d.site.ord d.v (Mma.rc n) r w) (hq : KvPlace d.site.ord) (j : Fin 3)
    {stF : MBarrier.State}
    (hst : MBarrier.stateBefore (X.objects (obj L g (32 + 8 * j.val)))
      (X.objects (obj L g (32 + 8 * j.val))).length = some stF) :
    stF.phase ≤ ringCount (ringAcq d.site.ord r) j.val + 1 := by
  obtain ⟨c, h12, hcta, hle⟩ := kv_phase hp hX hFw hg j hst
  have hc : c < L.threads := thread_lt_of_cta hg hcta
  have hw : SameWarp L c g := by
    refine ⟨⟨hc, hg, hcta⟩, ?_⟩
    simp only [Prologue.warpIndex] at h12 hg12
    omega
  have := com_le_lane hp hX hFw hc h12 hw hσ hQ hq j
  rw [show obj L c (56 + 8 * j.val) = obj L g (56 + 8 * j.val) by simp only [obj, hcta]] at this
  omega

/-! ### The poll, its ring index and the tile -/

/-- **A K/V poll** is at a K/V place and polls the slot of its ring index `ringAcq q r`. -/
theorem ringAcq_2 (r : Nat) : ringAcq 2 r = 2 * r := by
  rw [ringAcq_lin]; have : ringAcq 2 0 = 0 := by decide
  omega
theorem ringAcq_20 (r : Nat) : ringAcq 20 r = 2 * r + 1 := by
  rw [ringAcq_lin]; have : ringAcq 20 0 = 1 := by decide
  omega
theorem ringAcq_29 (r : Nat) : ringAcq 29 r = 2 * r + 2 := by
  rw [ringAcq_lin]; have : ringAcq 29 0 = 2 := by decide
  omega
theorem ringAcq_64 (r : Nat) : ringAcq 64 r = 2 * r + 1 := by
  rw [ringAcq_lin]; have : ringAcq 64 0 = 1 := by decide
  omega

theorem kv_poll {d : Mma.D} {r : Nat} (hs : Progress.isPoll d.site = true) {j : Fin 3}
    (ho : Progress.pollO r d.site = 32 + 8 * j.val) (hr : d.site.ord < 20 → r = 0) :
    KvPlace d.site.ord ∧ ringAcq d.site.ord r % 3 = j.val := by
  obtain ⟨site, v⟩ := d
  have hj := j.isLt
  cases site <;> simp only [Progress.isPoll, reduceCtorEq, Bool.false_eq_true] at hs
  case wt k =>
    fin_cases k
    all_goals simp only [Progress.pollO, Mma.Site.ord, Fin.isValue, Fin.reduceFinMk,
      Fin.val_mk, List.getD_cons_succ, List.getD_cons_zero] at ho ⊢
    all_goals simp only [Mma.Site.ord, Fin.isValue, Fin.reduceFinMk, Fin.val_mk,
      List.getD_cons_succ, List.getD_cons_zero] at hr
    all_goals simp only [KvPlace, ringAcq_2, ringAcq_20, ringAcq_29, ringAcq_64, true_or,
      or_true, true_and]
    all_goals (try have hr' := hr (by decide))
    all_goals omega
  case mw b ld =>
    simp only [Progress.pollO] at ho
    split at ho <;> omega

/-- **The ring index of a K/V poll is below the tile's ring uses** (`2 · max(Bs, 1)`), from the
count conjuncts' loop and tail conditions. -/
theorem idx_lt {d : Mma.D} {n : Mma.Cnt → Nat} {r : Nat} {w : Bool}
    (hQ : RefQ p L g d.site.ord d.v n r w) (hq : KvPlace d.site.ord) :
    (ringAcq d.site.ord r : Int) + 1 ≤ max (2 * Mma.Bs p L g d.v) 2 := by
  rcases hq with h | h | h | h
  · have hr := hQ.pre (by omega)
    rw [h, hr]; simp [ringAcq, pq]
  · have hl := (hQ.loop (by omega)).1
    rw [h]; simp only [ringAcq, pq]; norm_num; omega
  · have hl := (hQ.loop (by omega)).1
    rw [h]; simp only [ringAcq, pq]; norm_num; omega
  · have ht := hQ.tail (by omega)
    rw [h]; simp only [ringAcq, pq]; norm_num; omega

theorem sv_addm1 (b : BitVec 64) (h : 2 ≤ Loader.sv b) :
    Loader.sv (addi b (-1)) = Loader.sv b - 1 := by
  simp only [Loader.sv, toSigned, Flow.Arith32.addm1_toNat] at h ⊢
  have h1 := Nat.mod_lt b.toNat (show 0 < 2 ^ 32 by norm_num)
  generalize b.toNat % 2 ^ 32 = a at *
  simp only [Nat.reduceSub, Nat.reducePow] at h ⊢
  split_ifs at h ⊢ <;> omega

/-- **A tile's packets are at least twice its block count, and at least two.** -/
theorem pkts_ge (b : BitVec 64) : max (2 * Loader.sv b) 2 ≤ (Loader.pkts b : Int) := by
  by_cases h : 2 ≤ Loader.sv b
  · have hs := sv_addm1 b h
    have hw : Loader.w0 b = Loader.wRn b := by simp only [Loader.w0]; split_ifs <;> omega
    simp only [Loader.pkts, hw, Loader.wRn, hs]
    push_cast
    omega
  · simp only [Loader.pkts]
    push_cast
    omega

/-- The signed value of a 32-bit word does not read the high bits. -/
theorem toSigned_r32 (x : BitVec 64) : toSigned 32 (Flow.Arith32.r32 x) = toSigned 32 x := by
  simp only [toSigned, Flow.Arith32.r32, tr_toNat, Nat.mod_mod]

/-- A slot's count among more ring indices than one of its indices. -/
theorem ringCnt_gt {i A j : Nat} (hj : j < 3) (hi : i % 3 = j) (hA : i + 1 ≤ A) :
    ringCount i j + 1 ≤ Loader.ringCnt A j := by
  rw [Loader.ringCnt_eq A j hj]
  simp only [ringCount]
  split_ifs <;> omega

/-! ### The loader lanes' exit and time -/

set_option maxHeartbeats 4000000 in
/-- A loader exit event is fired at the exit site. -/
theorem ld_exit_site {w : Nat} {d : Loader.D} {pc : Nat}
    (hev : Loader.Ev p L g w d ⟨pc, .exit⟩) : d.site = .exit := by
  obtain ⟨s, v, k⟩ := d
  cases s <;> simp only [Loader.Ev] at hev
  all_goals first
    | rfl
    | (exfalso; obtain ⟨l, hl⟩ := epi_exit hev; simp [Loader.Site.toE] at hl; done)
    | skip
  all_goals (try split at hev)
  all_goals (try shape_destruct hev)
  all_goals (simp only [reduceCtorEq, Kind.tc.injEq, TcKind.commit.injEq] at *)

/-! ### A loader lane at its exit -/

/-- A K/V full barrier's no-increment arrive-ons are its asynchronous arrivals. -/
theorem kv_noinc (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) {o : Nat} (ho : KvOff o)
    {h k : Nat} {e : Event} (he : X.get (h, k) = some e) :
    MbarRing.arriveOnTo (obj L g o) e = Loader.cls L g (.asyncArrive (obj L g o)) e := by
  obtain ⟨pc, kind⟩ := e
  cases kind with
  | asyncArrive l ni =>
    by_cases hl : l = obj L g o
    · subst hl
      rcases kv_use hp hX hFw ho (g := g) he rfl (fun _ h => by cases h) with
        ⟨_, _, _, _, hk⟩ | ⟨-, hk⟩
      · cases hk
      · cases hk; simp [MbarRing.arriveOnTo, Loader.cls]
    · cases ni <;> simp [MbarRing.arriveOnTo, Loader.cls, hl]
  | _ => simp [MbarRing.arriveOnTo, Loader.cls]

set_option maxHeartbeats 8000000 in
/-- **A loader lane that has exited** has made `ringCnt A j` arrive-ons on full slot `j`, for the
tile's `A` packets: none without a picked tile, `pkts` of the picked tile's block word with
one. -/
theorem ld_end (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) {y : Nat}
    (hy : y < L.threads) (hw : Prologue.warpIndex L y = 14 ∨ Prologue.warpIndex L y = 15)
    {pc : Nat} (hl : (X.tr y).getLast? = some ⟨pc, .exit⟩) (j : Fin 3) :
    ∃ A, (X.tr y).countP (MbarRing.arriveOnTo (obj L y (32 + 8 * j.val))) = Loader.ringCnt A j ∧
      okPolls (obj L y (56 + 8 * j.val)) (X.tr y) = Loader.ringCnt (A + 3) j ∧
      ((A = 0 ∧ ¬ ∃ R bal, Epilogue.Picked p L y R bal) ∨
        ∃ R bal, Epilogue.Picked p L y R bal ∧ A = Loader.pkts (Loader.r28Ref p L y R bal)) := by
  have hT := table_shape_of hp hFw
  have hF := table_followed hp hX hFw
  have he := Sched.exit_get hl
  have hne : X.tr y ≠ [] := fun h => by rw [h] at hl; cases hl
  have hlen : 0 < (X.tr y).length := List.length_pos_iff.mpr hne
  obtain ⟨⟨σ1, n⟩, hσ, -, -, hev⟩ := Frame.RoleTable.ev_of_ne_ubU (T := table p L)
    (S := fun g => g < L.threads) (fun g hg => thread_sound hp hg) hX hT hF hy he
    (fun f h => by cases h)
  have hR := (LdWarp.good hp hX hw hy rfl _).2 _ hσ
  have hoF : KvOff (32 + 8 * j.val) := by fin_cases j <;> simp [KvOff]
  -- the arrive-ons up to the exit are the ledger's asynchronous arrivals
  have hcnt : (X.tr y).countP (MbarRing.arriveOnTo (obj L y (32 + 8 * j.val))) =
      n (.load (.asyncArrive (obj L y (32 + 8 * j.val)))) := by
    rw [← count hσ]
    conv_lhs => rw [← List.take_length (l := X.tr y),
      show (X.tr y).length = (X.tr y).length - 1 + 1 by omega, List.take_add_one]
    have he' : (X.tr y)[(X.tr y).length - 1]? = some ⟨pc, .exit⟩ := he
    rw [he']
    simp only [Option.toList_some, List.countP_append, List.countP_singleton]
    simp only [MbarRing.arriveOnTo, ite_false, Bool.false_eq_true, Nat.add_zero]
    refine List.countP_congr fun e hmem => ?_
    obtain ⟨i, hi, hie⟩ := List.getElem_of_mem hmem
    have hi' : i < (X.tr y).length - 1 := by
      have := hi; simp only [List.length_take] at this; omega
    have hget : X.get (y, i) = some e := by
      show (X.tr y)[i]? = _
      rw [← List.getElem?_take_of_lt hi', List.getElem?_eq_getElem hi, hie]
    have := kv_noinc hp hX hFw hoF (g := y) hget
    rw [this]
    rfl
  have hpl : okPolls (obj L y (56 + 8 * j.val)) (X.tr y) =
      n (.load (.acquire (obj L y (56 + 8 * j.val)))) := by
    rw [← count hσ]
    unfold okPolls
    conv_lhs => rw [← List.take_length (l := X.tr y),
      show (X.tr y).length = (X.tr y).length - 1 + 1 by omega, List.take_add_one]
    have he' : (X.tr y)[(X.tr y).length - 1]? = some ⟨pc, .exit⟩ := he
    rw [he']
    simp only [Option.toList_some, List.countP_append, List.countP_singleton]
    simp only [okPoll, sourceWaitSuccess, ite_false, Bool.false_eq_true, Nat.add_zero]
    rfl
  rcases σ1 with s | ⟨i, d⟩
  · exfalso
    have h1 := hR.1
    obtain ⟨site, x1, x2, x3⟩ := s
    have hEv : Startup.Ev L y ⟨site, x1, x2, x3⟩ ⟨pc, .exit⟩ := hev
    cases site with
    | sh jj =>
      fin_cases jj <;> simp only [Startup.Ev] at hEv <;> obtain ⟨_, _, hk⟩ := hEv <;> cases hk
    | fence => simp only [Startup.Ev] at hEv; cases hEv
    | bar => simp only [Startup.Ev] at hEv; cases hEv
    | _ => simp only [StartAt] at h1
  cases i with
  | loader b =>
    obtain ⟨hbw, hR'⟩ := hR
    have hub0 : n .ub = 0 := ub_zero hX he hσ
    obtain ⟨hJl, hFit⟩ := hR' hub0
    obtain ⟨kk, A, -, hCnt⟩ := hJl.refE
    have hEv : Loader.Ev p L y (Loader.wOf b) d ⟨pc, .exit⟩ := hev
    have hsite := ld_exit_site hEv
    have ha := Loader.arr_ring hp hX hy hw hσ hub0 j
    have hq := Loader.acq_ring hp hX hy hw hσ hub0 j
    have hc := hCnt.commit
    simp only [LdWarp.lcn, hsite, Loader.arrAt, Loader.inPkt, Nat.add_zero] at hc
    simp only [LdWarp.lcn, hsite, Loader.inPkt, Nat.sub_zero, hc] at ha
    simp only [LdWarp.lcn, hsite, Loader.acqOff, hc] at hq
    refine ⟨A, hcnt.trans ha, hpl.trans hq, ?_⟩
    simp only [Loader.LFits, hsite, Loader.lc] at hFit
    obtain ⟨l, -, hFE, h1, h2⟩ := hFit
    rw [show n (.load .commit) = A from hc] at h1 h2
    cases l
    · exact .inl ⟨h2 rfl, noPicked_exit hFE rfl⟩
    · obtain ⟨⟨R, bal, hP, hr⟩, hA⟩ := h1 rfl
      exact .inr ⟨R, bal, hP, by rw [hA, hr]⟩
  | _ => exact hR.elim

/-! ### The loader half at the K/V polls -/

/-- A pipeline state of warp 12 follows a role state: the startup enters the MMA warp's role at
its prefix. -/
theorem mma_prev {h k : Nat} {e : Event} {d : Mma.D} {n : Cls → Nat}
    (he : (X.tr h)[k]? = some e)
    (hσ : Frame.stateAt (thread p L) X h (k + 1) = some (some (Mma.minj p L h d n))) :
    ∃ r n0, Frame.stateAt (thread p L) X h k = some (some (.inr r, n0)) := by
  refine prev_role (i := .mma) he hσ (fun hd => ?_)
  simp [frag, Mma.M, Mma.G, Code.glue, Code.enter, Mma.Start.exit] at hd

set_option maxHeartbeats 8000000 in
/-- **The loader half of the MMA warp's poll premise at the K/V polls**: a lane of warp 12 at a
K/V poll at the end of its trace finds the full barrier in a state, and when its phase has the
poll's parity the lane has a blocker: an open arrive-on, or a pending loader lane short of the
packet (whose time is below the poll's). A loader lane that has exited has made every arrive-on of
the tile, which by the tile agreement is more than the poll's ring index, so with every arrive-on
recorded it is not short (`NoIncObject.blocked`); the phase is at most the lane's polls plus one
(`kv_bound_lane`). -/
theorem kv_lag (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X)
    (hfree : ∀ l, ∀ r ∈ X.objects l, r.fault = none) (hub : ¬ HasUb X)
    (hg : g < L.threads) (hg12 : Prologue.warpIndex L g = 12) {d : Mma.D} {n : Cls → Nat}
    (hσ : Frame.stateAt (thread p L) X g (X.tr g).length = some (some (Mma.minj p L g d n)))
    (hs : Progress.isPoll d.site = true) {r : Nat} {w : Bool}
    (hQ : RefQ p L g d.site.ord d.v (Mma.rc n) r w) {j : Fin 3}
    (ho : Progress.pollO r d.site = 32 + 8 * j.val) :
    ∃ before, MBarrier.stateBefore (X.objects (Mma.bl L g (Progress.pollO r d.site)))
        (X.objects (Mma.bl L g (Progress.pollO r d.site))).length = some before ∧
      (before.phase % 2 = n (.mma (.acquire (Mma.bl L g (Progress.pollO r d.site)))) % 2 →
        Sched.Blk (Progress.timed p L) X g) := by
  have hT := table_shape_of hp hFw
  have hFl := table_followed hp hX hFw
  have hb := hp.block
  rw [ho]
  change ∃ before, MBarrier.stateBefore (X.objects (obj L g (32 + 8 * j.val)))
      (X.objects (obj L g (32 + 8 * j.val))).length = some before ∧
    (before.phase % 2 = n (.mma (.acquire (obj L g (32 + 8 * j.val)))) % 2 → _)
  obtain ⟨hq, hmod⟩ := kv_poll hs ho hQ.pre
  have hoF : KvOff (32 + 8 * j.val) := by fin_cases j <;> simp [KvOff]
  have O := kvObj hp hX hFw hoF g
  -- the history holds the startup's initialization
  have hlen : 0 < (X.tr g).length := by
    by_contra h0
    rw [show (X.tr g).length = 0 by omega, Frame.stateAt_zero] at hσ
    simp [thread, glued, Code.glue, Code.counted, Code.enter, Startup.code, exit] at hσ
  have hne : X.objects (obj L g (32 + 8 * j.val)) ≠ [] := by
    obtain ⟨e, he⟩ : ∃ e, (X.tr g)[(X.tr g).length - 1]? = some e :=
      ⟨_, List.getElem?_eq_getElem (by omega)⟩
    have hσ' : Frame.stateAt (thread p L) X g ((X.tr g).length - 1 + 1) =
        some (some (Mma.minj p L g d n)) := by
      rw [show (X.tr g).length - 1 + 1 = (X.tr g).length by omega]; exact hσ
    obtain ⟨⟨i, dr⟩, n0, hσ0⟩ := mma_prev he hσ'
    have hb0 := role_bar0 hp hX _ hσ0
    obtain ⟨j0, c, hinit, -⟩ := init_exists hp hX hT hFl hg (by omega) hb0 (o := 32 + 8 * j.val)
      (by rcases hoF with h | h | h <;> rw [h] <;> decide)
    obtain ⟨i, r0, hi, -⟩ := init_record_of_consistent hX hinit
    intro h0
    rw [h0] at hi
    simp at hi
  obtain ⟨before, hst⟩ := MbarRing.Unit.final_of_init hX O.init O.noInval hne
  refine ⟨before, hst, fun hph => ?_⟩
  -- the lane's polls of the slot
  have hacq := hQ.acq (32 + 8 * j.val)
  simp only [Mma.rc, acqAt_ring] at hacq
  have hok : okPolls (obj L g (32 + 8 * j.val)) (X.tr g) =
      ringCount (ringAcq d.site.ord r) j.val := by
    rw [← hacq, ← count hσ, List.take_length]; rfl
  have hup := kv_bound_lane hp hX hFw hg hg12 hσ hQ hq j hst
  -- the loader lanes of the CTA
  have hld : ∀ a, ldProd L g a < L.threads ∧ (Prologue.warpIndex L (ldProd L g a) = 14 ∨
      Prologue.warpIndex L (ldProd L g a) = 15) ∧ ldProd L g a / L.block = g / L.block := by
    intro a
    have : g / L.block < L.grid := (Nat.div_lt_iff_lt_mul (by omega)).mpr hg
    have h2 := Nat.mul_le_mul_right 512 (show g / L.block + 1 ≤ L.grid by omega)
    have h3 := a.isLt
    have : (g / 512 * 512 + 448 + a.val) % 512 = 448 + a.val := by omega
    rw [Nat.add_mul] at h2
    simp only [ldProd, Launch.threads, Prologue.warpIndex, hb] at *
    omega
  -- the tile: the MMA lane is at a pipeline state of the picked tile
  have hpipe : d.site.pipe = true := by
    obtain ⟨site, v⟩ := d
    cases site <;> simp_all [Progress.isPoll, Mma.Site.pipe]
  obtain ⟨-, hFm⟩ := Progress.mma_ref hp hX hub hg hg12 hσ
  obtain ⟨R, bal, hC, hBs⟩ := Mma.bs_ref (Mma.pmid_of hpipe) hFm
  have hidx := idx_lt hQ hq
  -- the schedule of the K/V hand-off
  have hi3 : ringAcq d.site.ord r = 3 * ringCount (ringAcq d.site.ord r) j.val + j.val := by
    have := j.isLt
    simp only [ringCount]
    omega
  have H : Sched.LagShort (Progress.timed p L) X (obj L g (32 + 8 * j.val)) 0
      (fun y => ∃ a, y = ldProd L g a) (· = g) (fun v => Progress.Ld.bound p (3 * v + j.val))
      (ringCount (ringAcq d.site.ord r) j.val + 1)
      (MbarRing.arriveOnTo (obj L g (32 + 8 * j.val))) := {
    mono := fun a b hab => Progress.Ld.bound_mono p (by omega)
    wait := fun g' d' hg' hσ' => by
      subst hg'
      rw [← Sched.threadTime_of hσ', Sched.threadTime_of hσ, hok, ← hi3]
      simp only [Progress.timed, Progress.time, Progress.roleTime, Progress.Mm.time, hpipe,
        ite_true]
      refine (Progress.Ld.bound_le p _).trans (Progress.Mm.kv_time p hq hQ.ps hQ.pre)
    early := fun y g' hy hg' hyt hc => by
      subst hg'
      obtain ⟨a, rfl⟩ := hy
      obtain ⟨-, hyw, hyc⟩ := hld a
      have hPy := Epilogue.Picked.cta hyc.symm hC.1
      have hsv : Loader.sv (Loader.r28Ref p L (ldProd L g' a) R bal) = Mma.Bs p L g' d.v := by
        rw [hBs, tile_agree (p := p) hyc R bal]
        simp only [Loader.sv, Mma.Bs, toSigned_r32]
      have hpk := pkts_ge (Loader.r28Ref p L (ldProd L g' a) R bal)
      rw [hsv] at hpk
      rw [hok] at hc
      have hcnt : (X.tr (ldProd L g' a)).countP (Loader.cls L (ldProd L g' a)
          (.asyncArrive (obj L (ldProd L g' a) (32 + 8 * j.val)))) =
          (X.tr (ldProd L g' a)).countP (MbarRing.arriveOnTo (obj L g' (32 + 8 * j.val))) := by
        refine List.countP_congr fun e he => ?_
        obtain ⟨i, hi, hie⟩ := List.getElem_of_mem he
        rw [kv_noinc hp hX hFw hoF (g := g') (h := ldProd L g' a) (k := i) (e := e)
            (by rw [← hie]; exact List.getElem?_eq_getElem hi),
          show obj L (ldProd L g' a) (32 + 8 * j.val) = obj L g' (32 + 8 * j.val) by
            simp only [obj, hyc]]
        rfl
      have hj := j.isLt
      refine Loader.ld_early hp hX hub hyt hyw hPy ?_ ?_
      · omega
      · rw [show (3 * ((X.tr (ldProd L g' a)).countP
            (MbarRing.arriveOnTo (obj L g' (32 + 8 * j.val))) + 0) + j.val) % 3 = j.val by omega]
        exact hcnt.le.trans (by omega)
    exit := fun y k pc hy hx => by
      obtain ⟨a, rfl⟩ := hy
      obtain ⟨hyt, hyw, hyc⟩ := hld a
      have hl : (X.tr (ldProd L g a)).getLast? = some ⟨pc, .exit⟩ := by
        rw [List.getLast?_eq_getElem?, ← Execution.exit_last hX hyt hx, Nat.add_sub_cancel]
        exact hx
      obtain ⟨A, hA, -, hcase⟩ := ld_end hp hX hFw hyt hyw hl j
      rw [show obj L (ldProd L g a) (32 + 8 * j.val) = obj L g (32 + 8 * j.val) by
        simp only [obj, hyc]] at hA
      rcases hcase with ⟨rfl, hno⟩ | ⟨R', bal', hP', hAeq⟩
      · exact (hno ⟨R, bal, Epilogue.Picked.cta hyc.symm hC.1⟩).elim
      obtain ⟨rfl, rfl⟩ := (Epilogue.Picked.cta hyc hP').unique hC.1
      have hsv : Loader.sv (Loader.r28Ref p L (ldProd L g a) R' bal') = Mma.Bs p L g d.v := by
        rw [hBs, tile_agree (p := p) hyc R' bal']
        simp only [Loader.sv, Mma.Bs, toSigned_r32]
      have hpk := pkts_ge (Loader.r28Ref p L (ldProd L g a) R' bal')
      rw [hsv, ← hAeq] at hpk
      have hgt := ringCnt_gt j.isLt hmod (A := A) (by omega)
      omega
    bound := fun g' hg' => by subst hg'; omega }
  exact H.blk_noInc hX hub O (ldProd_inj L g)
    (fun a => ⟨⟨a, rfl⟩, (hld a).1, by rw [(hld a).2.2]⟩) (hfree _) hg rfl
    (fun h => by rw [h] at hlen; simp at hlen) hσ hst (by omega)
    (by rw [hok, ← hacq, Nat.add_zero]; exact hph)

end
end PTX.Kernels.TmlFa4Fwd.Proof
