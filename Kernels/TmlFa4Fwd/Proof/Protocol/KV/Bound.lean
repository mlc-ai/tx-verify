-- SPDX-License-Identifier: Apache-2.0
module

import Lemmas.Kernel.FrameU

public import Kernels.TmlFa4Fwd.Proof.Loader.Move
public import Kernels.TmlFa4Fwd.Proof.SmWarp.Export.Follow
public import Kernels.TmlFa4Fwd.Proof.Protocol.KV.EmptyObj
public import Kernels.TmlFa4Fwd.Proof.Protocol.KV.Obj
public import Lemmas.Protocol.NoIncRing
public import Lemmas.Protocol.PollIndex
public import Lemmas.Protocol.UnitReachBlocker
import Kernels.TmlFa4Fwd.Proof.Common.NoUb
import Kernels.TmlFa4Fwd.Proof.Common.Sound
import Kernels.TmlFa4Fwd.Proof.LdWarp.Src
import Kernels.TmlFa4Fwd.Proof.Loader.Export.AcqRing
import Kernels.TmlFa4Fwd.Proof.Loader.Export.ArrRing
import Kernels.TmlFa4Fwd.Proof.Mma.Warp
import Kernels.TmlFa4Fwd.Proof.Protocol.KV.EmptyPoll
import Kernels.TmlFa4Fwd.Proof.Loader.Export.NoUb
import Kernels.TmlFa4Fwd.Proof.Protocol.Mbar.InitOne
import Kernels.TmlFa4Fwd.Proof.Protocol.Mbar.SiteUse
import Kernels.TmlFa4Fwd.Proof.Protocol.Tmem.MmaNoUb
import Kernels.TmlFa4Fwd.Proof.Mma.Export.Ring
import Kernels.TmlFa4Fwd.Proof.Protocol.Credit.Handoff
import Kernels.TmlFa4Fwd.Proof.Protocol.Ready.Obj
import Lemmas.Kernel.ElectSource
import Lemmas.Kernel.Safety.StateInv
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The K/V ring's loader side

The inputs of `MbarRing.full_phase_le_commits` on the loader side of the K/V ring: every
no-increment arrive-on on a full barrier is by one of the CTA's 64 loader lanes (`kv_src`, through
`ldProd`), and each loader lane's arrive-ons on full slot `j` are at most its successful polls of
empty slot `j` (`ld_arr_le_polls`: at the lane's last followed state, `Frame.end_countP`, the
reference invariant's closed forms `ringCnt (arrAt …) j ≤ ringCnt (acqAt …) j`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow
open PTX.Frame (MbarOf)

noncomputable section
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- The 64 loader lanes of lane `g`'s CTA (warps 14 and 15). -/
def ldProd (L : Launch) (g : Nat) (a : Fin 64) : Nat := g / L.block * L.block + 448 + a.val

theorem ldProd_inj (L : Launch) (g : Nat) : Function.Injective (ldProd L g) := by
  intro a b h
  simp only [ldProd] at h
  exact Fin.ext (by omega)

/-- A loader lane of the CTA is one of `ldProd`. -/
theorem ldLane_prod {h : Nat} (hl : LdLane L g h) : ∃ a, h = ldProd L g a := by
  obtain ⟨hc, hw⟩ := hl
  simp only [Prologue.warpIndex] at hw
  have hd := Nat.div_add_mod h L.block
  refine ⟨⟨h % L.block - 448, by omega⟩, ?_⟩
  simp only [ldProd, ← hc]
  rw [Nat.mul_comm] at hd
  omega

/-- **Every no-increment arrive-on on a K/V full barrier is by a loader lane of the CTA.** -/
theorem kv_src (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) {o : Nat} (ho : KvOff o)
    (i : EvId) (hi : X.AsyncArrive i (obj L g o) true) : ∃ a, i.1 = ldProd L g a := by
  obtain ⟨pc, he⟩ := hi
  rcases kv_use hp hX hFw ho (h := i.1) (k := i.2) he rfl (fun _ h => by cases h) with
    ⟨_, _, _, _, hk⟩ | ⟨hl, -⟩
  · cases hk
  · exact ldLane_prod hl

theorem Loader.ringCnt_mono {a b : Nat} (h : a ≤ b) (s : Nat) :
    Loader.ringCnt a s ≤ Loader.ringCnt b s := by
  simp only [Loader.ringCnt]
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [List.range_add, List.filter_append, List.length_append]
  omega

set_option maxHeartbeats 4000000 in
/-- **A loader lane's arrive-ons on full slot `j` are at most its successful polls of empty slot
`j`.** -/
theorem ld_arr_le_polls (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    {y : Nat} (hy : y < L.threads)
    (hw14 : Prologue.warpIndex L y = 14 ∨ Prologue.warpIndex L y = 15) (j : Fin 3) :
    (X.tr y).countP (MbarRing.arriveOnTo (obj L y (32 + 8 * j.val))) ≤
      okPolls (obj L y (56 + 8 * j.val)) (X.tr y) := by
  set w := Prologue.warpIndex L y with hw
  have hG := fun k => LdWarp.good hp hX hw14 hy hw.symm k
  have hlive : ∀ k d e, X.get (y, k) = some e →
      Frame.stateAt (thread p L) X y k = some (some d) → (thread p L y).next d e = none →
      e.kind = .exit := by
    intro k σ e he hσ hn
    have hR := (hG k).2 σ hσ
    have hub : ∀ f, e.kind ≠ .ub f := Loader.ld_noUb hp hX hy hw14 he
    obtain ⟨σ, n⟩ := σ
    rcases σ with s | ⟨i, d⟩
    · exact start_live hp hX he hσ hR.1 hn
    cases i with
    | loader b =>
      have hn' := role_next_none hn
      obtain ⟨hbw, hR'⟩ := hR
      obtain ⟨hJ, hF⟩ := hR' (ub_zero hX he hσ)
      have hs : Loader.succ p L y w d e = none := by
        rw [← hbw]; simpa [frag, Loader.F, Loader.code] using hn'
      exact Loader.role_live hp hX hw14 hy hw.symm he hσ hbw hJ hF hub hs
    | _ => exact hR.elim
  obtain ⟨k, ⟨σ, n⟩, hσ, -, hcnt⟩ := Frame.end_countP hX hy (fun k => (hG k).1) hlive
  have hA := hcnt (MbarRing.arriveOnTo (obj L y (32 + 8 * j.val))) (fun _ => rfl)
  have hP := hcnt (okPoll (obj L y (56 + 8 * j.val))) (fun _ => rfl)
  unfold okPolls
  rw [hA, hP]
  have h1 : ((X.tr y).take k).countP (MbarRing.arriveOnTo (obj L y (32 + 8 * j.val))) ≤
      ((X.tr y).take k).countP (cls L y (.load (.asyncArrive (obj L y (32 + 8 * j.val))))) := by
    refine List.countP_mono_left fun e _ h => ?_
    obtain ⟨pc, kind⟩ := e
    cases kind with
    | asyncArrive l ni => cases ni <;> simp_all [MbarRing.arriveOnTo, cls, Loader.cls]
    | _ => simp [MbarRing.arriveOnTo] at h
  have h2 : ((X.tr y).take k).countP (okPoll (obj L y (56 + 8 * j.val))) =
      ((X.tr y).take k).countP (cls L y (.load (.acquire (obj L y (56 + 8 * j.val))))) := rfl
  rw [h2, count hσ]
  rw [count hσ] at h1
  refine h1.trans ?_
  have hR := (hG k).2 _ hσ
  rcases σ with s | ⟨i, d⟩
  · rw [hR.2.2 _]; exact Nat.zero_le _
  cases i with
  | loader b =>
    have hub0 : n .ub = 0 := by
      by_contra hne
      obtain ⟨j', -, ⟨pc, kind⟩, hf, hc⟩ := exists_of_count hσ (Nat.pos_of_ne_zero hne)
      cases kind <;> simp [cls] at hc
      exact Loader.ld_noUb hp hX hy hw14 hf _ rfl
    have ha := Loader.arr_ring hp hX hy hw14 hσ hub0 j
    have hq := Loader.acq_ring hp hX hy hw14 hσ hub0 j
    simp only [LdWarp.lcn] at ha hq
    rw [show n (.load (.asyncArrive (obj L y (32 + 8 * j.val)))) = _ from ha,
      show n (.load (.acquire (obj L y (56 + 8 * j.val)))) = _ from hq]
    exact Loader.ringCnt_mono (by omega) _
  | _ => exact hR.elim

/-! ### The MMA side: the commits to an empty barrier are one lane's -/

/-- A commit's target is the CTA's own: rank 0. -/
theorem commit_rank (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) {h k pc : Nat}
    {s : TcCommit.Spec} {rank : Fin 16} {l : Loc}
    (he : X.get (h, k) = some ⟨pc, .tc (.commit s)⟩) (ht : TcCommit.target s rank = some l) :
    rank = 0 := by
  have hsafe : TcCommitIssueSafe L (h, k) s := by
    by_contra hn
    exact noTcCommitUnsafe hp hX ⟨(h, k), s, ⟨pc, he⟩, hn⟩
  obtain ⟨-, hres, -⟩ := hsafe
  have hOne := hp.cluster.2.2
  have h1 := hp.cluster.1
  unfold TcCommit.resolve at hres
  split_ifs at hres
  simp only [Option.some.injEq] at hres
  rw [← hres] at ht
  unfold TcCommit.target at ht
  split_ifs at ht with hr
  simp only [Launch.oneDim_clusterSizeOf hOne, h1] at hr
  exact Fin.ext (by simp only [Fin.val_zero]; omega)

set_option maxHeartbeats 4000000 in
/-- **Two commits to an empty barrier are by one lane**, of the CTA's MMA warp, to the barrier
itself: the committing lanes won the warp's elections (`empty_use`), whose winner is one lane
(`elect_winner`). -/
theorem empty_one (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) {o : Nat}
    (ho : EmptyOff o) {i i' : EvId} {pc pc' : Nat} {s s' : TcCommit.Spec} {rank rank' : Fin 16}
    (he : X.get i = some ⟨pc, .tc (.commit s)⟩) (ht : TcCommit.target s rank = some (obj L g o))
    (he' : X.get i' = some ⟨pc', .tc (.commit s')⟩)
    (ht' : TcCommit.target s' rank' = some (obj L g o)) :
    i.1 = i'.1 ∧ s.mbar = obj L g o ∧ Prologue.warpIndex L i.1 = 12 ∧
      i.1 / L.block = g / L.block := by
  rcases empty_use hp hX hFw ho (h := i.1) (k := i.2) he ⟨rank, ht⟩
      (fun _ h => by cases h) with ⟨_, _, _, _, hk⟩ | ⟨s1, hk, h12, hmb, j, q, inst, hel⟩
  · cases hk
  rcases empty_use hp hX hFw ho (h := i'.1) (k := i'.2) he' ⟨rank', ht'⟩
      (fun _ h => by cases h) with ⟨_, _, _, _, hk'⟩ | ⟨s2, hk', h12', -, j', q', inst', hel'⟩
  · cases hk'
  cases hk
  have hc := commit_target hp hX (g := i.1) (k := i.2) he ht
  have hc' := commit_target hp hX (g := i'.1) (k := i'.2) he' ht'
  simp only [obj, Loc.mk.injEq, true_and] at hc hc'
  have hw : SameWarp L i.1 i'.1 := by
    refine ⟨⟨Frame.lt_of_get hX (k := i.2) he, Frame.lt_of_get hX (k := i'.2) he', by omega⟩, ?_⟩
    simp only [Prologue.warpIndex] at h12 h12'
    omega
  have hl := elect_winner hX (e := (i.1, j)) (f := (i'.1, j')) hel hel' hw
  simp only [laneOf] at hl
  refine ⟨?_, hmb, h12, by omega⟩
  have h1 := Nat.div_add_mod i.1 L.block
  have h2 := Nat.div_add_mod i'.1 L.block
  have h3 := Nat.div_add_mod (i.1 % L.block) 32
  have h4 := Nat.div_add_mod (i'.1 % L.block) 32
  obtain ⟨⟨-, -, hcta⟩, hww⟩ := hw
  rw [hcta] at h1
  rw [hww] at h3
  omega

set_option maxHeartbeats 4000000 in
/-- **An empty barrier's phase is at most the commits to it of one MMA lane of the CTA.** -/
theorem empty_phase (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) {o : Nat}
    (ho : EmptyOff o) {stE : MBarrier.State}
    (hst : MBarrier.stateBefore (X.objects (obj L g o)) (X.objects (obj L g o)).length =
      some stE) :
    ∃ c, Prologue.warpIndex L c = 12 ∧ c / L.block = g / L.block ∧
      stE.phase ≤ (X.tr c).countP (commitsTo (obj L g o)) := by
  have hU := fun {h k} {e : Event} (he : X.get (h, k) = some e) (hm : MbarOf e (obj L g o))
      (hni : ∀ c, e.kind ≠ .mbInit (obj L g o) c) =>
    empty_use hp hX hFw ho he hm hni
  have hni := AsyncCopy.objects_noInval hX.tma.2.2.1 (no_inval hp hX hFw) (obj L g o)
  have harr : ∀ {h i pc tx cnt : Nat} {rel : Bool} {sc : MbarScope},
      X.get (h, i) ≠ some ⟨pc, .arrive (obj L g o) tx cnt rel sc⟩ := by
    intro h i pc tx cnt rel sc he
    rcases hU he rfl (fun _ h => by cases h) with ⟨_, _, _, _, hk⟩ | ⟨_, hk, -⟩ <;> cases hk
  have hcpa : ∀ {i : EvId} {pc : Nat} {m' : Loc} {noinc : Bool},
      X.get i = some ⟨pc, .asyncArrive m' noinc⟩ → m' ≠ obj L g o := by
    intro i pc m' noinc he hm
    subst hm
    rcases hU (h := i.1) (k := i.2) he rfl (fun _ h => by cases h) with
      ⟨_, _, _, _, hk⟩ | ⟨_, hk, -⟩ <;> cases hk
  by_cases hex : ∃ (i : EvId) (pc : Nat) (s : TcCommit.Spec) (rank : Fin 16),
      X.get i = some ⟨pc, .tc (.commit s)⟩ ∧ TcCommit.target s rank = some (obj L g o)
  · obtain ⟨i0, pc0, s0, rank0, he0, ht0⟩ := hex
    obtain ⟨-, -, h12, hcta⟩ := empty_one hp hX hFw ho he0 ht0 he0 ht0
    refine ⟨i0.1, h12, hcta, MbarRing.commitObj_phase_le_commits hX
      (emptyObj hp hX hFw ho g) hni harr hcpa i0.1 ?_ hst⟩
    intro i pc sp rank he ht
    obtain ⟨hi, hmb, -, -⟩ := empty_one hp hX hFw ho he ht he0 ht0
    refine ⟨hi, hmb, fun rank' ht' => ?_⟩
    rw [commit_rank hp hX (h := i.1) (k := i.2) he ht',
      commit_rank hp hX (h := i.1) (k := i.2) he ht]
  · have hb := hp.block
    refine ⟨g / L.block * L.block + 384, ?_, ?_, MbarRing.commitObj_phase_le_commits hX
      (emptyObj hp hX hFw ho g) hni harr hcpa _
      (fun he ht => (hex ⟨_, _, _, _, he, ht⟩).elim) hst⟩
    · simp only [Prologue.warpIndex, hb]
      omega
    · rw [hb]
      omega

/-! ### The K/V bound -/

set_option maxHeartbeats 4000000 in
/-- **A K/V full barrier's phase is at most one MMA lane's commits to its empty barrier plus
one.** -/
theorem kv_phase (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) (hg : g < L.threads)
    (j : Fin 3) {stF : MBarrier.State}
    (hst : MBarrier.stateBefore (X.objects (obj L g (32 + 8 * j.val)))
      (X.objects (obj L g (32 + 8 * j.val))).length = some stF) :
    ∃ c, Prologue.warpIndex L c = 12 ∧ c / L.block = g / L.block ∧
      stF.phase ≤ (X.tr c).countP (commitsTo (obj L g (56 + 8 * j.val))) + 1 := by
  have hb := hp.block
  have hoF : KvOff (32 + 8 * j.val) := by fin_cases j <;> simp [KvOff]
  have hoE : EmptyOff (56 + 8 * j.val) := by fin_cases j <;> simp [EmptyOff]
  have hyc : ∀ a, ldProd L g a / L.block = g / L.block := by
    intro a; simp only [ldProd, hb]; omega
  have hobj : ∀ a o, obj L (ldProd L g a) o = obj L g o := by
    intro a o; simp only [obj, hyc]
  have hyt : ∀ a, ldProd L g a < L.threads := by
    intro a
    have : g / L.block < L.grid := (Nat.div_lt_iff_lt_mul (by omega)).mpr hg
    simp only [ldProd, Launch.threads]
    rw [hb] at this ⊢
    have h2 := Nat.mul_le_mul_right 512 (show g / 512 + 1 ≤ L.grid by omega)
    have h3 := a.isLt
    rw [Nat.add_mul] at h2
    omega
  have hyw : ∀ a, Prologue.warpIndex L (ldProd L g a) = 14 ∨
      Prologue.warpIndex L (ldProd L g a) = 15 := by
    intro a
    simp only [Prologue.warpIndex, ldProd, hb]
    have : (g / 512 * 512 + 448 + a.val) % 512 = 448 + a.val := by omega
    rw [this]
    omega
  have hlane : ∀ a, (X.tr (ldProd L g a)).countP (MbarRing.arriveOnTo (obj L g (32 + 8 * j.val))) ≤
      okPolls (obj L g (56 + 8 * j.val)) (X.tr (ldProd L g a)) + 0 := by
    intro a
    have := ld_arr_le_polls hp hX (hyt a) (hyw a) j
    rwa [hobj, hobj] at this
  obtain ⟨q, hq, hc⟩ := empty_init hoE
  have hinit : PairTmaRing.InitFirst X (obj L g (56 + 8 * j.val)) 1 := by
    have := obj_initFirst hp hX hFw g q
    rwa [hq, hc] at this
  have hni := AsyncCopy.objects_noInval hX.tma.2.2.1 (no_inval hp hX hFw)
    (obj L g (56 + 8 * j.val))
  by_cases hne : X.objects (obj L g (56 + 8 * j.val)) = []
  · -- no record on the empty barrier: no successful poll of it, so no arrive-on
    have h0 : ∀ a, okPolls (obj L g (56 + 8 * j.val)) (X.tr (ldProd L g a)) = 0 := by
      intro a
      by_contra hpos
      obtain ⟨i, w, -, hi, -⟩ := MbarRing.Poll.record hX (PairTmaRing.poll_clean hX hinit hni)
        (Nat.pos_of_ne_zero hpos)
      rw [hne] at hi
      cases hi
    refine ⟨g / L.block * L.block + 384, ?_, ?_, ?_⟩
    · simp only [Prologue.warpIndex, hb]
      omega
    · rw [hb]; omega
    · have := MbarRing.full_phase_le_commits (stE := { stF with phase := 0 })
        (c := g / L.block * L.block + 384) hX (kvObj hp hX hFw hoF g) (by decide)
        (ldProd L g) (ldProd_inj L g) (kv_src hp hX hFw hoF) hlane
        (fun a => by rw [h0 a]; exact Nat.zero_le _) (Nat.zero_le _) hst
      omega
  obtain ⟨stE, hstE⟩ := MbarRing.Unit.final_of_init hX hinit hni hne
  obtain ⟨c, h12, hcta, hE⟩ := empty_phase hp hX hFw hoE hstE
  refine ⟨c, h12, hcta, ?_⟩
  have := MbarRing.full_phase_le_commits hX (kvObj hp hX hFw hoF g) (by decide)
    (ldProd L g) (ldProd_inj L g) (kv_src hp hX hFw hoF) hlane
    (fun a => by
      have := ld_empty_okPolls hp hX hFw hoE (hyw a) (hyt a) (before := stE)
        (by rw [hobj]; exact hstE)
      rwa [hobj] at this) hE hst
  omega

set_option maxHeartbeats 4000000 in
/-- **A lane of warp 12 that stops stops at its start**: no event of its fragment ends it unless
it is the fragment's exit. -/
theorem warp12_live (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) {c : Nat} (hc : c < L.threads) (hc12 : Prologue.warpIndex L c = 12) :
    ∀ k d e, X.get (c, k) = some e → Frame.stateAt (thread p L) X c k = some (some d) →
      (thread p L c).next d e = none → e.kind = .exit := by
  have hReads := cuQReadsFromLaunch hp hX
  have hG := fun k => Mma.good hp hX hReads hc hc12 k
  intro k σ e he hσ hn
  have hR := (hG k).2 σ hσ
  have hub : ∀ f, e.kind ≠ .ub f := Mma.mma_noUb hp hX hFw hc hc12 he
  obtain ⟨σ, n⟩ := σ
  rcases σ with s | ⟨i, d⟩
  · exact start_live hp hX he hσ hR.1 hn
  cases i with
  | mma =>
    have hn' := role_next_none hn
    rcases d with s0 | ⟨⟨⟩, d⟩
    · obtain ⟨t, ins, o, hat, hinv, hcd, hf⟩ :=
        Frame.fired_siteU (fun g hg => thread_sound hp hg) hX he hσ hub
      exfalso
      cases s0 <;> simp [frag, Mma.M, Mma.G, Code.glue, Mma.S] at hn'
      exact absurd hinv.2 (by simp [Mma.Start.exit])
    · obtain ⟨hJ, hF⟩ := hR (ub_zero hX he hσ)
      have hs : Mma.succ p L c d e = none := by
        simpa [frag, Mma.M, Mma.G, Code.glue, Mma.code] using hn'
      exact Mma.role_live hp hX hFw hc hc12 he hσ hJ hF hub hs
  | _ => exact hR.elim

/-- **An MMA lane's commits to empty slot `j` are at most its successful polls of full slot `j`**
(at its last followed state, `Mma.commit_le_acq`). -/
theorem mma_com_le_polls (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) {c : Nat}
    (hc : c < L.threads) (h12 : Prologue.warpIndex L c = 12) (j : Fin 3) :
    (X.tr c).countP (commitsTo (obj L c (56 + 8 * j.val))) ≤
      okPolls (obj L c (32 + 8 * j.val)) (X.tr c) := by
  have hReads := cuQReadsFromLaunch hp hX
  have hG := fun k => Mma.good hp hX hReads hc h12 k
  have hlive := warp12_live hp hX hFw hc h12
  obtain ⟨k, ⟨σ, n⟩, hσ, -, hcnt⟩ := Frame.end_countP hX hc (fun k => (hG k).1) hlive
  have hA := hcnt (commitsTo (obj L c (56 + 8 * j.val))) (fun _ => rfl)
  have hP := hcnt (okPoll (obj L c (32 + 8 * j.val))) (fun _ => rfl)
  unfold okPolls
  rw [hA, hP]
  have h1 : ((X.tr c).take k).countP (commitsTo (obj L c (56 + 8 * j.val))) =
      ((X.tr c).take k).countP (cls L c (.mma (.commit (obj L c (56 + 8 * j.val))))) := rfl
  have h2 : ((X.tr c).take k).countP (okPoll (obj L c (32 + 8 * j.val))) =
      ((X.tr c).take k).countP (cls L c (.mma (.acquire (obj L c (32 + 8 * j.val))))) := rfl
  rw [h1, h2, count hσ, count hσ]
  have hR := (hG k).2 _ hσ
  rcases σ with s | ⟨i, d⟩
  · rw [(hR.2.2.1 _).2]; exact Nat.zero_le _
  cases i with
  | mma =>
    rcases d with s0 | ⟨⟨⟩, d⟩
    · rw [(hR.2.2.1 _).2]; exact Nat.zero_le _
    have hub0 : n .ub = 0 := by
      by_contra hne
      obtain ⟨j', -, ⟨pc, kind⟩, hf, hcl⟩ := exists_of_count hσ (Nat.pos_of_ne_zero hne)
      cases kind <;> simp [cls] at hcl
      exact Mma.mma_noUb hp hX hFw hc h12 hf _ rfl
    obtain ⟨r, w, hQ, -⟩ := (hR hub0).1
    have hcom := hQ.com (56 + 8 * j.val)
    have hacq := hQ.acq (32 + 8 * j.val)
    rw [show n (.mma (.commit (obj L c (56 + 8 * j.val)))) = _ from hcom,
      show n (.mma (.acquire (obj L c (32 + 8 * j.val)))) = _ from hacq]
    have := Mma.commit_le_acq d.site.ord r j.val j.isLt
    cases w <;> simp only [ite_true, Bool.false_eq_true, ite_false] <;> omega
  | _ => exact hR.elim

/-- **The K/V bound**: a K/V full barrier's final phase is at most one MMA lane's successful polls
of it plus one. -/
theorem kv_bound (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) (hg : g < L.threads)
    (j : Fin 3) {stF : MBarrier.State}
    (hst : MBarrier.stateBefore (X.objects (obj L g (32 + 8 * j.val)))
      (X.objects (obj L g (32 + 8 * j.val))).length = some stF) :
    ∃ c, c < L.threads ∧ Prologue.warpIndex L c = 12 ∧ c / L.block = g / L.block ∧
      stF.phase ≤ okPolls (obj L g (32 + 8 * j.val)) (X.tr c) + 1 := by
  obtain ⟨c, h12, hcta, hle⟩ := kv_phase hp hX hFw hg j hst
  have hc : c < L.threads := thread_lt_of_cta hg hcta
  have hobj : ∀ o, obj L c o = obj L g o := fun o => by simp only [obj, hcta]
  have := mma_com_le_polls hp hX hFw hc h12 j
  rw [hobj, hobj] at this
  exact ⟨c, hc, h12, hcta, by omega⟩

end
end PTX.Kernels.TmlFa4Fwd.Proof
