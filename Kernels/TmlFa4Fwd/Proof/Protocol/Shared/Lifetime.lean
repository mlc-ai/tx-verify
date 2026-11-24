-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.Mbar.Start
public import Kernels.TmlFa4Fwd.Proof.Protocol.Shared.ShFrame
import Kernels.TmlFa4Fwd.Proof.Protocol.Mbar.Init
import Kernels.TmlFa4Fwd.Proof.Protocol.Mbar.InitOne
import Lemmas.Flow.NthEv

@[expose] public section

/-! # The objects' bytes, the copies' groups and masks

The parts of ERR-OBJECT-LIFETIME that the map of the shared accesses gives: no access covers a byte
of an mbarrier object (`acc_free`: the objects are the startup's, below 240 and from 320 to 352, and
the map's accesses are the allocation word at 312 and bytes from 368 on), two row copies of one
`cp.async` group write apart (`no_overlap`: they are copies of one packet, at two of its places),
and no copy is masked (`no_masked`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow AsyncCopy

noncomputable section

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g k : Nat}

/-- **An access of shared memory is of the allocation word or at `sb + 368` or above.** -/
theorem ShAcc.low {r : Ref} {a : Acc} {w : Bool} (h : ShAcc L X r a w) :
    (∃ g k, r = .thread (g, k) ∧ Prologue.warpIndex L g = 12 ∧ AllocAcc L g a) ∨
      L.sharedBase + 368 ≤ a.loc.addr := by
  cases h with
  | allocWr hw h | allocRd hw h => exact .inl ⟨_, _, rfl, hw, h⟩
  | statWr _ h => obtain ⟨-, n, -, hl⟩ := h; right; rw [hl]; simp only; omega
  | statRd _ _ n st h => right; rw [h.2]; simp only; omega
  | biasRd _ h => obtain ⟨-, -, -, h1, -⟩ := h; right; omega
  | fstWr _ _ st h => obtain ⟨-, q, -, w, -, hl⟩ := h; right; rw [hl]; simp only; omega
  | rowCp _ _ h =>
    obtain ⟨i, j, -, hl⟩ := h.dst
    right; rw [hl]; simp only [Loader.cpAddr]; omega
  | tmaWr _ _ _ _ _ j hlo _ => right; rcases tload_off_apart j with h | h <;> omega
  | mmaA _ _ _ _ hl => right; rw [hl]; simp only; omega
  | mmaB _ _ _ _ hl => right; rw [hl]; simp only; omega
  | storeRd _ _ _ _ st bx _ hlo _ => right; omega

theorem initOff_apart : ∀ q : Fin 34, initOff q + 8 ≤ 240 ∨
    320 ≤ initOff q ∧ initOff q + 8 ≤ 352 := by decide

/-- A footprint's space is that of the bytes it covers. -/
theorem covers_space {a : Acc} {l : Loc} (h : a.Covers l) : a.loc.space = l.space := h.1.symm

theorem cpAddr_inj {g s : Nat} {i i' : Fin 16} {j j' : Fin 2}
    (h1 : Loader.cpAddr L g s i j < Loader.cpAddr L g s i' j' + 16)
    (h2 : Loader.cpAddr L g s i' j' < Loader.cpAddr L g s i j + 16) : i = i' ∧ j = j' := by
  simp only [Loader.cpAddr] at h1 h2
  constructor <;> apply Fin.ext
  · have := j.isLt; have := j'.isLt; omega
  · omega

section
variable (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow p L X)
include hp hX hFw

/-- **No access covers a byte of an mbarrier object.** -/
theorem acc_free : ∀ e a w i o c l, X.Intent e a w → X.MbInit i o c → a.Covers l →
    ¬ Acc.Covers { loc := o, size := 8 } l := by
  intro e a w i o c l hi ⟨pc, hinit⟩ ha ho
  obtain ⟨-, q, -, -, -, -, rfl, -⟩ :=
    init_event hp hX hFw (h := i.1) (k := i.2) (Frame.lt_of_get hX (k := i.2) hinit) hinit
  have hq := initOff_apart q
  simp only [Acc.Covers, Loc.InRange] at ha ho
  obtain ⟨ha1, -, ha2, ha3⟩ := ha
  obtain ⟨ho1, -, ho2, ho3⟩ := ho
  have hs : a.loc.space = .shared := ha1.symm.trans ho1
  rcases (sh_intent hp hX hFw hi hs).low with ⟨g, k, -, -, hz, h⟩ | h
  · rw [h] at ha2 ha3
    simp only at ha2 ha3
    omega
  · omega

/-- A copy is a loader lane's row copy. -/
theorem copy_row {i : EvId} {s : AsyncCopy.Spec} (hc : X.Copy i s) :
    (Prologue.warpIndex L i.1 = 14 ∨ Prologue.warpIndex L i.1 = 15) ∧ LdCp L X i.1 i.2 s := by
  obtain ⟨pc, he⟩ := hc
  rcases mem_event hp hX hFw (g := i.1) (k := i.2) he trivial with ⟨_, _, hk, -⟩ | ⟨_, _, hk, -⟩ |
    ⟨sp', hk, hw, h⟩ | ⟨_, _, hk, -⟩ | ⟨_, _, hk, -⟩ | ⟨_, _, _, _, hk, -⟩ <;> cases hk
  exact ⟨hw, h⟩

/-- **No copy is masked.** -/
theorem no_masked : ¬ MaskedRangeUnalloc m X := by
  apply not_maskedRangeUnalloc_of_none
  intro i s mask hi
  rw [(copy_row hp hX hFw hi).2.whole]
  intro h
  cases h

/-- **Two row copies of one `cp.async` group write apart.** -/
theorem no_overlap : ¬ CpAsyncOverlap X := by
  rintro ⟨⟨g, k⟩, ⟨g', k'⟩, s, s', ⟨-, -, hgg, hlt, hno⟩, hc, hc', l, hl, hl'⟩
  simp only at hgg hlt hno
  subst hgg
  obtain ⟨-, h⟩ := copy_row hp hX hFw hc
  obtain ⟨-, h'⟩ := copy_row hp hX hFw hc'
  simp only at h h'
  -- one packet
  have hpk : pkt X g k = pkt X g k' := by
    rw [← h.commits, ← h'.commits]
    refine le_antisymm (countP_take_mono _ _ hlt.le) ?_
    by_contra hn
    obtain ⟨j, ⟨pce, kd⟩, hj, hje, hcm, hjc⟩ := exists_nthEv (X := X) (g := g) (k := k')
      (p := isAsyncCommit) (n := ((X.tr g).take k).countP isAsyncCommit) (by omega)
    have hkd : kd = .asyncCommit := by
      unfold isAsyncCommit at hcm
      cases kd <;> first | rfl | cases hcm
    subst hkd
    rcases lt_trichotomy j k with hjk | rfl | hjk
    · have h1 := countP_take_succ (p := isAsyncCommit) hje rfl
      have h2 := countP_take_mono isAsyncCommit (X.tr g) (show j + 1 ≤ k by omega)
      rw [h1, hjc] at h2
      omega
    · obtain ⟨pc, he⟩ := hc
      rw [hje] at he
      cases he
    · exact hno j pce hjk hj hje
  obtain ⟨i, j, hN, hd⟩ := h.dst
  obtain ⟨i', j', hN', hd'⟩ := h'.dst
  rw [hd] at hl
  rw [hd', ← hpk] at hl'
  simp only [Acc.Covers, Loc.InRange] at hl hl'
  obtain ⟨rfl, rfl⟩ := cpAddr_inj (L := L) (g := g) (s := pkt X g k % 3) (i := i) (i' := i')
    (j := j) (j' := j') (by omega) (by omega)
  -- two places
  obtain ⟨pc, he⟩ := hc
  have h1 := countP_take_succ (p := cpCopy) he rfl
  have h2 := countP_take_mono cpCopy (X.tr g) (show k + 1 ≤ k' by omega)
  rw [h1] at h2
  unfold pkt at hpk
  omega

end

end
end PTX.Kernels.TmlFa4Fwd.Proof
