-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.KV.Handoff
public import Kernels.TmlFa4Fwd.Proof.Protocol.Shared.ShFrame
import Kernels.TmlFa4Fwd.Proof.Mma.Export.RingSlot
import Kernels.TmlFa4Fwd.Proof.Protocol.Mbar.Use
import Kernels.TmlFa4Fwd.Proof.Protocol.Tmem.FactsProof
import Lemmas.Flow.NthEv
import Lemmas.Protocol.NoIncRingOrder
import Lemmas.Protocol.RegionOrder

@[expose] public section

/-! # The K/V ring: a row copy and an MMA's read of its slot are ordered

Packet `c` of the loader writes slot `c mod 3`; the MMAs of ring use `t` read slot `t mod 3`. A copy
of packet `c ≤ t` of the slot is before the read (`kv_copy_read`): the issuing lane's poll of the
full barrier with `t / 3` earlier ones observes every loader lane's arrive-on with `t / 3` earlier
ones, which tracks the lane's copies up to packet `t`. A read of use `t` is before a copy of a
packet `c > t` of the slot (`kv_read_copy`): the copy follows the lane's poll of the empty barrier
with `t / 3 + 1` earlier ones, which observes the commit with `t / 3` earlier ones, which tracks the
read. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow AsyncCopy PTX.MbarRing

noncomputable section

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g k : Nat}

/-- A lane with more than `n` successful polls of a barrier made the one with `n` earlier ones. -/
theorem nth_poll {l : Loc} {n : Nat} (h : n + 1 ≤ okPolls l ((X.tr g).take k)) :
    ∃ j pc par acq sc, j < k ∧ X.get (g, j) = some ⟨pc, .wait l par true acq sc⟩ ∧
      okPolls l ((X.tr g).take j) = n := by
  obtain ⟨j, ⟨pc, kd⟩, hj, he, hp, hc⟩ := exists_nthEv (X := X) (g := g) (k := k)
    (p := okPoll l) (n := n) h
  unfold okPoll sourceWaitSuccess at hp
  split at hp
  · rename_i hk
    simp only [decide_eq_true_eq] at hp
    simp only at hk
    subst hk
    subst hp
    exact ⟨j, pc, _, _, _, hj, he, hc⟩
  · cases hp

/-- **An MMA that reads the slot of ring use `t`**: a QK MMA of tile `u` (`t = 2 u`) or a PV MMA of
tile `u` (`t = 2 u + 1`). -/
def KvRead (L : Launch) (X : Execution) (g k t : Nat) : Prop :=
  ∃ st u j, Tm.Qk L X g k st u j ∧ t = 2 * u ∨ Tm.Pv L X g k st u j ∧ t = 2 * u + 1

theorem KvRead.use {t : Nat} (h : KvRead L X g k t) :
    t + 1 ≤ Tm.kvPolls L X g k ∧ Tm.kvRels L X g k ≤ t ∧
      ∃ d s acc mask, X.MmaIssue (g, k) d s acc mask := by
  obtain ⟨st, u, j, ⟨h, rfl⟩ | ⟨h, rfl⟩⟩ := h
  · obtain ⟨pc, da, db, he⟩ := h.issue
    exact ⟨by have := h.kv; omega, h.rel, _, _, _, _, pc, he⟩
  · obtain ⟨pc, db, he⟩ := h.issue
    exact ⟨by have := h.kv; omega, h.rel, _, _, _, _, pc, he⟩

section
variable (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow p L X)
include hp hX hFw

/-- **The place of a read in its slot**: more polls of the slot's full barrier, and at most as many
commits to its empty barrier, as the uses of the slot before it. -/
theorem KvRead.slot {t : Nat} (h : KvRead L X g k t) : MmaIn L g g ∧
    t / 3 + 1 ≤ okPolls (obj L g (32 + 8 * (t % 3))) ((X.tr g).take k) ∧
      ((X.tr g).take k).countP (commitsTo (obj L g (56 + 8 * (t % 3)))) ≤ t / 3 := by
  obtain ⟨h1, h2, d, s, acc, mask, hi⟩ := h.use
  have hw := (Tm.mma_qkpv hp hX hFw ⟨_, _, _, _, hi⟩).1
  have hg : g < L.threads := by obtain ⟨pc, he⟩ := hi; exact Frame.lt_of_get hX he
  obtain ⟨e1, e2⟩ := Mma.mma_kv_slots hp hX hw hi ⟨t % 3, Nat.mod_lt _ (by decide)⟩
  simp only at e1 e2
  refine ⟨⟨hg, rfl, hw⟩, by rw [e1]; omega, by rw [e2]; omega⟩

/-- **A copy of packet `c ≤ t` is before the reads of use `t`** of its slot. -/
theorem kv_copy_read {y jc pc t : Nat} {sp : AsyncCopy.Spec} {isB : Bool} {idx : Nat} {l : Loc}
    (hcp : X.get (y, jc) = some ⟨pc, .copy sp⟩)
    (hy : Prologue.warpIndex L y = 14 ∨ Prologue.warpIndex L y = 15) (hC : LdCp L X y jc sp)
    (hR : KvRead L X g k t) (hcta : y / L.block = g / L.block) (hs : pkt X y jc % 3 = t % 3)
    (hle : pkt X y jc ≤ t) (hca : AsyncCovers X (y, jc) (.write .copy) l)
    (hcb : AsyncCovers X (g, k) (.mmaRead isB idx) l) :
    modelCausality L X l (.async (y, jc) (.write .copy)) (.async (g, k) (.mmaRead isB idx)) := by
  obtain ⟨hin, hpoll, -⟩ := hR.slot hp hX hFw
  obtain ⟨-, -, d, s, acc, mask, hi⟩ := hR.use
  obtain ⟨c, hc, -, hcm, hfull, -⟩ := kvHandoff hp hX hFw g hin.1 ⟨t % 3, Nat.mod_lt _ (by decide)⟩
  obtain rfl := hcm hi hin
  -- the poll
  obtain ⟨j, pcj, par, acq, sc, hjk, hje, hjn⟩ := nth_poll hpoll
  have hacq : acq = true := by
    obtain ⟨-, hu⟩ := bar_use (o := 32 + 8 * (t % 3)) hp hX hFw hje rfl (fun _ h => by cases h)
    cases hu with
    | mmaPoll _ _ _ hk => cases hk; rfl
    | ldPoll _ _ _ _ hk | epiPoll _ _ _ _ hk | corrPoll _ _ _ hk | softPoll _ _ _ _ _ hk =>
      cases hk; rfl
    | epiArr _ _ _ hk | corrArr _ _ hk | softArr _ _ _ _ hk | mmaCommit _ _ _ hk
    | ldAsync _ _ hk | ldArr _ _ _ hk | ldCopy _ _ _ _ hk => cases hk
  subst hacq
  obtain ⟨a, rfl⟩ := ldLane_prod (g := g) ⟨hcta, hy⟩
  obtain ⟨i, pci, hie, hin', harr, hob⟩ := hfull hje hjn a
  -- the arrive-on is after the copy
  have hij : jc < i := by
    rcases lt_trichotomy i jc with h | h | h
    · exfalso
      have h1 := countP_take_succ (p := arriveOnTo (obj L g (32 + 8 * (t % 3)))) hie
        (by simp [arriveOnTo])
      have h2 := countP_take_mono (arriveOnTo (obj L g (32 + 8 * (t % 3)))) (X.tr (ldProd L g a))
        (show i + 1 ≤ jc by omega)
      have h3 := hC.arrs
      rw [hs, obj_cta hcta] at h3
      rw [h3, h1, hin'] at h2
      omega
    · subst h; rw [hcp] at hie; cases hie
    · exact h
  have ht : TracksCpAsync X (ldProd L g a, jc) (ldProd L g a, i) :=
    ⟨rfl, hij, ⟨sp, ⟨_, hcp⟩, hC.grp⟩, _, true, ⟨_, hie⟩⟩
  have hya := Frame.lt_of_get hX hcp
  refine ⟨.inl ⟨hya, hin.1, hcta⟩, .direct ⟨hca, hcb, .inl ⟨(g, j), .inr ⟨sc, ⟨_, _,
    .inr ⟨_, true, rfl, ht, ⟨pci, hie⟩, harr⟩, hob⟩,
    Unit.Gate.scopesMeet ⟨hya, hin.1, hcta⟩ _ _⟩, ?_⟩⟩⟩
  obtain ⟨pck, hke⟩ := hi
  exact base_of_poll hje hjk (List.getElem?_eq_some_iff.mp (show (X.tr g)[k]? = _ from hke)).1

/-- **A successful poll of a K/V empty barrier** has acquire semantics. -/
theorem kv_empty_acq {h y j pc par t : Nat} {acq : Bool} {sc : MbarScope}
    (hje : X.get (h, j) = some ⟨pc, .wait (obj L y (56 + 8 * (t % 3))) par true acq sc⟩) :
    acq = true := by
  obtain ⟨-, hu⟩ := bar_use (o := 56 + 8 * (t % 3)) hp hX hFw hje rfl (fun _ h => by cases h)
  cases hu with
  | mmaPoll _ _ _ hk => cases hk; rfl
  | ldPoll _ _ _ _ hk | epiPoll _ _ _ _ hk | corrPoll _ _ _ hk | softPoll _ _ _ _ _ hk =>
    cases hk; rfl
  | epiArr _ _ _ hk | corrArr _ _ hk | softArr _ _ _ _ hk | mmaCommit _ _ _ hk
  | ldAsync _ _ hk | ldArr _ _ _ hk | ldCopy _ _ _ _ hk => cases hk

/-- **A read of use `t` is before the copies of the packets after `t`** of its slot. -/
theorem kv_read_copy {y jc pc t : Nat} {sp : AsyncCopy.Spec} {isB : Bool} {idx : Nat} {l : Loc}
    (hcp : X.get (y, jc) = some ⟨pc, .copy sp⟩)
    (hy : Prologue.warpIndex L y = 14 ∨ Prologue.warpIndex L y = 15) (hC : LdCp L X y jc sp)
    (hR : KvRead L X g k t) (hcta : y / L.block = g / L.block) (hs : pkt X y jc % 3 = t % 3)
    (hlt : t < pkt X y jc) (hca : AsyncCovers X (g, k) (.mmaRead isB idx) l)
    (hcb : AsyncCovers X (y, jc) (.write .copy) l) :
    modelCausality L X l (.async (g, k) (.mmaRead isB idx)) (.async (y, jc) (.write .copy)) := by
  obtain ⟨hin, -, hrel⟩ := hR.slot hp hX hFw
  obtain ⟨-, -, d, s, acc, mask, hi⟩ := hR.use
  obtain ⟨c, hc, -, hcm, -, hempty⟩ := kvHandoff hp hX hFw g hin.1
    ⟨t % 3, Nat.mod_lt _ (by decide)⟩
  obtain rfl := hcm hi hin
  have hp1 : t / 3 + 1 + 1 ≤ okPolls (obj L g (56 + 8 * (t % 3))) ((X.tr y).take jc) := by
    have h3 := hC.polls
    rw [hs, obj_cta hcta] at h3
    rw [h3]
    omega
  obtain ⟨j, pcj, par, acq, sc, hjk, hje, hjn⟩ := nth_poll hp1
  obtain rfl := kv_empty_acq hp hX hFw hje
  obtain ⟨i, pci, spc, rank, hie, hmb, hcnt, -, hob, hdone⟩ := hempty ⟨hcta, hy⟩ hje hjn
  -- the commit is after the read
  obtain ⟨pck, hke⟩ := id hi
  have hki : k < i := by
    rcases lt_trichotomy i k with h | h | h
    · exfalso
      have h1 := countP_take_succ (p := commitsTo (obj L g (56 + 8 * (t % 3)))) hie
        (by simp [commitsTo, hmb])
      have h2 := countP_take_mono (commitsTo (obj L g (56 + 8 * (t % 3)))) (X.tr g)
        (show i + 1 ≤ k by omega)
      rw [h1, hcnt] at h2
      omega
    · subst h; rw [hke] at hie; cases hie
    · exact h
  have ht : TracksMma X (g, k) (g, i) := ⟨rfl, hki, .inl ⟨_, _, _, _, hi⟩, spc, ⟨_, hie⟩⟩
  have hya := Frame.lt_of_get hX hcp
  obtain ⟨n, l', hn, hwo⟩ := hdone _ ht
  refine ⟨.inl ⟨hin.1, hya, hcta.symm⟩, .direct ⟨hca, hcb, .inl ⟨(y, j), .inr ⟨sc, ⟨n, l', hn, hwo⟩,
    Unit.Gate.scopesMeet ⟨hin.1, hya, hcta.symm⟩ _ _⟩, ?_⟩⟩⟩
  exact base_of_poll hje hjk (List.getElem?_eq_some_iff.mp (show (X.tr y)[jc]? = _ from hcp)).1

/-- **A row copy and an MMA's B operand byte of one location are ordered.** -/
theorem kv_row_mma {r r' : Ref} {a a' : Acc} {w w' : Bool} {l : Loc} (hi : X.Intent r a w)
    (hi' : X.Intent r' a' w') (hc : a.Covers l) (hc' : a'.Covers l)
    (hr : ∃ y jc pc sp, r = .async (y, jc) (.write .copy) ∧ X.get (y, jc) = some ⟨pc, .copy sp⟩ ∧
      a = sp.dst)
    (hr' : ∃ g k idx, r' = .async (g, k) (.mmaRead true idx)) :
    modelCausality L X l r r' ∨ modelCausality L X l r' r := by
  obtain ⟨y, jc, pc, sp, rfl, hcp, rfl⟩ := hr
  obtain ⟨g, k, idx, rfl⟩ := hr'
  obtain ⟨hy, hC⟩ : (Prologue.warpIndex L y = 14 ∨ Prologue.warpIndex L y = 15) ∧
      LdCp L X y jc sp := by
    rcases mem_event hp hX hFw hcp trivial with ⟨_, _, hk, -⟩ | ⟨_, _, hk, -⟩ | ⟨sp', hk, hw, h⟩ |
      ⟨_, _, hk, -⟩ | ⟨_, _, hk, -⟩ | ⟨_, _, _, _, hk, -⟩ <;> cases hk
    exact ⟨hw, h⟩
  cases sh_intent hp hX hFw hi' (Execution.mmaFootprint_shared hi'.2.2) with
  | @mmaB _ _ _ _ st u j off t hst h hz ho hl =>
    have hR : KvRead L X g k t := ⟨st, u, j, h⟩
    obtain ⟨i, j', -, hd⟩ := hC.dst
    have hcl := Loader.rowCol_lt _ (Nat.mod_lt (y % L.block) (show 0 < 64 by decide))
    have h3 := Nat.mod_lt (pkt X y jc) (show 0 < 3 by decide)
    have h3' := Nat.mod_lt t (show 0 < 3 by decide)
    have hij := i.isLt
    have hjj := j'.isLt
    have hcv := hc
    have hcv' := hc'
    simp only [Acc.Covers, Loc.InRange, hd, hl, hz, Loader.cpAddr] at hcv hcv'
    obtain ⟨-, hct, h1, h2⟩ := hcv
    obtain ⟨-, hct', h1', h2'⟩ := hcv'
    have hcta : y / L.block = g / L.block := hct.symm.trans hct'
    have hs : pkt X y jc % 3 = t % 3 := by omega
    have hca : AsyncCovers X (y, jc) (.write .copy) l := ⟨_, _, hi, hc⟩
    have hcb : AsyncCovers X (g, k) (.mmaRead true idx) l := ⟨_, _, hi', hc'⟩
    by_cases hle : pkt X y jc ≤ t
    · exact .inl (kv_copy_read hp hX hFw hcp hy hC hR hcta hs hle hca hcb)
    · exact .inr (kv_read_copy hp hX hFw hcp hy hC hR hcta hs (by omega) hcb hca)

end

end
end PTX.Kernels.TmlFa4Fwd.Proof
