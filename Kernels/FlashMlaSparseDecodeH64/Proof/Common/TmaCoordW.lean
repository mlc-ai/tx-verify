-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.TmaLen
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.CoordLoad
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.LastAt

@[expose] public section

/-! # The coordinate words in the TMA lane's state are 32-bit words

`CoordW d`: the words the state keeps at the sites of `CoordInv` (`Common/TmaCoordInv.lean`) are
32-bit words, when every read of the lane at a pc of its code rebuilds to one (`CoordWordsBits`).
`coordW_step` is one step. -/

/-! # The coordinate words in the TMA lane's state are its last reads

The TMA lane's state keeps the words of its coordinate loads (`ac`, `cq`, `cp`,
`Tma/Machine.lean`). `CoordInv X g i d`: at the state before event `i` of lane `g`, the words
the state keeps are the words of the lane's last reads at the loads' pcs (`coordWords`): at the
elements of quadruple `k`'s load the elements so far (`accOf`) and quadruple `k - 1` in `cq`, at
gather `k` quadruple `k` in `cp` and `k + 1` in `cq` (quadruple 15 in `cq` at the last gather).
`coordInv_step` is one step, `tma_coordInv` the invariant at every state of the lane's winner. -/

/-! # The winner's region with the trace index

`tma_region_idx`: like `tma_region` (`Common/TmaLen.lean`), but the invariant `Q i d` names the
trace index `i` of its state, so that it can speak of the lane's earlier events, and a step also
knows its event's pc is its site's. The induction runs up to a bound `K` below which the lane has
no undefined behaviour. For the TMA role's value exports. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow MbarRow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- The TMA states after the election with `Q` at index `i`. -/
def TmaIdxR (Q : Nat → Tma.D → Prop) (i : Nat) : (thread P L g).D → Prop :=
  fun σ => ∃ d n, σ = (.inr ⟨.inl .wg1, .inr ⟨.inl .tma, d⟩⟩, n) ∧ Tma.Post d.site ∧ Q i d

/-- **The winner's region with the trace index**: after the election that lane `g` won (at
`j`), every state before index `K` is a TMA state with `Q` at its index, when every elected
first state has `Q`, and every step of the lane keeps it. -/
theorem tma_region_idx (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (Q : Nat → Tma.D → Prop) {j inst K : Nat} (hKl : K ≤ (X.tr g).length)
    (hj : X.get (g, j) = some ⟨2165, .elect (2 ^ 32 - 1) inst (PTX.laneOf L g)⟩)
    (hub : ∀ i0 f, j < i0 → i0 < K → (X.tr g)[i0]? = some f → ∀ fl, f.kind ≠ .ub fl)
    (hlead : ∀ d, Q (j + 1) (Tma.leadNext P L g d))
    (hstep : ∀ {i0 : Nat} {d a : Tma.D} {n : Cls → Nat} {f : Event}, j < i0 → i0 < K →
      Frame.stateAt (thread P L) X g i0 =
        some (some (.inr ⟨.inl .wg1, .inr ⟨.inl .tma, d⟩⟩, n)) →
      Tma.Post d.site → Q i0 d → (X.tr g)[i0]? = some f → f.pc = d.site.pc →
      Tma.succ P L g d f = some (some a) → Q (i0 + 1) a)
    {i : Nat} (hji : j < i) (hiK : i ≤ K) {σ : (thread P L g).D}
    (hσ : Frame.stateAt (thread P L) X g i = some (some σ)) : TmaIdxR Q i σ := by
  induction i, (Nat.succ_le_of_lt hji) using Nat.le_induction generalizing σ with
  | base =>
    rcases tma_lead hp hX hFw hj with hn | ⟨dj, nj, hn⟩
    · rw [hn] at hσ
      cases hσ
    · rw [hn, Option.some.injEq, Option.some.injEq] at hσ
      subst hσ
      exact ⟨_, _, rfl, (Tma.lead_post (P := P) (L := L) (g := g) dj).1, hlead dj⟩
  | succ i hji' ih =>
    obtain ⟨f, hg⟩ : ∃ f, (X.tr g)[i]? = some f :=
      ⟨_, List.getElem?_eq_getElem (by omega)⟩
    rw [Frame.stateAt_succ hg] at hσ
    cases hs : Frame.stateAt (thread P L) X g i with
    | none => simp [hs] at hσ
    | some o =>
      rw [hs] at hσ
      cases o with
      | none => simp [Code.toMachine] at hσ
      | some σ0 =>
        obtain ⟨d, n, rfl, hP, hq⟩ := ih (by omega) (by omega) hs
        simp only [Option.bind_some] at hσ
        obtain ⟨a, ha, rfl⟩ := sub_step hσ fun a ha =>
          by simp [subBack, (Tma.succ_post (P := P) (L := L) (g := g) hP ha).2 _]
        have hget : X.get (g, i) = some f := hg
        obtain ⟨σ1, hσ1, -, -, -, hpc⟩ := ev_at hp hX hFw hget
          (hub i f (by omega) (by omega) hg)
        rw [hs] at hσ1
        cases hσ1
        exact ⟨a, _, rfl, Tma.succ_post hP ha, hstep (by omega) (by omega) hs hP hq hg hpc ha⟩

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow MbarRow

noncomputable section

/-- The words the state keeps are the lane's last reads. -/
def CoordInv (X : Execution) (g i : Nat) (d : Tma.D) : Prop :=
  match d.site with
  | .coord0 k => 1 ≤ k.val → d.cq.list = coordWords X g i (k.val - 1)
  | .coord1 k => Tma.accOf d = (lastAt X g i (coordLoadPc k.val) 1).map rdVal ∧
      (1 ≤ k.val → d.cq.list = coordWords X g i (k.val - 1))
  | .coord2 k => Tma.accOf d = (lastAt X g i (coordLoadPc k.val) 2).map rdVal ∧
      (1 ≤ k.val → d.cq.list = coordWords X g i (k.val - 1))
  | .coord3 k => Tma.accOf d = (lastAt X g i (coordLoadPc k.val) 3).map rdVal ∧
      (1 ≤ k.val → d.cq.list = coordWords X g i (k.val - 1))
  | .gather k => (k.val < 15 → d.cp.list = coordWords X g i k.val ∧
      d.cq.list = coordWords X g i (k.val + 1)) ∧
      (k.val = 15 → d.cq.list = coordWords X g i 15)
  | _ => True

/-- The coordinate loads' pcs are distinct. -/
theorem coordLoadPc_inj {a b : Nat} (ha : a < 16) (hb : b < 16)
    (h : coordLoadPc a = coordLoadPc b) : a = b := by
  unfold coordLoadPc at h
  split_ifs at h <;> omega

/-- No gather's pc is a coordinate load's. -/
theorem gatherPc_ne {a b : Nat} (ha : a < 16) (hb : b < 16) : gatherPc a ≠ coordLoadPc b := by
  unfold gatherPc coordLoadPc
  split_ifs <;> omega


variable {P : Params} {L : Launch} {X : Execution} {g i : Nat} {f : Event}

theorem lastAt_zero (X : Execution) (g i p : Nat) : lastAt X g i p 0 = [] := by
  simp [lastAt, lastN]

theorem rdVal_rd {a : Acc} {bs : List (Option Byte)} (h : f.kind = .rd a bs) :
    rdVal f = (rebuild 3 bs).toOption.getD (.pred false) := by
  simp [rdVal, h]

/-- The event of a coordinate element is a read. -/
theorem rdAny_of {a : Tma.D} {c : Value → Tma.D}
    (hs : Tma.rdAny f c = some (some a)) :
    ∃ ac bs, f.kind = .rd ac bs ∧ a = c (rdVal f) := by
  unfold Tma.rdAny at hs
  split at hs
  · rename_i ac bs hk
    simp only [Option.some.injEq] at hs
    exact ⟨ac, bs, hk, by rw [rdVal_rd hk, hs]⟩
  · cases hs

/-- The words of the other loads stay as they were when an event at another pc comes. -/
private theorem words_stay (hg : (X.tr g)[i]? = some f) {q : Nat} (h : f.pc ≠ coordLoadPc q) :
    coordWords X g (i + 1) q = coordWords X g i q := by
  unfold coordWords
  rw [lastAt_succ_ne hg h]

/-- A site that is no coordinate element and no gather (the first element is the loop's
entry). -/
def Tma.Site.Plain : Tma.Site → Prop
  | .coord0 k => k.val = 0
  | .coord1 _ | .coord2 _ | .coord3 _ | .gather _ => False
  | _ => True

/-- A site outside the block's loads and gathers. -/
def Tma.Site.Other : Tma.Site → Prop
  | .coord0 _ | .coord1 _ | .coord2 _ | .coord3 _ | .gather _ => False
  | _ => True

private theorem plain_lens (d : Tma.D) (x y : BitVec 64) : (Tma.lensD d x y).site.Plain := by
  simp [Tma.lensD, Tma.Site.Plain]

theorem plain_lead (d : Tma.D) : (Tma.leadNext P L g d).site.Plain := by
  unfold Tma.leadNext
  split
  · simp [Tma.Site.Plain]
  split
  · unfold Tma.afterTopk
    split <;> simp [Tma.lensD, Tma.Site.Plain]
  · simp [Tma.Site.Plain]

private theorem plain_entry (d : Tma.D) : (Tma.loopEntry d).site.Plain := by
  unfold Tma.loopEntry
  split <;> simp [Tma.Site.Plain]

private theorem plain_end (d : Tma.D) : (Tma.loopEnd d).site.Plain := by
  unfold Tma.loopEnd
  split <;> simp [Tma.Site.Plain]

private theorem poll_cases {d d' a : Tma.D} {e : Event} (h : Tma.poll d e d' = some (some a)) :
    a = d ∨ a = d' := by
  unfold Tma.poll at h
  split at h
  · simp only [Option.some.injEq] at h
    subst h
    split <;> simp
  · cases h

private theorem nc_cases {e : Event} {c : BitVec 64 → Tma.D} {a : Tma.D}
    (h : Tma.ncWord e c = some (some a)) : ∃ x, a = c x := by
  unfold Tma.ncWord at h
  split at h
  · split at h
    · unfold Tma.word32 at h
      split at h
      · simp only [Option.some.injEq] at h
        exact ⟨_, h.symm⟩
      · cases h
    · cases h
  · cases h

/-- **A step from a site outside the loads and gathers goes to a plain site.** -/
theorem plain_succ {d a : Tma.D} (hs : d.site.Other)
    (h : Tma.succ P L g d f = some (some a)) : a.site.Plain := by
  cases hd : d.site
  case coord0 => rw [hd] at hs; exact hs.elim
  case coord1 => rw [hd] at hs; exact hs.elim
  case coord2 => rw [hd] at hs; exact hs.elim
  case coord3 => rw [hd] at hs; exact hs.elim
  case gather => rw [hd] at hs; exact hs.elim
  case elect =>
    simp only [Tma.succ, hd, Tma.electNext] at h
    split at h
    · simp only [Option.some.injEq] at h
      subst h
      split
      · exact plain_lead _
      · simp [Tma.Site.Plain]
    · cases h
  case loadTopk =>
    simp only [Tma.succ, hd] at h
    obtain ⟨x, rfl⟩ := nc_cases h
    unfold Tma.afterTopk
    split <;> simp [Tma.lensD, Tma.Site.Plain]
  case loadExtra =>
    simp only [Tma.succ, hd] at h
    obtain ⟨x, rfl⟩ := nc_cases h
    exact plain_lens _ _ _
  case qWait =>
    simp only [Tma.succ, hd] at h
    rcases poll_cases h with rfl | rfl <;> simp [Tma.Site.Plain, hd]
  case storeWait =>
    simp only [Tma.succ, hd] at h
    rcases poll_cases h with rfl | rfl
    · simp [hd, Tma.Site.Plain]
    · exact plain_entry _
  case coordWait =>
    simp only [Tma.succ, hd] at h
    rcases poll_cases h with rfl | rfl <;> simp [Tma.Site.Plain, hd]
  case rawWait =>
    simp only [Tma.succ, hd] at h
    rcases poll_cases h with rfl | rfl <;> simp [Tma.Site.Plain, hd]
  case rawArrive =>
    simp only [Tma.succ, hd, Option.some.injEq] at h
    subst h
    simp [Tma.Site.Plain]
  case coordFree =>
    simp only [Tma.succ, hd, Option.some.injEq] at h
    subst h
    exact plain_end _
  case outBar =>
    simp only [Tma.succ, hd, Option.some.injEq] at h
    subst h
    simp [Tma.Site.Plain]
  case exit => simp [Tma.succ, hd] at h
  case leave => simp only [Tma.succ, hd] at h; cases h

theorem coordInv_plain {a : Tma.D} (h : a.site.Plain) : CoordInv X g i a := by
  unfold CoordInv
  cases hs : a.site <;> simp_all [Tma.Site.Plain]

private theorem pc_ne {p k q : Nat} (hk : k < 16) (hq : q < 16) (hn : q ≠ k)
    (hp : p = coordLoadPc k) : p ≠ coordLoadPc q :=
  fun h => hn (coordLoadPc_inj hq hk (h.symm.trans hp))

/-- **A step keeps the invariant.** -/
theorem coordInv_step {d a : Tma.D} (hg : (X.tr g)[i]? = some f) (hpc : f.pc = d.site.pc)
    (hq : CoordInv X g i d) (ha : Tma.succ P L g d f = some (some a)) :
    CoordInv X g (i + 1) a := by
  obtain ⟨s, l0, l1, neg, cnt, buf, slot, pf, pr, ac, cp, cq⟩ := d
  dsimp only at hpc hq ha
  cases s with
  | coord0 k =>
    simp only [Tma.succ] at ha
    obtain ⟨-, -, hk, rfl⟩ := rdAny_of ha
    have hpk : f.pc = coordLoadPc k.val := hpc
    refine ⟨?_, fun h1 => ?_⟩
    · simp only [Tma.accOf]
      rw [lastAt_succ_eq hg hpk 0, lastAt_zero]
      rfl
    · simp only [CoordInv] at hq
      rw [words_stay hg (pc_ne k.isLt (by omega) (by omega) hpk)]
      exact hq h1
  | coord1 k =>
    simp only [Tma.succ] at ha
    obtain ⟨-, -, hk, rfl⟩ := rdAny_of ha
    have hpk : f.pc = coordLoadPc k.val := hpc
    simp only [CoordInv, Tma.accOf] at hq ⊢
    refine ⟨?_, fun h1 => ?_⟩
    · rw [lastAt_succ_eq hg hpk 1, List.map_append, ← hq.1]
      rfl
    · rw [words_stay hg (pc_ne k.isLt (by omega) (by omega) hpk)]
      exact hq.2 h1
  | coord2 k =>
    simp only [Tma.succ] at ha
    obtain ⟨-, -, hk, rfl⟩ := rdAny_of ha
    have hpk : f.pc = coordLoadPc k.val := hpc
    simp only [CoordInv, Tma.accOf] at hq ⊢
    refine ⟨?_, fun h1 => ?_⟩
    · rw [lastAt_succ_eq hg hpk 2, List.map_append, ← hq.1]
      rfl
    · rw [words_stay hg (pc_ne k.isLt (by omega) (by omega) hpk)]
      exact hq.2 h1
  | coord3 k =>
    simp only [Tma.succ] at ha
    obtain ⟨-, -, hk, rfl⟩ := rdAny_of ha
    have hpk : f.pc = coordLoadPc k.val := hpc
    simp only [CoordInv, Tma.accOf] at hq
    have hnew : (Tma.afterQuad ⟨.coord3 k, l0, l1, neg, cnt, buf, slot, pf, pr, ac, cp, cq⟩ k
        (rdVal f)).cq.list = coordWords X g (i + 1) k.val := by
      unfold coordWords
      rw [lastAt_succ_eq hg hpk 3, List.map_append, ← hq.1]
      rfl
    unfold Tma.afterQuad Tma.afterCoord
    by_cases h0 : k.val = 0
    · simp only [h0, ↓reduceIte, CoordInv]
      intro _
      rw [show ((1 : Fin 16).val - 1) = k.val by rw [h0]; rfl]
      exact hnew
    · simp only [h0, ↓reduceIte, CoordInv]
      refine ⟨fun _ => ⟨?_, ?_⟩, fun h => by omega⟩
      · rw [words_stay hg (pc_ne k.isLt (by omega) (by omega) hpk)]
        exact hq.2 (by omega)
      · rw [show k.val - 1 + 1 = k.val by omega]
        exact hnew
  | gather k =>
    simp only [Tma.succ] at ha
    obtain rfl := (Option.some.inj (Option.some.inj ha))
    have hpk : f.pc = gatherPc k.val := by
      rw [hpc]; unfold Tma.Site.pc gatherPc; rfl
    simp only [CoordInv] at hq
    unfold Tma.afterGather
    by_cases h15 : k.val = 15
    · simp [h15, CoordInv]
    by_cases h14 : k.val = 14
    · simp only [h14, ↓reduceIte, CoordInv]
      refine ⟨fun h => by omega, fun _ => ?_⟩
      have := (hq.1 (by omega)).2
      have h15' : coordWords X g i 15 = coordWords X g i (k.val + 1) := by
        rw [show k.val + 1 = 15 by omega]
      rw [words_stay hg (hpk ▸ gatherPc_ne k.isLt (by omega)), h15']
      exact this
    · simp only [h15, h14, ↓reduceIte, CoordInv]
      have hv : (k + 2 : Fin 16).val = k.val + 2 := by
        rw [Fin.val_add]; show (k.val + 2) % 16 = _; omega
      intro _
      rw [hv, words_stay hg (hpk ▸ gatherPc_ne k.isLt (by omega))]
      rw [show k.val + 2 - 1 = k.val + 1 by omega]
      exact (hq.1 (by omega)).2
  | elect | loadTopk | loadExtra | qWait | storeWait | coordWait | rawWait | rawArrive
    | coordFree | outBar | exit | leave _ =>
    exact coordInv_plain (plain_succ (by simp [Tma.Site.Other]) ha)

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

/-- A value that is a 32-bit word. -/
def IsW32 (v : Value) : Prop := ∃ z, v = .bits 32 z

/-- The words the state keeps are 32-bit words. -/
def CoordW (d : Tma.D) : Prop :=
  match d.site with
  | .coord0 k => 1 ≤ k.val → ∀ v ∈ d.cq.list, IsW32 v
  | .coord1 k | .coord2 k | .coord3 k =>
      (∀ v ∈ Tma.accOf d, IsW32 v) ∧ (1 ≤ k.val → ∀ v ∈ d.cq.list, IsW32 v)
  | .gather k => (k.val < 15 → (∀ v ∈ d.cp.list, IsW32 v) ∧ ∀ v ∈ d.cq.list, IsW32 v) ∧
      (k.val = 15 → ∀ v ∈ d.cq.list, IsW32 v)
  | _ => True

variable {P : Params} {L : Launch} {g : Nat} {f : Event}

theorem coordPc_range (k : Fin 16) : 2162 ≤ Tma.coordPc k ∧ Tma.coordPc k < 2332 := by
  fin_cases k <;> decide

theorem coordW_plain {a : Tma.D} (h : a.site.Plain) : CoordW a := by
  unfold CoordW
  cases hs : a.site <;> simp_all [Tma.Site.Plain]

/-- A step keeps `CoordW`, when the event of a coordinate element is a 32-bit word. -/
theorem coordW_step {d a : Tma.D} (hpc : f.pc = d.site.pc)
    (hv : ∀ ac bs, f.kind = .rd ac bs → 2162 ≤ f.pc → f.pc < 2332 → IsW32 (rdVal f))
    (hq : CoordW d) (ha : Tma.succ P L g d f = some (some a)) : CoordW a := by
  obtain ⟨s, l0, l1, neg, cnt, buf, slot, pf, pr, ac, cp, cq⟩ := d
  dsimp only at hpc hq ha
  cases s with
  | coord0 k =>
    simp only [Tma.succ] at ha
    obtain ⟨ac', bs, hk, rfl⟩ := rdAny_of ha
    simp only [CoordW, Tma.accOf] at hq ⊢
    have := hv ac' bs hk (by rw [hpc]; exact (coordPc_range _).1)
      (by rw [hpc]; exact (coordPc_range _).2)
    refine ⟨fun v hv' => ?_, hq⟩
    simp only [List.mem_singleton] at hv'
    exact hv' ▸ this
  | coord1 k =>
    simp only [Tma.succ] at ha
    obtain ⟨ac', bs, hk, rfl⟩ := rdAny_of ha
    simp only [CoordW, Tma.accOf] at hq ⊢
    have := hv ac' bs hk (by rw [hpc]; exact (coordPc_range _).1)
      (by rw [hpc]; exact (coordPc_range _).2)
    refine ⟨fun v hv' => ?_, hq.2⟩
    rcases List.mem_cons.mp hv' with rfl | hv'
    · exact hq.1 _ (by simp)
    · simp only [List.mem_singleton] at hv'
      exact hv' ▸ this
  | coord2 k =>
    simp only [Tma.succ] at ha
    obtain ⟨ac', bs, hk, rfl⟩ := rdAny_of ha
    simp only [CoordW, Tma.accOf] at hq ⊢
    have := hv ac' bs hk (by rw [hpc]; exact (coordPc_range _).1)
      (by rw [hpc]; exact (coordPc_range _).2)
    refine ⟨fun v hv' => ?_, hq.2⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv'
    rcases hv' with rfl | rfl | rfl
    · exact hq.1 _ (by simp)
    · exact hq.1 _ (by simp)
    · exact this
  | coord3 k =>
    simp only [Tma.succ] at ha
    obtain ⟨ac', bs, hk, rfl⟩ := rdAny_of ha
    simp only [CoordW, Tma.accOf] at hq
    have := hv ac' bs hk (by rw [hpc]; exact (coordPc_range _).1)
      (by rw [hpc]; exact (coordPc_range _).2)
    have hnew : ∀ w ∈ ({ ac with w3 := rdVal f } : Tma.Quad).list, IsW32 w := by
      intro w hw
      simp only [Tma.Quad.list, List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl | rfl
      · exact hq.1 _ (by simp)
      · exact hq.1 _ (by simp)
      · exact hq.1 _ (by simp)
      · exact this
    unfold Tma.afterQuad Tma.afterCoord
    by_cases h0 : k.val = 0
    · simp only [h0, ↓reduceIte, CoordW]
      exact fun _ => hnew
    · simp only [h0, ↓reduceIte, CoordW]
      exact ⟨fun _ => ⟨hq.2 (by omega), hnew⟩, fun h => by omega⟩
  | gather k =>
    simp only [Tma.succ] at ha
    obtain rfl := (Option.some.inj (Option.some.inj ha))
    simp only [CoordW] at hq
    unfold Tma.afterGather
    by_cases h15 : k.val = 15
    · simp [h15, CoordW]
    by_cases h14 : k.val = 14
    · simp only [h14, ↓reduceIte, CoordW]
      exact ⟨fun h => by omega, fun _ => (hq.1 (by omega)).2⟩
    · simp only [h15, h14, ↓reduceIte, CoordW]
      intro _
      exact (hq.1 (by omega)).2
  | elect | loadTopk | loadExtra | qWait | storeWait | coordWait | rawWait | rawArrive
    | coordFree | outBar | exit | leave _ =>
    exact coordW_plain (plain_succ (by simp [Tma.Site.Other]) ha)

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
