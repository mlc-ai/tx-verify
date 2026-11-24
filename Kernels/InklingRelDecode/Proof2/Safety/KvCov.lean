-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof2.Safety.KvRace
public import Kernels.InklingRelDecode.Proof2.Lib.KvCover
public import Lemmas.Tcgen05.MmaObservedReads

@[expose] public section

/-! # The MMA lane's reads of a released use cover its slot

Before the MMA lane's commit to `kv_empty s` (the PV half's first commit of iteration `i`, with
`(i - 1) % 3 = s`) the lane made the eight QK MMAs of iteration `i - 1` (they read the K tile of
slot `s`) and the eight PV MMAs of iteration `i` (the V tile of slot `s`), with no commit to
`kv_empty s` since. The lane that leads its elections never takes the branches that skip an MMA
(`ElectLead`), and its broadcasts receive 7 (`mma_recv7`), so it never skips a half.

* `KH`, `VH`: the lane's state at an earlier position is the QK (PV) MMA `j` of iteration `t`,
  with the same commits to the slot's `kv_empty` since;
* `HI`, `hi_inv`: at the lane's MMA states, the QK MMAs of the previous iteration (until the PV
  half's first commit), of the current one once done, and the PV MMAs done;
* `hcover`: the premise of `SingleTmaRing.copies_chain` for the declared ring. -/

namespace PTX.Kernels.InklingRelDecode.Proof2
open PTX PTX.Proof PTX.Flow PTX.Frame AsyncCopy

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- The lane's commits to `kv_empty s` of its CTA before position `k`. -/
abbrev cmE (L : Launch) (X : Execution) (g s k : Nat) : Nat :=
  ((X.tr g).take k).countP (commitsTo (Proof.EvW.kvEmpty L (g / L.block) s))

/-- The lane's state at position `kR` is an MMA state satisfying `p`. -/
def AtMma (Q : Params) (L : Launch) (X : Execution) (g kR : Nat) (p : Proof.Mma.D → Prop) :
    Prop :=
  ∃ tm dR P n, Frame.stateAt (thread Q L) X g kR =
    some (some (.inr ⟨.inl (.worker tm), .mma dR P⟩, n)) ∧ p dR

/-- **QK MMA `j` of iteration `t` happened before `k`**, with no commit to `kv_empty (t % 3)`
since. -/
def KH (Q : Params) (L : Launch) (X : Execution) (g t : Nat) (j : Fin 8) (k : Nat) : Prop :=
  ∃ kR < k, AtMma Q L X g kR (fun dR => dR.site = .qk j ∧ dR.i = t) ∧
    cmE L X g (t % 3) kR = cmE L X g (t % 3) k

/-- **PV MMA `j` of iteration `t` happened before `k`**, with no commit to
`kv_empty ((t - 1) % 3)` since. -/
def VH (Q : Params) (L : Launch) (X : Execution) (g t : Nat) (j : Fin 8) (k : Nat) : Prop :=
  ∃ kR < k, AtMma Q L X g kR (fun dR => dR.site = .pv j ∧ dR.i = t) ∧
    cmE L X g ((t - 1) % 3) kR = cmE L X g ((t - 1) % 3) k

/-- The QK half's sites. -/
def qkS : Proof.Mma.Site → Bool
  | .qkBar | .kvWait | .qkShfl | .qkBar2 | .qkElect | .qk _ | .qkCommit => true
  | _ => false

/-- The PV half's sites up to its first commit. -/
def pvS : Proof.Mma.Site → Bool
  | .pvBar | .pWait | .pvShfl | .pvBar2 | .pvElect | .pv _ | .pvCommit1 => true
  | _ => false

/-- The QK MMAs done in the current half. -/
def kd : Proof.Mma.Site → Nat
  | .qk j => j.val
  | .qkCommit | .pvBar | .pWait | .pvShfl | .pvBar2 | .pvElect | .pv _ | .pvCommit1
  | .pvCommit2 => 8
  | _ => 0

/-- The PV MMAs done in the current half. -/
def vd : Proof.Mma.Site → Nat
  | .pv j => j.val
  | .pvCommit1 => 8
  | _ => 0

/-- **The history of the MMA lane at an MMA state.** -/
def HI (Q : Params) (L : Launch) (X : Execution) (g : Nat) (d : Proof.Mma.D) (k : Nat) : Prop :=
  ((qkS d.site = true ∧ 1 ≤ d.i) ∨ pvS d.site = true → ∀ j, KH Q L X g (d.i - 1) j k) ∧
  (∀ j : Fin 8, j.val < kd d.site → (qkS d.site = true ∨ d.i < d.n) → KH Q L X g d.i j k) ∧
  (∀ j : Fin 8, j.val < vd d.site → VH Q L X g d.i j k) ∧
  d.site ≠ .qkSkip ∧ d.site ≠ .pvSkip

theorem cmE_succ {s k : Nat} {e : Event} (he : (X.tr g)[k]? = some e) :
    cmE L X g s (k + 1) =
      cmE L X g s k + if commitsTo (Proof.EvW.kvEmpty L (g / L.block) s) e then 1 else 0 := by
  simp only [cmE, List.take_add_one, he, Option.toList_some, List.countP_append,
    List.countP_singleton]

theorem KH_succ {t : Nat} {j : Fin 8} {k : Nat} {e : Event} (he : (X.tr g)[k]? = some e)
    (h : KH Q L X g t j k)
    (hc : commitsTo (Proof.EvW.kvEmpty L (g / L.block) (t % 3)) e = false) :
    KH Q L X g t j (k + 1) := by
  obtain ⟨kR, hkR, hA, hcnt⟩ := h
  exact ⟨kR, by omega, hA, by rw [cmE_succ he, hc, hcnt]; rfl⟩

theorem VH_succ {t : Nat} {j : Fin 8} {k : Nat} {e : Event} (he : (X.tr g)[k]? = some e)
    (h : VH Q L X g t j k)
    (hc : commitsTo (Proof.EvW.kvEmpty L (g / L.block) ((t - 1) % 3)) e = false) :
    VH Q L X g t j (k + 1) := by
  obtain ⟨kR, hkR, hA, hcnt⟩ := h
  exact ⟨kR, by omega, hA, by rw [cmE_succ he, hc, hcnt]; rfl⟩

theorem kvEmpty_ne_sReady {c c' s b : Nat} (hs : s < 3) :
    Proof.EvW.kvEmpty L c s ≠ Proof.EvW.sReady L c' b := by
  simp only [Proof.EvW.kvEmpty, Proof.EvW.sReady, Proof.EvW.barLoc, Proof.EvW.kvEmptyOff,
    Proof.EvW.sReadyOff, ne_eq, Loc.mk.injEq, true_and, not_and]
  intro _; omega

/-- **The MMA warp's commits to `kv_empty`** are its PV half's first commits, to the slot of the
iteration's previous block. -/
theorem mm_commit_kv {d : Proof.Mma.D} {e : Event} (hsh : Proof.EvW.MmShape L g d e) {s : Nat}
    (hs : s < 3) (hc : commitsTo (Proof.EvW.kvEmpty L (g / L.block) s) e = true) :
    d.site = .pvCommit1 ∧ s = (d.i - 1) % 3 := by
  obtain ⟨site, i, n, tm, pro⟩ := d
  cases site
  all_goals simp only [Proof.EvW.MmShape] at hsh
  case pvCommit1 =>
    subst hsh
    simp only [commitsTo, Proof.EvW.commitSpec] at hc
    simp only [Proof.EvW.kvEmpty, Proof.EvW.barLoc, Proof.EvW.kvEmptyOff, Loc.mk.injEq,
      true_and, decide_eq_true_eq] at hc
    refine ⟨rfl, ?_⟩
    dsimp only at hc ⊢
    omega
  all_goals exfalso
  all_goals first
    | (subst hsh; simp [commitsTo, Proof.EvW.commitSpec, Proof.EvW.kvEmpty, Proof.EvW.sReady,
        Proof.EvW.oDone, Proof.EvW.oFinal, Proof.EvW.barLoc, Proof.EvW.kvEmptyOff,
        Proof.EvW.sReadyOff, Proof.EvW.oDoneOff, Proof.EvW.oFinalOff] at hc; omega)
    | (subst hsh; simp [commitsTo] at hc)
    | (obtain ⟨_, rfl⟩ := hsh; simp [commitsTo] at hc)
    | (obtain ⟨_, _, rfl⟩ := hsh; simp [commitsTo] at hc)
    | (obtain ⟨_, _, rfl, -⟩ := hsh; simp [commitsTo] at hc)
    | (obtain ⟨_, _, _, _, _, _, rfl⟩ := hsh; simp [commitsTo] at hc)
/-- A step within one half of an iteration keeps the history. -/
theorem hi_same {k : Nat} {d d' : Proof.Mma.D} {e : Event} (he : (X.tr g)[k]? = some e)
    (hd : HI Q L X g d k)
    (hA : (qkS d'.site = true ∧ 1 ≤ d'.i) ∨ pvS d'.site = true →
      (qkS d.site = true ∧ 1 ≤ d.i) ∨ pvS d.site = true)
    (hi : d'.i = d.i) (hn : d'.n = d.n) (hq : qkS d'.site = true → qkS d.site = true)
    (hkd : ∀ j : Fin 8, j.val < kd d'.site → j.val < kd d.site ∨ d.site = .qk j)
    (hvd : ∀ j : Fin 8, j.val < vd d'.site → j.val < vd d.site ∨ d.site = .pv j)
    (hns : d'.site ≠ .qkSkip ∧ d'.site ≠ .pvSkip)
    (hnc : ∀ s < 3, commitsTo (Proof.EvW.kvEmpty L (g / L.block) s) e = false)
    (newK : ∀ j, d.site = .qk j → KH Q L X g d.i j (k + 1))
    (newV : ∀ j, d.site = .pv j → VH Q L X g d.i j (k + 1)) :
    HI Q L X g d' (k + 1) := by
  obtain ⟨h1, h2, h3, -⟩ := hd
  refine ⟨fun hA' j => ?_, fun j hj hc => ?_, fun j hj => ?_, hns⟩
  · rw [hi]; exact KH_succ he (h1 (hA hA') j) (hnc _ (Nat.mod_lt _ (by omega)))
  · rw [hi]
    rcases hkd j hj with hlt | hs
    · refine KH_succ he (h2 j hlt ?_) (hnc _ (Nat.mod_lt _ (by omega)))
      rcases hc with hc | hc
      · exact .inl (hq hc)
      · exact .inr (by rw [← hi, ← hn]; exact hc)
    · exact newK j hs
  · rw [hi]
    rcases hvd j hj with hlt | hs
    · exact VH_succ he (h3 j hlt) (hnc _ (Nat.mod_lt _ (by omega)))
    · exact newV j hs

theorem hi_triv {k : Nat} {d : Proof.Mma.D} (hq : qkS d.site = false) (hv : pvS d.site = false)
    (hk : kd d.site = 0) (hvd : vd d.site = 0) (hns : d.site ≠ .qkSkip ∧ d.site ≠ .pvSkip) :
    HI Q L X g d k := by
  refine ⟨fun h => ?_, fun j hj => ?_, fun j hj => ?_, hns⟩
  · rw [hq, hv] at h; simp at h
  · rw [hk] at hj; omega
  · rw [hvd] at hj; omega

set_option maxHeartbeats 2000000 in
/-- **A step of the MMA lane that leads its elections and receives 7 keeps its history.** -/
theorem hi_step {k : Nat} {d d' : Proof.Mma.D} {e : Event}
    (he : (X.tr g)[k]? = some e) (hd : HI Q L X g d k) (hL : MmLoop d)
    (hsh : Proof.EvW.MmShape L g d e)
    (hEL : ∀ mask inst ld, e.kind = .elect mask inst ld → ld = laneOf L g)
    (hrecv : ∀ md a b c recv ok, e.kind = .shfl md a b c recv ok → recv = b32 7)
    (hAt : AtMma Q L X g k (fun dR => dR = d))
    (hn : Proof.Mma.next L g d e = some (some d')) : HI Q L X g d' (k + 1) := by
  have hnc0 : d.site ≠ .pvCommit1 → ∀ s < 3,
      commitsTo (Proof.EvW.kvEmpty L (g / L.block) s) e = false := fun h s hs => by
    cases hq : commitsTo (Proof.EvW.kvEmpty L (g / L.block) s) e
    · rfl
    · exact absurd (mm_commit_kv hsh hs hq).1 h
  have newK : ∀ j, d.site = .qk j → KH Q L X g d.i j (k + 1) := fun j hj => by
    obtain ⟨tm, dR, P, n, hσ, rfl⟩ := hAt
    refine ⟨k, by omega, ⟨tm, dR, P, n, hσ, hj, rfl⟩, ?_⟩
    rw [cmE_succ he, hnc0 (by rw [hj]; nofun) _ (Nat.mod_lt _ (by omega))]; rfl
  have newV : ∀ j, d.site = .pv j → VH Q L X g d.i j (k + 1) := fun j hj => by
    obtain ⟨tm, dR, P, n, hσ, rfl⟩ := hAt
    refine ⟨k, by omega, ⟨tm, dR, P, n, hσ, hj, rfl⟩, ?_⟩
    rw [cmE_succ he, hnc0 (by rw [hj]; nofun) _ (Nat.mod_lt _ (by omega))]; rfl
  obtain ⟨site, i, n, tm, pro⟩ := d
  have hd0 := hd
  obtain ⟨h1, h2, h3, hs1, hs2⟩ := hd
  simp only at hs1 hs2 h1 h2 h3 newK newV hnc0
  cases site
  case qkSkip => exact absurd rfl hs1
  case pvSkip => exact absurd rfl hs2
  case setMaxReg | ldNum | finBar | finCommit | bar1 | finElect =>
    all_goals simp only [Proof.Mma.next] at hn
    all_goals (repeat' split at hn)
    all_goals first
      | (cases hn; done)
      | (simp only [Option.some.injEq] at hn
         subst hn
         exact hi_triv rfl rfl rfl rfl ⟨nofun, nofun⟩)
  case setMaxRegInc => simp [Proof.Mma.next] at hn
  case bar0 =>
    simp only [MmLoop] at hL
    simp only [Proof.Mma.next, Proof.Mma.start] at hn
    split at hn
    · simp only [Option.some.injEq] at hn
      subst hn
      split
      · exact hi_triv rfl rfl rfl rfl ⟨nofun, nofun⟩
      · refine ⟨fun h => ?_, fun j hj => ?_, fun j hj => ?_, nofun, nofun⟩
        · simp [qkS, pvS] at h hL; omega
        · simp [kd] at hj
        · simp [vd] at hj
    · cases hn
  case qkBar | qkBar2 | pvBar | pvBar2 =>
    all_goals simp only [Proof.Mma.next, Option.some.injEq] at hn
    all_goals subst hn
    all_goals
      exact hi_same he hd0 (fun h => h) rfl rfl (fun h => by simp_all [qkS])
        (fun j hj => .inl (by simp only [kd] at hj ⊢; omega))
        (fun j hj => .inl (by simp only [vd] at hj ⊢; omega))
        ⟨nofun, nofun⟩ (hnc0 nofun) (fun j h => by cases h) (fun j h => by cases h)
  case kvWait | pWait =>
    all_goals simp only [Proof.Mma.next] at hn
    all_goals split at hn
    all_goals first
      | (cases hn; done)
      | (simp only [Option.some.injEq] at hn
         subst hn
         split
         all_goals
           exact hi_same he hd0 (fun h => by simp_all [qkS, pvS]) rfl rfl
             (fun h => by simp_all [qkS]) (fun j hj => .inl (by simp only [kd] at hj ⊢; omega))
             (fun j hj => .inl (by simp only [vd] at hj ⊢; omega)) ⟨nofun, nofun⟩ (hnc0 nofun)
             (fun j h => by cases h) (fun j h => by cases h))
  case qkShfl | pvShfl =>
    all_goals simp only [Proof.Mma.next] at hn
    all_goals split at hn
    all_goals first
      | (cases hn)
      | (rename_i md a b c v ok hk
         have hv := hrecv _ _ _ _ _ _ hk
         subst hv
         simp only [Proof.Raw.word32Of_b32, show (7 : Nat) % 2 ^ 32 = 7 from rfl, ite_true,
           Option.some.injEq] at hn
         subst hn
         exact hi_same he hd0 (fun h => by simp_all [qkS, pvS]) rfl rfl
           (fun h => by simp_all [qkS]) (fun j hj => .inl (by simp only [kd] at hj ⊢; omega))
           (fun j hj => .inl (by simp only [vd] at hj ⊢; omega)) ⟨nofun, nofun⟩ (hnc0 nofun)
           (fun j h => by cases h) (fun j h => by cases h))
  case qkElect | pvElect =>
    all_goals simp only [Proof.Mma.next] at hn
    all_goals split at hn
    all_goals first
      | (cases hn; done)
      | (rename_i mk inst ld hk
         have hl := hEL _ _ _ hk
         subst hl
         simp only [ite_true, Option.some.injEq] at hn
         subst hn
         exact hi_same he hd0 (fun h => by simp_all [qkS, pvS]) rfl rfl
           (fun h => by simp_all [qkS]) (fun j hj => .inl (by simp only [kd] at hj ⊢; omega))
           (fun j hj => .inl (by simp only [vd] at hj ⊢; omega)) ⟨nofun, nofun⟩ (hnc0 nofun)
           (fun j h => by cases h) (fun j h => by cases h))
  case qk j0 =>
    simp only [Proof.Mma.next, Proof.Mma.qkNext, Option.some.injEq] at hn
    split at hn
    all_goals subst hn
    all_goals
      refine hi_same he hd0 (fun h => by simp_all [qkS, pvS]) rfl rfl
        (fun h => by simp [qkS]) (fun j hj => ?_)
        (fun j hj => .inl (by simp only [vd] at hj ⊢; omega))
        ⟨nofun, nofun⟩ (hnc0 nofun) newK newV
    all_goals simp only [kd] at hj
    all_goals rcases Nat.lt_or_ge j.val j0.val with h | h
    all_goals first
      | exact .inl (by simp only [kd]; exact h)
      | exact .inr (by simp only [Proof.Mma.Site.qk.injEq]; exact Fin.ext (by omega))
  case pv j0 =>
    simp only [Proof.Mma.next, Proof.Mma.pvNext, Option.some.injEq] at hn
    split at hn
    all_goals subst hn
    all_goals
      refine hi_same he hd0 (fun h => by simp_all [qkS, pvS]) rfl rfl
        (fun h => by simp [qkS] at h) (fun j hj => .inl (by simp only [kd] at hj ⊢; omega))
        (fun j hj => ?_) ⟨nofun, nofun⟩ (hnc0 nofun) newK newV
    all_goals simp only [vd] at hj
    all_goals rcases Nat.lt_or_ge j.val j0.val with h | h
    all_goals first
      | exact .inl (by simp only [vd]; exact h)
      | exact .inr (by simp only [Proof.Mma.Site.pv.injEq]; exact Fin.ext (by omega))
  case qkCommit =>
    simp only [MmLoop] at hL
    simp only [Proof.Mma.next, Proof.Mma.afterQk, Proof.Mma.iterNext, Option.some.injEq] at hn
    have hnc := hnc0 nofun
    have hK0 : ∀ j, KH Q L X g i j (k + 1) := fun j =>
      KH_succ he (h2 j (by simp [kd]) (.inl rfl)) (hnc _ (Nat.mod_lt _ (by omega)))
    split at hn
    · rename_i hi0
      subst hn hi0
      refine ⟨fun _ j => ?_, fun j hj hc => ?_, fun j hj => ?_, ?_, ?_⟩
      · exact hK0 j
      · dsimp only at hj hc ⊢
        by_cases h0 : 0 = n <;> by_cases h1 : 1 < n
        all_goals simp [h0, h1, kd, qkS] at hj hc
        all_goals omega
      · dsimp only at hj; split at hj <;> [simp [vd] at hj; (split at hj <;> simp [vd] at hj)]
      · dsimp only; split <;> [nofun; (split <;> nofun)]
      · dsimp only; split <;> [nofun; (split <;> nofun)]
    · subst hn
      refine ⟨fun _ j => h1 (.inl ⟨rfl, by omega⟩) j |> fun h => KH_succ he h
          (hnc _ (Nat.mod_lt _ (by omega))), fun j hj hc => hK0 j,
        fun j hj => by simp [vd] at hj, nofun, nofun⟩
  case pvCommit1 =>
    simp only [MmLoop] at hL
    simp only [Proof.Mma.next, Option.some.injEq] at hn
    subst hn
    refine ⟨fun h => by simp [qkS, pvS] at h, fun j hj hc => ?_, fun j hj => by simp [vd] at hj,
      nofun, nofun⟩
    refine KH_succ he (h2 j (by simp [kd]) hc) ?_
    cases hq : commitsTo (Proof.EvW.kvEmpty L (g / L.block) (i % 3)) e
    · rfl
    · have := (mm_commit_kv hsh (Nat.mod_lt _ (by omega)) hq).2
      simp only at this
      omega
  case pvCommit2 =>
    simp only [MmLoop] at hL
    simp only [Proof.Mma.next, Proof.Mma.iterNext, Option.some.injEq] at hn
    have hnc := hnc0 nofun
    subst hn
    have hK : i < n → ∀ j, KH Q L X g i j (k + 1) := fun hlt j =>
      KH_succ he (h2 j (by simp [kd]) (.inr hlt)) (hnc _ (Nat.mod_lt _ (by omega)))
    refine ⟨fun h j => ?_, fun j hj hc => ?_, fun j hj => ?_, ?_, ?_⟩
    · dsimp only at h ⊢
      split at h
      · simp [qkS, pvS] at h
      · rename_i hne
        simp only [Nat.add_sub_cancel]
        exact hK (by omega) j
    · dsimp only at hj hc ⊢
      by_cases h0 : i = n <;> by_cases h1 : i + 1 < n
      all_goals simp [h0, h1, kd, qkS] at hj hc
    · dsimp only at hj; split at hj <;> [simp [vd] at hj; (split at hj <;> simp [vd] at hj)]
    · dsimp only; split <;> [nofun; (split <;> nofun)]
    · dsimp only; split <;> [nofun; (split <;> nofun)]

/-- The history at the thread machine's MMA states. -/
def HIt (Q : Params) (L : Launch) (X : Execution) (g : Nat) : (thread Q L g).D → Nat → Prop
  | (.inr ⟨.inl (.worker _), .mma d _⟩, _), k => HI Q L X g d k
  | _, _ => True

/-- **The history along the MMA lane** (a thread that leads its elections). -/
theorem hi_inv (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hg : g < L.threads) (hEL : ElectLead L g (X.tr g)) :
    ∀ k, k < (X.tr g).length → ∀ σ, Frame.stateAt (thread Q L) X g k = some (some σ) →
      HIt Q L X g σ k := by
  intro k
  induction k with
  | zero =>
    intro _ σ hσ
    rw [Frame.stateAt_zero, thread_init_eq] at hσ
    obtain rfl := Option.some.inj (Option.some.inj hσ)
    trivial
  | succ k ih =>
    intro hk σ' hσ'0
    have hlt : k < (X.tr g).length := by omega
    obtain ⟨e, he⟩ : ∃ e, (X.tr g)[k]? = some e := ⟨_, List.getElem?_eq_getElem hlt⟩
    have hσ' := hσ'0
    rw [Frame.stateAt_succ he] at hσ'
    have hF := good_all' hp hX hg k
    rcases hk0 : Frame.stateAt (thread Q L) X g k with _ | _ | σ
    · rw [hk0] at hσ'; cases hσ'
    · exact absurd hk0 hF.1
    · rw [hk0] at hσ'
      have hn : (thread Q L g).next σ e = some (some σ') := hσ'
      have hJ := hF.2 σ hk0
      have hR0 := ih hlt σ hk0
      obtain ⟨t, ins, o, hat, hi, hc, hf⟩ :=
        Frame.fired_site (fun g hg => thread_sound hp hg) hX he hk0
      have hnE : ¬ Ends e := not_ends_of_lt hX hg he hk
      have hget : X.get (g, k) = some e := he
      obtain ⟨x, n⟩ := σ
      rcases x with st | ⟨_ | r, d⟩
      · rw [next_start] at hn
        obtain ⟨s', -, rfl⟩ := mm_some hn
        simp only [Code.enter]
        split
        · rename_i j _
          rcases j with (_ | _) | _ <;> trivial
        · trivial
      · rename_i i
        obtain ⟨d', hd'⟩ := next_same_role hn
        obtain ⟨x', n'⟩ := σ'
        simp only at hd'
        subst hd'
        cases i with
        | dp tm bw => trivial
        | worker w =>
          rw [next_worker] at hn
          obtain ⟨σw', hσw, he'⟩ := mm_some hn
          simp only [Prod.mk.injEq, Sum.inr.injEq, heq_eq_eq, Sigma.mk.injEq, true_and] at he'
          obtain ⟨he1, -⟩ := he'
          subst he1
          cases σw' with
          | mma d' P' =>
            rcases w_next_mma' hσw with hst | ⟨dm, rfl, hmn⟩
            · exact hi_triv (by rw [hst]; rfl) (by rw [hst]; rfl) (by rw [hst]; rfl)
                (by rw [hst]; rfl) (by rw [hst]; exact ⟨nofun, nofun⟩)
            · cases o with
              | none => exact absurd (fires_none_ends hf) hnE
              | some u =>
              have hsh : Proof.EvW.MmShape L g dm e := frag_ev hp hg hJ hat hi hc hf
              obtain ⟨-, hL, -⟩ := (sh_inv hp hX hg k hlt _ hk0 : _ = 1 + mmSh dm ∧ MmLoop dm ∧ _)
              refine hi_step he (hR0 : HI Q L X g dm k) hL hsh
                (fun mask inst ld hk' => hEL e (List.mem_of_getElem? he) mask inst ld hk')
                (fun md a b c recv ok hk' => ?_) ⟨w, dm, P', n, hk0, rfl⟩ hmn
              obtain ⟨pc, kd⟩ := e
              simp only at hk'
              subst hk'
              exact mma_recv7 hp hX hget hk0
          | _ => trivial
      · exact hJ.elim

/-- **A commit to `kv_empty` is the MMA lane's PV half's first commit**, at an MMA state. -/
theorem commit_kv_state (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    {jc pc : Nat} {sp : TcCommit.Spec} (he : X.get (g, jc) = some ⟨pc, .tc (.commit sp)⟩)
    {s : Nat} (hs : s < 3) (hm : sp.mbar = Proof.EvW.kvEmpty L (g / L.block) s) :
    ∃ tm d P n, Frame.stateAt (thread Q L) X g jc =
      some (some (.inr ⟨.inl (.worker tm), .mma d P⟩, n)) ∧ d.site = .pvCommit1 ∧
      s = (d.i - 1) % 3 := by
  have hg := Frame.lt_of_get hX he
  obtain ⟨σ, t, ins, o, hσ, hJ, hat, hi, hc, hf⟩ := ev_state hp hX he (fun f h => by cases h)
  cases o with
  | none => exact absurd (fires_none_ends hf) (by simp [Ends])
  | some u =>
  have hpc := commit_pc hc hf rfl
  have hev := frag_ev hp hg hJ hat hi hc hf
  have hct : commitsTo (Proof.EvW.kvEmpty L (g / L.block) s) ⟨pc, .tc (.commit sp)⟩ = true := by
    simp [commitsTo, hm]
  obtain ⟨x, n⟩ := σ
  rcases x with st | ⟨_ | r, d⟩
  · exact (startup_commit st.site hpc).elim
  · rename_i i
    cases i with
    | dp tm bw =>
      exfalso
      rcases d with d | ⟨_ | _, τ⟩
      · exact proA_commit d.site hpc
      · cases τ with
        | sm d => exact sm_commit d.site hpc
        | epi d => exact epi_commit d.site hpc
      · exact hJ.elim
    | worker w =>
      cases d with
      | mma d P =>
        obtain ⟨h1, h2⟩ := mm_commit_kv (hev : Proof.EvW.MmShape L g d _) hs hct
        exact ⟨w, d, P, n, hσ, h1, h2⟩
      | worker w => exact (worker_commit w.site hpc).elim
      | idle d => exact (idle_commit d.site hpc).elim
      | loader d P => exact (loader_commit d.site hpc).elim
      | exit x => exact (exitsite_commit x.site hpc).elim
  · exact hJ.elim

/-- The MMA event at a state with the history's site, and its operand. -/
theorem mma_at (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X) {kR jc : Nat}
    (hkR : kR < jc) (hjc : jc < (X.tr g).length) {p : Proof.Mma.D → Prop}
    (hA : AtMma Q L X g kR p) :
    ∃ dR e, p dR ∧ X.get (g, kR) = some e ∧ Proof.EvW.MmShape L g dR e ∧
      ∃ tm P n, Frame.stateAt (thread Q L) X g kR =
        some (some (.inr ⟨.inl (.worker tm), .mma dR P⟩, n)) := by
  obtain ⟨tm, dR, P, n, hσ, hpd⟩ := hA
  have hg : g < L.threads := thread_lt_of_len hX hjc
  obtain ⟨e, he⟩ : ∃ e, X.get (g, kR) = some e :=
    ⟨_, List.getElem?_eq_getElem (show kR < (X.tr g).length by omega)⟩
  have hnE : ¬ Ends e := not_ends_of_lt hX hg he (by omega)
  obtain ⟨t, ins, o, hat, hi, hc, hf⟩ :=
    Frame.fired_site (fun g hg => thread_sound hp hg) hX he hσ
  cases o with
  | none => exact absurd (fires_none_ends hf) hnE
  | some u =>
  have hJ := (good_all' hp hX hg kR).2 _ hσ
  exact ⟨dR, e, hpd, he, frag_ev hp hg hJ hat hi hc hf, tm, P, n, hσ⟩

set_option maxHeartbeats 1000000 in
/-- **The MMA lane's reads of a released use cover its slot** (the premise `hcover` of
`SingleTmaRing.copies_chain` for slot `s` of CTA `c`, at byte `l`). -/
theorem hcover (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X) {c : Nat}
    (hc : c < L.grid) {s : Nat} (hs : s < 3) {l : Loc} (hsp : l.space = .shared)
    (hlc : l.cta = c) (hl : InSlot L s l.addr) (u : Nat) :
    ∀ jc pc sp, X.get (leadT L X c 7, jc) = some ⟨pc, .tc (.commit sp)⟩ →
      sp.mbar = Proof.EvW.kvEmpty L c s →
      ((X.tr (leadT L X c 7)).take jc).countP (commitsTo (Proof.EvW.kvEmpty L c s)) = u →
      ∃ kR isB idx, X.TcAsync (leadT L X c 7, kR) ∧
        ((X.tr (leadT L X c 7)).take kR).countP (commitsTo (Proof.EvW.kvEmpty L c s)) = u ∧
        u + 1 ≤ okPolls (Proof.EvW.kvReady L c s) ((X.tr (leadT L X c 7)).take kR) ∧
        AsyncCovers X (leadT L X c 7, kR) (.mmaRead isB idx) l ∧
        ∀ w ws, AsyncObserved X (leadT L X c 7, kR) .mmaDone w true ws →
          X.AsyncPresent (leadT L X c 7, kR) (.mmaRead isB idx) := by
  have hb : L.block = 256 := hp.block
  have hE := Proof.EvW.mmEnv_of_pre hp
  have hal := hE.align
  obtain ⟨hcc, hct, hcw⟩ := leadT_cta (X := X) hc (w := 7) (by omega) hb
  set cm := leadT L X c 7 with hcm
  intro jc pc sp hget hm hu
  have hjc : jc < (X.tr cm).length := (List.getElem?_eq_some_iff.mp hget).1
  rw [← hcc] at hm
  obtain ⟨tm, d, P, n, hσ, hsite, hsd⟩ := commit_kv_state hp hX hget hs hm
  -- the lane leads its elections
  have hEL : ElectLead L cm (X.tr cm) := by
    have hel := mm_pv_elected hp hX hct jc hjc.le _ hσ
      (by show isPvS d.site = true; rw [hsite]; rfl)
    exact Proof.Interface.electLead_of_elected hX hel
  have hH : HI Q L X cm d jc := hi_inv hp hX hct hEL jc hjc _ hσ
  obtain ⟨h1, -, h3, -⟩ := hH
  have hK := h1 (.inr (by rw [hsite]; rfl))
  have hV := h3
  rw [hsite] at hV
  simp only [vd] at hV
  -- the read and its facts, from a history position
  have key : ∀ (kR : Nat) (dR : Proof.Mma.D) (e : Event), kR < jc → X.get (cm, kR) = some e →
      Proof.EvW.MmShape L cm dR e → (∃ tm P n, Frame.stateAt (thread Q L) X cm kR =
        some (some (.inr ⟨.inl (.worker tm), .mma dR P⟩, n))) →
      cmE L X cm s kR = cmE L X cm s jc →
      (∃ (pc' dst : Nat) (sp' : TcMma.OperandSpec) (acc : Bool) (mask : List Nat) (idx : Nat),
        e = ⟨pc', .tc (.mma dst sp' acc mask)⟩ ∧ sp'.byteLoc .b idx = some l) →
      ∃ kR isB idx, X.TcAsync (cm, kR) ∧
        ((X.tr cm).take kR).countP (commitsTo (Proof.EvW.kvEmpty L c s)) = u ∧
        u + 1 ≤ okPolls (Proof.EvW.kvReady L c s) ((X.tr cm).take kR) ∧
        AsyncCovers X (cm, kR) (.mmaRead isB idx) l ∧
        ∀ w ws, AsyncObserved X (cm, kR) .mmaDone w true ws →
          X.AsyncPresent (cm, kR) (.mmaRead isB idx) := by
    intro kR dR e hkR he hsh _ hcnt ⟨pc', dst, sp', acc, mask, idx, hev, hbl⟩
    subst hev
    have hMI : X.MmaIssue (cm, kR) dst sp' acc mask := ⟨pc', he⟩
    have hbl' : sp'.byteLoc (if true then .b else .a) idx = some l := by simpa using hbl
    have hcov := Proof.Ring.Cover.covers_of_byteLoc hMI hbl'
    have hcnt' : ((X.tr cm).take kR).countP (commitsTo (Proof.EvW.kvEmpty L c s)) = u := by
      have : cmE L X cm s kR = cmE L X cm s jc := hcnt
      simp only [cmE, hcc] at this
      rw [this, ← hu]
    obtain ⟨s', hs', -, -, -, hsl', hTc, hpol⟩ := mma_read_info hp hX hcov hsp (by
      unfold InSlot at hl; omega)
    obtain rfl := inSlot_unique hs hs' hl hsl'
    rw [hcc] at hpol
    exact ⟨kR, true, idx, hTc, hcnt', by omega, hcov,
      fun w ws hob => observed_mmaRead hX hMI hbl' hob⟩
  unfold InSlot at hl
  rcases hl with ⟨hlo, hhi⟩ | ⟨hlo, hhi⟩
  · -- a byte of the K tile: a QK MMA of iteration `i - 1`
    obtain ⟨j, idx, hcv⟩ := Proof.Ring.Cover.k_cover (B := L.sharedBase + 32768 * s)
      (a := l.addr - (L.sharedBase + 32768 * s)) (by omega) (by omega)
    obtain ⟨kR, hkR, hA, hcnt⟩ := hK j
    obtain ⟨dR, e, ⟨hsR, hiR⟩, he, hsh, hst⟩ := mma_at hp hX hkR hjc hA
    refine key kR dR e hkR he hsh hst (by rw [hsd]; exact hcnt) ?_
    obtain ⟨pc', dst, sp', acc, mask, hev, hD, hlow, hbs⟩ := Proof.Ring.Cover.qk_spec hp hsR hsh
    refine ⟨pc', dst, sp', acc, mask, idx, hev, ?_⟩
    have := hcv sp' hD (by rw [hbs, hiR, ← hsd])
    rw [this, hlow, hcc]
    rcases l with ⟨ls, lc, la⟩
    simp only at hsp hlc hlo hhi ⊢
    subst hsp hlc
    congr 2
    omega
  · -- a byte of the V tile: a PV MMA of iteration `i`
    obtain ⟨j, idx, hcv⟩ := Proof.Ring.Cover.v_cover (B := L.sharedBase + 98304 + 32768 * s)
      (a := l.addr - (L.sharedBase + 98304 + 32768 * s)) (by omega) (by omega)
    obtain ⟨kR, hkR, hA, hcnt⟩ := hV j (by omega)
    obtain ⟨dR, e, ⟨hsR, hiR⟩, he, hsh, hst⟩ := mma_at hp hX hkR hjc hA
    refine key kR dR e hkR he hsh hst (by rw [hsd]; exact hcnt) ?_
    obtain ⟨pc', dst, sp', acc, mask, hev, hD, hlow, hbs⟩ := Proof.Ring.Cover.pv_spec hp hsR hsh
    refine ⟨pc', dst, sp', acc, mask, idx, hev, ?_⟩
    have := hcv sp' hD (by rw [hbs, hiR, ← hsd])
    rw [this, hlow, hcc]
    rcases l with ⟨ls, lc, la⟩
    simp only at hsp hlc hlo hhi ⊢
    subst hsp hlc
    congr 2
    omega

/-! ### The kv region -/

/-- **No thread access covers a byte of the rings above the base word.** -/
theorem thread_notKv (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X) {k : Nat}
    {c : Acc} {v : Bool} {l : Loc} (hI : X.Access (g, k) c v) (hc : c.Covers l)
    (hl : Proof.Safety.InKv L l) : False := by
  obtain ⟨hsp, hlo, hhi⟩ := hl
  have hsr := hp.sharedRange
  unfold sharedBytes at hsr
  have hsa : c.loc.space = .shared := hc.1.symm.trans hsp
  obtain ⟨-, -, hca, hcb⟩ := hc
  rcases hI with ⟨bs, ⟨pc, he⟩, rfl⟩ | ⟨bs, ⟨pc, he⟩, rfl⟩ | ⟨old, new, pc, he⟩
  · cases rd_class hp hX he hsa with
    | base h hz => simp only [h, hz] at hca hcb; omega
    | role h4 _ h hz => simp only [h, hz] at hca hcb; omega
    | pair _ _ hz h => rcases h with h | h <;> omega
    | scratch h hz => simp only [h, hz] at hca hcb; omega
  · cases wr_class hp hX he hsa with
    | base _ => simp only at hca hcb; omega
    | qtile _ _ hz h1 _ => omega
    | role _ _ =>
      simp only [Proof.EvD.wordAcc] at hca hcb
      rw [Nat.mod_eq_of_lt (by omega)] at hca
      omega
    | pair _ _ hz h =>
      rw [Nat.mod_eq_of_lt (by omega)] at h
      rcases h with h | h <;> omega
    | scratch => simp only [Proof.EvD.wordAcc] at hca hcb; omega
  · exact absurd he (no_rmw hX)

/-- **Two copies' writes of one ring byte in two uses of its slot are ordered** (through the MMA
lane's read of the byte in the earlier use, `SingleTmaRing.copies_chain` with `hcover`). -/
theorem copies_diff_ordered (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    {g1 k1 g2 k2 x y z x' y' z' : Nat} {l : Loc}
    (hca : AsyncCovers X (g1, k1) (.write (.load x y z)) l)
    (hcb : AsyncCovers X (g2, k2) (.write (.load x' y' z')) l) (hsp : l.space = .shared) :
    ∃ c s, ∃ hs : s < 3, g1 / L.block = c ∧ g2 / L.block = c ∧ InSlot L s l.addr ∧
      (SingleTmaRing.copyUse X ((kvDecl Q L X c).slot ⟨s, hs⟩) (g1, k1) <
          SingleTmaRing.copyUse X ((kvDecl Q L X c).slot ⟨s, hs⟩) (g2, k2) →
        AsyncChain L X l ((g1, k1), .write (.load x y z)) ((g2, k2), .write (.load x' y' z'))) := by
  obtain ⟨pc1, a1, sp1, he1, hl1⟩ := copy_write_at hca
  obtain ⟨pc2, a2, sp2, he2, hl2⟩ := copy_write_at hcb
  obtain ⟨⟨-, s1, hs1, hm1, hreg1, -⟩, -⟩ := copy_ring_ev hp hX he1
  obtain ⟨⟨-, s2, hs2, hm2, hreg2, -⟩, -⟩ := copy_ring_ev hp hX he2
  obtain ⟨-, hc1, hsl1⟩ := hreg1 x y z l hl1
  obtain ⟨-, hc2, hsl2⟩ := hreg2 x' y' z' l hl2
  obtain rfl := inSlot_unique hs1 hs2 hsl1 hsl2
  have hg1 := Frame.lt_of_get hX he1
  set c := g1 / L.block with hcdef
  have hc12 : g2 / L.block = c := by rw [← hc2, hc1]
  rw [hc12] at hm2
  have hcg : c < L.grid := NamedBar.cta_lt hg1
  refine ⟨c, s1, hs1, rfl, hc12, hsl1, fun hlt => ?_⟩
  have H := kv_hyp hp hX hcg ⟨s1, hs1⟩
  exact SingleTmaRing.copies_chain hX H (kv_fits c ⟨s1, hs1⟩) he1 hm1 he2 hm2 hlt hca hcb
    (hcover hp hX hcg hs1 hsp (by rw [← hc1]) hsl1 _)

end
end PTX.Kernels.InklingRelDecode.Proof2
