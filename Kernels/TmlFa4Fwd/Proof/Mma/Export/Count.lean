-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Lib.Export
public import Kernels.TmlFa4Fwd.Proof.Epilogue.Ideal
public import Kernels.TmlFa4Fwd.Proof.Mma.Places
public import Lemmas.Flow.NotCommit
public import Lemmas.Order.ElectOrdinal
import Kernels.TmlFa4Fwd.Proof.Common.Frame
import Kernels.TmlFa4Fwd.Proof.Mma.Export.CommitTarget
import Kernels.TmlFa4Fwd.Proof.Mma.Counts
import Kernels.TmlFa4Fwd.Proof.Mma.Export.Coll
import Kernels.TmlFa4Fwd.Proof.Mma.Export.Mbar
import Kernels.TmlFa4Fwd.Proof.Mma.Export.MbarSite
import Kernels.TmlFa4Fwd.Proof.Startup.Export.MbarSite
import Lemmas.Flow.NthEv
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The MMA warp's commits and its polls

The commit of S-full (80, 88) with `t` earlier ones follows an election of its lane at which every
lane of the warp, at its election of that ordinal, has polled the stage's P barriers `t` times; the
commit of final O (144, 152) one at which every lane has polled the stage's P-full once more than
the tile's rescale rounds (`mma_s_commit`, `mma_o_commit`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.TmlFa4Fwd.Proof.Mma (RefQ electAll pq acqAt commitAt)

noncomputable section
set_option maxRecDepth 100000

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {h k : Nat} {e : Event} {l : Loc}

/-- The rounds' values of the tile the first pass picked. -/
def mmaRef (p : Params) (L : Launch) (g R : Nat) (bal : BitVec 64) : Mma.V :=
  let c := Epilogue.chosenD p (g / L.block) R bal
  { sc := { c with c0 := Epilogue.qv p (Epilogue.chosen c),
                   c1 := Epilogue.qv p (Epilogue.addi (Epilogue.chosen c) 1) },
    ukw := Mma.ukv p (Epilogue.chosen c) }

/-- **The MMA lane's tile has `R` loop rounds.** -/
def MmaRounds (p : Params) (L : Launch) (g R : Nat) : Prop :=
  ∃ r bal, Epilogue.Picked p L g r bal ∧ (Mma.Bs p L g (mmaRef p L g r bal)).toNat - 1 = R

theorem MmaRounds.unique {R R' : Nat} (h1 : MmaRounds p L h R) (h2 : MmaRounds p L h R') :
    R = R' := by
  obtain ⟨r, bal, hP, rfl⟩ := h1
  obtain ⟨r', bal', hP', rfl⟩ := h2
  obtain ⟨rfl, rfl⟩ := hP.unique hP'
  rfl

theorem MmaRounds.cta {g R : Nat} (hc : h / L.block = g / L.block) (h1 : MmaRounds p L h R) :
    MmaRounds p L g R := by
  obtain ⟨r, bal, hP, rfl⟩ := h1
  refine ⟨r, bal, ?_, ?_⟩
  · simp only [Epilogue.Picked, hc] at hP ⊢
    exact hP
  · simp only [Mma.Bs, Mma.blocks, Mma.coords, mmaRef, Epilogue.chosenD, Epilogue.ctaW, hc]

/-- The places of the elections. -/
private def elQ : List Nat :=
  [5, 7, 11, 13, 15, 25, 31, 33, 38, 42, 44, 46, 48, 60, 62, 69, 76, 80, 82, 84]

/-- The elections before each election place in round 0. -/
private def elN : Nat → Nat
  | 5 => 0 | 7 => 1 | 11 => 2 | 13 => 3 | 15 => 4 | 25 => 5 | 31 => 6 | 33 => 7 | 38 => 8
  | 42 => 9 | 44 => 10 | 46 => 11 | 48 => 12 | 60 => 5 | 62 => 6 | 69 => 7 | 76 => 8 | 80 => 9
  | 82 => 10 | 84 => 11 | _ => 0

private theorem elN_tab : ∀ q ∈ elQ, electAll q 0 = elN q := by decide

private theorem electAll_lin' (q r : Nat) : electAll q r = electAll q 0 + 8 * r := by
  induction r with
  | zero => rfl
  | succ r ih => rw [electAll_succ, ih]; omega

/-- A place and round of a tile of `R` rounds. -/
private def RoundOk (q r R : Nat) : Prop :=
  (q < 20 → r = 0) ∧ (20 ≤ q ∧ q < 60 → r < R) ∧ (60 ≤ q ∧ q < 100 → r = R)

/-- **Elections of one ordinal are at one place and round.** -/
private theorem place_eq {q q' r r' R : Nat} (hq : q ∈ elQ) (hq' : q' ∈ elQ)
    (h1 : RoundOk q r R) (h2 : RoundOk q' r' R) (h : electAll q r = electAll q' r') :
    q = q' ∧ r = r' := by
  rw [electAll_lin' q, electAll_lin' q', elN_tab q hq, elN_tab q' hq'] at h
  obtain ⟨a1, a2, a3⟩ := h1
  obtain ⟨b1, b2, b3⟩ := h2
  have hlt : ∀ q ∈ elQ, (q < 20 ∧ elN q < 5) ∨ (20 ≤ q ∧ q < 60 ∧ 5 ≤ elN q ∧ elN q ≤ 12) ∨
      (60 ≤ q ∧ q < 100 ∧ 5 ≤ elN q ∧ elN q ≤ 11) := by decide
  have hinj : ∀ q ∈ elQ, ∀ q' ∈ elQ, elN q = elN q' →
      ((q < 20 ∧ q' < 20) ∨ (20 ≤ q ∧ q < 60 ∧ 20 ≤ q' ∧ q' < 60) ∨ (60 ≤ q ∧ 60 ≤ q')) →
        q = q' := by decide
  have key : r = r' ∧ elN q = elN q' ∧
      ((q < 20 ∧ q' < 20) ∨ (20 ≤ q ∧ q < 60 ∧ 20 ≤ q' ∧ q' < 60) ∨ (60 ≤ q ∧ 60 ≤ q')) := by
    rcases hlt q hq with ⟨c1, c2⟩ | ⟨c1, c2, c3, c4⟩ | ⟨c1, c2, c3, c4⟩ <;>
      rcases hlt q' hq' with ⟨d1, d2⟩ | ⟨d1, d2, d3, d4⟩ | ⟨d1, d2, d3, d4⟩
    · have := a1 c1; have := b1 d1; omega
    · have := a1 c1; omega
    · have := a1 c1; omega
    · have := b1 d1; omega
    · have := a2 ⟨c1, c2⟩; have := b2 ⟨d1, d2⟩; omega
    · have := a2 ⟨c1, c2⟩; have := b3 ⟨d1, d2⟩; omega
    · have := b1 d1; omega
    · have := a3 ⟨c1, c2⟩; have := b2 ⟨d1, d2⟩; omega
    · have := a3 ⟨c1, c2⟩; have := b3 ⟨d1, d2⟩; omega
  exact ⟨hinj q hq q' hq' key.2.1 key.2.2, key.1⟩

/-- The rounds of a pipeline state. -/
private theorem roundOk {d : Mma.D} {n : Cls → Nat} {r : Nat} {w : Bool}
    (hQ : RefQ p L h d.site.ord d.v (Mma.rc n) r w) (hF : Mma.MFits p L h d (n .shfl) (n .vote))
    (hpipe : d.site.pipe = true) : ∃ R, MmaRounds p L h R ∧ RoundOk d.site.ord r R := by
  obtain ⟨R, bal, hC, hB⟩ := Mma.bs_ref (Mma.pmid_of hpipe) hF
  refine ⟨_, ⟨R, bal, hC.1, rfl⟩, hQ.pre, fun hq => ?_, fun hq => ?_⟩
  · have h1 := (hQ.loop hq).1
    rw [hB] at h1
    change (r : Int) + 1 < Mma.Bs p L h (mmaRef p L h R bal) at h1
    omega
  · have h1 := hQ.tail hq
    rw [hB] at h1
    change (r : Int) + 1 = Mma.Bs p L h (mmaRef p L h R bal) ∨
      (r = 0 ∧ Mma.Bs p L h (mmaRef p L h R bal) < 2) at h1
    omega

section
variable (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow p L X)
include hp hX hFw

/-- **An election of an MMA lane**: its place and round, with the lane's counts. -/
private theorem elect_state (hw : Prologue.warpIndex L h = 12) {pc mask inst ld : Nat}
    (he : X.get (h, k) = some ⟨pc, .elect mask inst ld⟩) :
    ∃ q r R, q ∈ elQ ∧ MmaRounds p L h R ∧ RoundOk q r R ∧
      ((X.tr h).take k).countP isElectEv = electAll q r ∧
      ∀ o, okPolls (obj L h o) ((X.tr h).take k) = acqAt q r o := by
  rcases mma_counts hp hX hFw hw he (fun f h => by cases h) with ⟨s, n, hS, hev, hx⟩ | hev |
    ⟨d, n, r, w, hσ, hQ, hcm, hF, hev⟩
  · exfalso
    obtain ⟨-, -, -, -, hk⟩ := start_kind (g := h) hS hev
    have hm := elect_full hX (show X.Elect (h, k) pc mask inst ld from he)
    by_cases hl : ld = laneOf L h
    · rcases hk (.mma .won) (by simp [cls, Mma.cls, hm, hl]) with h1 | h1 | h1 <;> cases h1
    · rcases hk (.mma .lost) (by simp [cls, Mma.cls, hm, hl]) with h1 | h1 | h1 <;> cases h1
  · rcases hev with ⟨_, _, _, hk⟩ | ⟨_, _, _, hk⟩ | ⟨_, _, hk⟩ | ⟨_, hk⟩ <;> cases hk
  · obtain ⟨hpipe, hs⟩ := mma_elect_site hev rfl
    obtain ⟨R, hR, hok⟩ := roundOk hQ hF hpipe
    have hq : d.site.ord ∈ elQ := by
      rcases hs with ⟨b, hs⟩ | ⟨b, hs⟩ | ⟨b, hs⟩ <;> rw [hs] <;> clear hs <;> revert b <;> decide
    refine ⟨_, r, R, hq, hR, hok, mma_elections hX hσ hQ, fun o => ?_⟩
    rw [mma_okPolls, count hσ]
    exact hQ.acq o

/-- **The election before a commit** and the counts of every lane of the warp at its election of
that ordinal. -/
private theorem commit_elect (hw : Prologue.warpIndex L h = 12) {pc o : Nat} {s : TcCommit.Spec}
    (he : X.get (h, k) = some ⟨pc, .tc (.commit s)⟩) (hs : s.mbar = obj L h o) :
    ∃ c r R, o = Mma.cmO r c ∧ MmaRounds p L h R ∧ RoundOk (Mma.Site.cm c).ord r R ∧
      ((X.tr h).take k).countP (commitsTo (obj L h o)) = commitAt (Mma.Site.cm c).ord r o ∧
      ∃ j pce mask inst ld, j < k ∧ X.get (h, j) = some ⟨pce, .elect mask inst ld⟩ ∧
        ∀ g, SameWarp L h g → ∀ i pci maski insti ldi,
          X.get (g, i) = some ⟨pci, .elect maski insti ldi⟩ →
          ((X.tr g).take i).countP isElectEv = ((X.tr h).take j).countP isElectEv →
          ∀ o', okPolls (obj L g o') ((X.tr g).take i) = acqAt (Mma.Site.ce c).ord r o' := by
  rcases mma_counts hp hX hFw hw he (fun f h => by cases h) with ⟨s', n, hS, hev, hx⟩ | hev |
    ⟨d, n, r, w, hσ, hQ, hcm, hF, hev⟩
  · exfalso
    obtain ⟨-, -, -, -, hk⟩ := start_kind (g := h) hS hev
    rcases hk (.mma (.commit s.mbar)) (by simp [cls, Mma.cls]) with h1 | h1 | h1 <;> cases h1
  · rcases hev with ⟨_, _, _, hk⟩ | ⟨_, _, _, hk⟩ | ⟨_, _, hk⟩ | ⟨_, hk⟩ <;> cases hk
  obtain ⟨c, hc, hb⟩ := mma_commit_site hev rfl
  have hw1 : w = true := hcm (by rw [hc]; clear hc hb; revert c; decide)
  subst hw1
  have hmb : s.mbar = obj L h (Mma.cmO r c) :=
    hb.trans (Mma.cm_loc hp c (r := r) (fun hc' => hQ.regs (by
      rw [hc]; fin_cases c <;> simp_all [Mma.Site.ord])))
  have ho : o = Mma.cmO r c := obj_inj (hs.symm.trans hmb)
  obtain ⟨R, hR, hok⟩ := roundOk hQ hF (by rw [hc]; rfl)
  have hcom : ((X.tr h).take k).countP (commitsTo (obj L h o)) = commitAt d.site.ord r o := by
    rw [mma_commits, count hσ]
    exact hQ.com o
  -- the lane's election before the commit
  have hord : ∀ c : Fin 12, electAll (Mma.Site.cm c).ord 0 = electAll (Mma.Site.ce c).ord 0 + 1 ∧
      (Mma.Site.ce c).ord ∈ elQ ∧ ((Mma.Site.cm c).ord < 20 ↔ (Mma.Site.ce c).ord < 20) ∧
      (20 ≤ (Mma.Site.cm c).ord ∧ (Mma.Site.cm c).ord < 60 ↔
        20 ≤ (Mma.Site.ce c).ord ∧ (Mma.Site.ce c).ord < 60) ∧
      (60 ≤ (Mma.Site.cm c).ord ∧ (Mma.Site.cm c).ord < 100 ↔
        60 ≤ (Mma.Site.ce c).ord ∧ (Mma.Site.ce c).ord < 100) := by decide
  obtain ⟨o1, o2, o3, o4, o5⟩ := hord c
  have hwon : ((X.tr h).take k).countP (cls L h (.mma .won)) =
      electAll (Mma.Site.ce c).ord r + 1 := by
    rw [count hσ]
    have h1 := hQ.won
    simp only [ite_true] at h1
    change n (.mma .won) = _ at h1
    rw [h1, hc, electAll_lin' (Mma.Site.cm c).ord, electAll_lin' (Mma.Site.ce c).ord]
    omega
  have hlost : ((X.tr h).take k).countP (cls L h (.mma .lost)) = 0 := by
    rw [count hσ]
    exact hQ.lost
  obtain ⟨j, ev, hj, hget, hp', hcj⟩ := exists_nthEv (X := X) (g := h) (k := k)
    (p := cls L h (.mma .won)) (n := electAll (Mma.Site.ce c).ord r) (by omega)
  obtain ⟨pce, kd⟩ := ev
  cases kd <;> simp [cls, Mma.cls] at hp'
  rename_i mask inst ld
  have hel : elections X h j = electAll (Mma.Site.ce c).ord r := by
    have hl0 : ((X.tr h).take j).countP (cls L h (.mma .lost)) = 0 := by
      have := (List.take_sublist_take_left (l := X.tr h) hj.le).countP_le
        (p := cls L h (.mma .lost))
      omega
    rw [elect_split hX j]
    change ((X.tr h).take j).countP (cls L h (.mma .won)) +
      ((X.tr h).take j).countP (cls L h (.mma .lost)) = _
    omega
  rw [hc] at hcom hok
  refine ⟨c, r, R, ho, hR, hok, hcom, j, pce, mask, inst, ld, hj, hget, ?_⟩
  intro g hwg i pci maski insti ldi hgi hcnt o'
  have hg12 : Prologue.warpIndex L g = 12 := by
    have h1 : h % L.block / 32 = g % L.block / 32 := hwg.2
    simp only [Prologue.warpIndex] at hw ⊢
    omega
  obtain ⟨q, r', R', hq, hR', hok', hcnt', hpolls⟩ := elect_state hp hX hFw hg12 hgi
  have hRR : R' = R := (MmaRounds.cta hwg.1.2.2.symm hR').unique hR
  subst hRR
  have hoke : RoundOk (Mma.Site.ce c).ord r R' := by
    obtain ⟨a1, a2, a3⟩ := hok
    exact ⟨fun x => a1 (o3.mpr x), fun x => a2 (o4.mpr x), fun x => a3 (o5.mpr x)⟩
  obtain ⟨rfl, rfl⟩ := place_eq hq o2 hok' hoke (by
    rw [← hcnt', hcnt]; exact hel)
  exact hpolls o'

/-- **The commit of S-full with `t` earlier ones** follows an election of its lane at which every
lane of the warp has polled both P barriers of the stage `t` times. -/
theorem mma_s_commit (q : Fin 2) (hw : Prologue.warpIndex L h = 12) {pc : Nat}
    {s : TcCommit.Spec} (he : X.get (h, k) = some ⟨pc, .tc (.commit s)⟩)
    (hs : s.mbar = obj L h (80 + 8 * q.val)) :
    ∃ j pce mask inst ld, j < k ∧ X.get (h, j) = some ⟨pce, .elect mask inst ld⟩ ∧
      ∀ g, SameWarp L h g → ∀ i pci maski insti ldi,
        X.get (g, i) = some ⟨pci, .elect maski insti ldi⟩ →
        ((X.tr g).take i).countP isElectEv = ((X.tr h).take j).countP isElectEv →
        okPolls (obj L g (96 + 8 * q.val)) ((X.tr g).take i) =
            ((X.tr h).take k).countP (commitsTo (obj L h (80 + 8 * q.val))) ∧
          okPolls (obj L g (112 + 8 * q.val)) ((X.tr g).take i) =
            ((X.tr h).take k).countP (commitsTo (obj L h (80 + 8 * q.val))) := by
  obtain ⟨c, r, R, ho, -, hok, hcom, j, pce, mask, inst, ld, hj, hget, hall⟩ :=
    commit_elect hp hX hFw hw he hs
  refine ⟨j, pce, mask, inst, ld, hj, hget, fun g hwg i pci maski insti ldi hgi hcnt => ?_⟩
  have h1 := hall g hwg i pci maski insti ldi hgi hcnt (96 + 8 * q.val)
  have h2 := hall g hwg i pci maski insti ldi hgi hcnt (112 + 8 * q.val)
  rw [h1, h2, hcom]
  have hpre := hok.1
  fin_cases q <;> fin_cases c <;> simp [Mma.cmO] at ho <;> try omega
  all_goals simp [Mma.Site.ord] at hpre
  all_goals simp [Mma.Site.ord, acqAt, commitAt, pq]
  all_goals omega

/-- **The commit of a final O barrier** follows an election of its lane at which every lane of the
warp has polled the stage's P-full once more than the tile's loop rounds; it is the lane's first. -/
theorem mma_o_commit (q : Fin 2) (hw : Prologue.warpIndex L h = 12) {pc : Nat}
    {s : TcCommit.Spec} (he : X.get (h, k) = some ⟨pc, .tc (.commit s)⟩)
    (hs : s.mbar = obj L h (144 + 8 * q.val)) :
    ((X.tr h).take k).countP (commitsTo (obj L h (144 + 8 * q.val))) = 0 ∧
    ∃ R, MmaRounds p L h R ∧
    ∃ j pce mask inst ld, j < k ∧ X.get (h, j) = some ⟨pce, .elect mask inst ld⟩ ∧
      ∀ g, SameWarp L h g → ∀ i pci maski insti ldi,
        X.get (g, i) = some ⟨pci, .elect maski insti ldi⟩ →
        ((X.tr g).take i).countP isElectEv = ((X.tr h).take j).countP isElectEv →
        okPolls (obj L g (96 + 8 * q.val)) ((X.tr g).take i) = R + 1 := by
  obtain ⟨c, r, R, ho, hR, hok, hcom, j, pce, mask, inst, ld, hj, hget, hall⟩ :=
    commit_elect hp hX hFw hw he hs
  have htail := hok.2.2
  have hc : c = ⟨10 + q.val, by omega⟩ := by
    fin_cases q <;> fin_cases c <;> simp [Mma.cmO] at ho ⊢ <;> omega
  clear ho
  refine ⟨?_, R, hR, j, pce, mask, inst, ld, hj, hget,
    fun g hwg i pci maski insti ldi hgi hcnt => ?_⟩
  · rw [hcom, hc]
    fin_cases q <;> simp [Mma.Site.ord, commitAt, pq]
  · rw [hall g hwg i pci maski insti ldi hgi hcnt (96 + 8 * q.val)]
    rw [hc] at htail ⊢
    fin_cases q
    · simp [Mma.Site.ord] at htail
      simp [Mma.Site.ord, acqAt, pq]
      omega
    · simp [Mma.Site.ord] at htail
      simp [Mma.Site.ord, acqAt, pq]
      omega

/-- The lane's own polls at a commit are at least those at the election before it. -/
private theorem commit_own (hw : Prologue.warpIndex L h = 12) {pc o : Nat} {s : TcCommit.Spec}
    (he : X.get (h, k) = some ⟨pc, .tc (.commit s)⟩) (hs : s.mbar = obj L h o) :
    ∃ c r, o = Mma.cmO r c ∧ ((Mma.Site.cm c).ord < 20 → r = 0) ∧
      ((X.tr h).take k).countP (commitsTo (obj L h o)) = commitAt (Mma.Site.cm c).ord r o ∧
      ∀ o', acqAt (Mma.Site.ce c).ord r o' ≤ okPolls (obj L h o') ((X.tr h).take k) := by
  obtain ⟨c, r, R, ho, -, hok, hcom, j, pce, mask, inst, ld, hj, hget, hall⟩ :=
    commit_elect hp hX hFw hw he hs
  refine ⟨c, r, ho, hok.1, hcom, fun o' => ?_⟩
  have hh := Frame.lt_of_get hX he
  rw [← hall h ⟨⟨hh, hh, rfl⟩, rfl⟩ j pce mask inst ld hget rfl o']
  exact (List.take_sublist_take_left (l := X.tr h) hj.le).countP_le

/-- **The commit of K/V empty slot `s` with `t` earlier ones** follows `t + 1` of the lane's polls
of full slot `s`. -/
theorem mma_kv_commit (q : Fin 3) (hw : Prologue.warpIndex L h = 12) {pc : Nat}
    {s : TcCommit.Spec} (he : X.get (h, k) = some ⟨pc, .tc (.commit s)⟩)
    (hs : s.mbar = obj L h (56 + 8 * q.val)) :
    ((X.tr h).take k).countP (commitsTo (obj L h (56 + 8 * q.val))) + 1 ≤
      okPolls (obj L h (32 + 8 * q.val)) ((X.tr h).take k) := by
  obtain ⟨c, r, ho, hpre, hcom, hall⟩ := commit_own hp hX hFw hw he hs
  refine le_trans ?_ (hall (32 + 8 * q.val))
  rw [hcom]
  have hq := q.isLt
  -- the release index, its slot, and the acquisitions before the election
  have key : Mma.ringRel (Mma.Site.cm c).ord r % 3 = q.val ∧
      Mma.ringRel (Mma.Site.cm c).ord r + 1 ≤ Mma.ringAcq (Mma.Site.ce c).ord r := by
    fin_cases c <;> simp [Mma.cmO] at ho <;> simp [Mma.Site.ord] at hpre <;>
      simp [Mma.Site.ord, Mma.ringRel, Mma.ringAcq, pq] <;> omega
  have e1 : commitAt (Mma.Site.cm c).ord r (56 + 8 * q.val) =
      Mma.ringCount (Mma.ringRel (Mma.Site.cm c).ord r) q.val := by
    unfold commitAt
    have : (56 + 8 * q.val - 56) / 8 = q.val := by omega
    rw [this]
    simp only [show ¬ (56 + 8 * q.val = 80) by omega, show ¬ (56 + 8 * q.val = 88) by omega,
      show ¬ (56 + 8 * q.val = 16) by omega, show ¬ (56 + 8 * q.val = 24) by omega,
      show ¬ (56 + 8 * q.val = 144) by omega, show ¬ (56 + 8 * q.val = 152) by omega,
      show 56 ≤ 56 + 8 * q.val ∧ 56 + 8 * q.val < 80 ∧ (56 + 8 * q.val) % 8 = 0 by omega,
      ite_false, ite_true, Nat.zero_add, and_self]
  have e2 : acqAt (Mma.Site.ce c).ord r (32 + 8 * q.val) =
      Mma.ringCount (Mma.ringAcq (Mma.Site.ce c).ord r) q.val := by
    unfold acqAt
    have : (32 + 8 * q.val - 32) / 8 = q.val := by omega
    rw [this]
    simp only [show ¬ (32 + 8 * q.val = 0) by omega, show ¬ (32 + 8 * q.val = 8) by omega,
      show ¬ (32 + 8 * q.val = 96) by omega, show ¬ (32 + 8 * q.val = 104) by omega,
      show ¬ (32 + 8 * q.val = 112) by omega, show ¬ (32 + 8 * q.val = 120) by omega,
      show 32 ≤ 32 + 8 * q.val ∧ 32 + 8 * q.val < 56 ∧ (32 + 8 * q.val) % 8 = 0 by omega,
      ite_false, ite_true, Nat.zero_add, and_self]
  rw [e1, e2]
  obtain ⟨k1, k2⟩ := key
  have h1 : Mma.ringCount (Mma.ringRel (Mma.Site.cm c).ord r + 1) q.val =
      Mma.ringCount (Mma.ringRel (Mma.Site.cm c).ord r) q.val + 1 := by
    unfold Mma.ringCount; omega
  rw [← h1]
  unfold Mma.ringCount
  omega

/-- **The commit of a Q stage's empty barrier** is the lane's first, after its poll of the stage's
full barrier. -/
theorem mma_q_commit (q : Fin 2) (hw : Prologue.warpIndex L h = 12) {pc : Nat}
    {s : TcCommit.Spec} (he : X.get (h, k) = some ⟨pc, .tc (.commit s)⟩)
    (hs : s.mbar = obj L h (16 + 8 * q.val)) :
    ((X.tr h).take k).countP (commitsTo (obj L h (16 + 8 * q.val))) + 1 ≤
      okPolls (obj L h (8 * q.val)) ((X.tr h).take k) := by
  obtain ⟨c, r, ho, hpre, hcom, hall⟩ := commit_own hp hX hFw hw he hs
  refine le_trans ?_ (hall (8 * q.val))
  rw [hcom]
  fin_cases q <;> fin_cases c <;> simp [Mma.cmO] at ho <;> try omega
  all_goals simp [Mma.Site.ord, acqAt, commitAt, pq]

end

end
end PTX.Kernels.TmlFa4Fwd.Proof
