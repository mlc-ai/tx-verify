-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Protocol.SingleTmaRing.Attribution

@[expose] public section

/-! # The order of a single-CTA ring slot's copies and the consumer's reads

A proof tool (generalized from the Inkling KV ring). A copy issue completing on `full` is the item
of its *use* `copyUse` (0 for the preloading copies, else the copy thread's earlier copies over
`n` plus `δ`), and a read of the consumer is of the use `readUse` (its earlier commits to
`empty`). Then (`copy_read_order`):

* **RAW**: `copyUse ≤ readUse` implies the copy's writes are before the read: the consumer's
  successful poll of `full` for the use observes the copy's completion record (`copy_observed`),
  and the read follows the poll in program order;
* **WAR**: `readUse < copyUse` implies the read is before the copy's writes: the copy thread's
  successful poll of `empty` for the use `readUse + 1` observes the consumer's notification of
  the commit that completes the read (`read_observed`), and the copy follows the poll in program
  order, the budget placing the copy's use below its successful polls. -/

namespace PTX.SingleTmaRing
open PTX PTX.Flow AsyncCopy
open PTX.MBarrier hiding okPolls

noncomputable section


variable {X : Execution} {S : Slot} {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0}
  {sc₀ : MbarScope}

open Classical in
/-- The use of the slot a copy issue is for: 0 for the prologue's copies, else the loader's earlier
copies on `full` over `n`, plus the preloaded use. -/
def copyUse (X : Execution) (S : Slot) (e : EvId) : Nat :=
  if S.δ = 1 ∧ ∃ i : Fin S.n, e = S.pCp i then 0
  else ((X.tr e.1).take e.2).countP (issuesTo S.full) / S.n + S.δ

/-- The use of the slot a read of the MMA lane is in: its earlier commits to `empty`. -/
def readUse (X : Execution) (S : Slot) (e : EvId) : Nat :=
  ((X.tr e.1).take e.2).countP (commitsTo S.empty)

/-- A tensor-core MMA or copy issue is not a commit. -/
theorem commits_tcAsync_succ {g k : Nat} {m : Loc} (h : X.TcAsync (g, k)) :
    ((X.tr g).take (k + 1)).countP (commitsTo m) = ((X.tr g).take k).countP (commitsTo m) := by
  rcases h with ⟨d, sp, ac, mk, pc, he⟩ | ⟨c, pc, he⟩ | ⟨s, pc, he⟩ <;>
  · rw [List.take_add_one, show (X.tr g)[k]? = _ from he]
    simp [commitsTo]

theorem tcAsync_lt {g k : Nat} (h : X.TcAsync (g, k)) : k < (X.tr g).length := by
  rcases h with ⟨d, sp, ac, mk, pc, he⟩ | ⟨c, pc, he⟩ | ⟨s, pc, he⟩ <;> exact len_of_get he

/-- Threads of one CTA meet at every scope. -/
theorem scopesMeet {g h : Nat} (hs : SameCta L g h) (us ws : MbarScope) :
    ScopesMeet L us g ws h := by
  obtain ⟨hg, hh, hc⟩ := hs
  constructor
  · cases us
    · exact ⟨hg, hh, hc⟩
    · exact ⟨hg, hh, congrArg _ hc⟩
    · exact ⟨hg, hh⟩
    · exact ⟨hg, hh⟩
  · cases ws
    · exact ⟨hh, hg, hc.symm⟩
    · exact ⟨hh, hg, congrArg _ hc.symm⟩
    · exact ⟨hh, hg⟩
    · exact ⟨hh, hg⟩

/-! ### Copies before reads -/

/-- **A copy issue is an item of its use.** -/
theorem copy_item (H : Hyp L K A X S sc₀) {gl kl pc al : Nat} {sp : TensorCopy.Spec}
    (he : X.get (gl, kl) = some ⟨pc, .tensorIssue al sp⟩) (hm : sp.mbar = S.full) :
    ∃ k : Kind S, k.val ≠ 0 ∧ opF X S k (copyUse X S (gl, kl)) = (gl, kl) := by
  classical
  have hδ := H.δ_le
  rcases H.issue he hm with ⟨rfl, hb⟩ | ⟨hδ1, i, hi⟩
  · set I := ((X.tr S.cp).take kl).countP (issuesTo S.full) with hI
    have hp : issuesTo S.full ⟨pc, .tensorIssue al sp⟩ = true := by simp [issuesTo, hm]
    have hnp : ¬ (S.δ = 1 ∧ ∃ i : Fin S.n, (S.cp, kl) = S.pCp i) := by
      rintro ⟨hδ1, i, hi⟩
      exact (H.pre_ne hδ1).2 i (congrArg Prod.fst hi).symm
    have hcu : copyUse X S (S.cp, kl) = I / S.n + S.δ := by
      simp [copyUse, hnp, hI]
    have hn0 : 0 < S.n := by
      rcases Nat.eq_zero_or_pos S.n with h0 | h0
      · rw [h0] at hb; omega
      · exact h0
    have hmod := Nat.mod_lt I hn0
    let k : Kind S := ⟨I % S.n + 1, by omega⟩
    have hk0 : k.val ≠ 0 := by simp [k]
    have hnz : ¬ (S.δ = 1 ∧ I / S.n + S.δ = 0) := fun h => by
      rw [h.1] at h; exact absurd h.2 (Nat.succ_ne_zero _)
    refine ⟨k, hk0, ?_⟩
    rw [hcu, opF_ld hnz, kOwner_ne hk0, prod_one, kPred_ne hk0, kIdx_ne hk0, Nat.add_sub_cancel]
    have : S.n * (I / S.n) + (k.val - 1) = I := by
      simp only [k, Nat.add_sub_cancel]
      exact Nat.div_add_mod I S.n
    rw [this, hI, nthEv_eq he hp]
  · have hcu : copyUse X S (gl, kl) = 0 := by
      simp [copyUse, hδ1, hi]
    let k : Kind S := ⟨i.val + 1, by omega⟩
    have hk0 : k.val ≠ 0 := by simp [k]
    refine ⟨k, hk0, ?_⟩
    rw [hcu, opF_pre_ne hk0 hδ1, hi]
    congr 1

variable (hX : Consistent L K A mem0 X) (hP : S.Fits)
include hX hP

/-- **A copy is observed by its use's poll.** The consumer's successful full poll with `u` earlier
ones observes the completion of a copy issue on the full barrier of use `u`. -/
theorem copy_observed (H : Hyp L K A X S sc₀) {gl kl pc al : Nat} {sp : TensorCopy.Spec}
    (he : X.get (gl, kl) = some ⟨pc, .tensorIssue al sp⟩) (hm : sp.mbar = S.full) {j pcw p : Nat}
    {acq : Bool} {sc : MbarScope} (hew : X.get (S.cm, j) = some ⟨pcw, .wait S.full p true acq sc⟩)
    (hj : okPolls S.full ((X.tr S.cm).take j) = copyUse X S (gl, kl)) :
    AsyncObserved X (gl, kl) (.notify .load) (S.cm, j) true sc := by
  obtain ⟨k, hk, hop⟩ := copy_item H he hm
  have hit : itF X S k (copyUse X S (gl, kl)) = .async (gl, kl) (.notify .load) := by
    simp only [itF, hk, ↓reduceIte, hop]
  have hlt : copyUse X S (gl, kl) < okPolls S.full (X.tr S.cm) := by
    have := PairTmaRing.okPolls_lt_of_get hew
    omega
  obtain ⟨hx, -, hupd⟩ := consumer_observes hX H hP (b := 0) hlt k
  obtain ⟨⟨id, r, hid, hrid, -, -, h1⟩, -⟩ := SF_op H hx
  have hra : r.action = .completeTx S.bytes := h1 hk
  have hwF : wF X S 0 (copyUse X S (gl, kl)) = (S.cm, j) := by
    simp only [wF]
    rw [← hj, MbarRing.Poll.nth_eq hew]
  rw [hit, hwF] at hupd
  rw [hit] at hrid
  obtain ⟨rfl, -⟩ := H.full_acq hew
  have hobj : objectAction X X.async S.full (.async (gl, kl) (.notify .load)) =
      some (.completeTx S.bytes) := by
    have h := ((hX.tma.2.2.1 S.full).2.1 r (List.mem_of_getElem? hid)).1
    rw [hrid, hra] at h
    exact h
  exact PairTmaRing.tensorObserved_of_notified hX hobj hew hupd

/-- **A copy before a read.** A copy on the full barrier of use `u` is ordered before a read of the
MMA lane, at a byte both cover, that has polled the full barrier successfully more than `u` times
before it. -/
theorem copy_before_read (H : Hyp L K A X S sc₀) {km : Nat} (hkm : km < (X.tr S.cm).length)
    {gl kl pcl al : Nat} {spl : TensorCopy.Spec}
    (hel : X.get (gl, kl) = some ⟨pcl, .tensorIssue al spl⟩) (hml : spl.mbar = S.full)
    (hpolls : copyUse X S (gl, kl) + 1 ≤ okPolls S.full ((X.tr S.cm).take km)) {x y z : Nat}
    {l : Loc} {isB : Bool} {idx : Nat} (hca : AsyncCovers X (gl, kl) (.write (.load x y z)) l)
    (hcb : AsyncCovers X (S.cm, km) (.mmaRead isB idx) l) :
    AsyncBefore L X l ((gl, kl), .write (.load x y z)) ((S.cm, km), .mmaRead isB idx) := by
  obtain ⟨j, pc, p, acq, sc, hj, hew, hcw⟩ := MbarRing.Poll.exists_nth hpolls
  have hTO := copy_observed hX hP H hel hml hew hcw
  have hbo : baseCausality L X (S.cm, j) (S.cm, km) :=
    Relation.TransGen.single (Or.inl (po_of_source_not_access rfl hj hkm (by simp [hew,
      Event.acc])))
  have hsm : ScopesMeet L .cluster gl sc S.cm := by
    rcases H.issue hel hml with ⟨rfl, -⟩ | ⟨hδ1, i, hi⟩
    · have := H.cta 1
      rw [prod_one] at this
      exact scopesMeet this _ _
    · rw [show gl = (S.pCp i).1 from congrArg Prod.fst hi]
      exact scopesMeet (H.pre_cta hδ1 i) _ _
  exact ⟨hca, hcb, Or.inl ⟨_, .inr ⟨sc, hTO, hsm⟩, hbo⟩⟩

/-! ### Reads before copies -/

/-- **A producer's poll acquires an earlier read.** A read of the MMA lane, with at most `q`
commits of the lane to the slot up to it, is acquired by a successful empty poll of producer `a`
at or before its successful poll with `q + 1 - δ` earlier ones (the poll for use `q + 1`). -/
theorem read_observed (H : Hyp L K A X S sc₀) {a : Fin 2} {km : Nat} (hR : X.TcAsync (S.cm, km))
    {jl pc p : Nat} {acq : Bool} {sc : MbarScope}
    (hwl : X.get (S.prod a, jl) = some ⟨pc, .wait S.empty p true acq sc⟩) {q : Nat}
    (hq : okPolls S.empty ((X.tr (S.prod a)).take jl) + S.δ = q + 1)
    (hK : ((X.tr S.cm).take (km + 1)).countP (commitsTo S.empty) ≤ q) :
    ∃ jw, jw ≤ jl ∧ AsyncObserved X (S.cm, km) .mmaDone (S.prod a, jw) true sc₀ := by
  have hδ := H.δ_le
  have hlt := PairTmaRing.okPolls_lt_of_get hwl
  obtain ⟨t, htdef⟩ : ∃ t, t = ((X.tr S.cm).take (km + 1)).countP (commitsTo S.empty) :=
    ⟨_, rfl⟩
  rw [← htdef] at hK
  obtain ⟨hy, -, hupd⟩ := producer_observes hX H hP (a := a) (n := t) (by omega) 0
  obtain ⟨⟨i, r, hi, hid, -, -⟩, ⟨pcc, sp, hcm, hmb, htg, hcnt⟩, -⟩ := SE_op H hy
  have hkc : km < (cmE X S 0 t).2 := by
    by_contra hge
    have hp : commitsTo S.empty ⟨pcc, .tc (.commit sp)⟩ = true := by
      simp [commitsTo, hmb]
    have hcm' : X.get (S.cm, (cmE X S 0 t).2) = some ⟨pcc, .tc (.commit sp)⟩ := hcm
    have hcnt' : ((X.tr S.cm).take (cmE X S 0 t).2).countP (commitsTo S.empty) = t :=
      hcnt
    have h1 := countP_take_succ hcm' hp
    have h2 := countP_take_mono (commitsTo S.empty) (X.tr S.cm)
      (show (cmE X S 0 t).2 + 1 ≤ km + 1 by omega)
    omega
  have hwpos : (wE X S a (t + 1)).2 ≤ jl := by
    simp only [wE]
    have hnq : MbarRing.Poll.nth X S.empty (S.prod a)
        (okPolls S.empty ((X.tr (S.prod a)).take jl)) = jl := MbarRing.Poll.nth_eq hwl
    rcases Nat.lt_or_eq_of_le (show t + 1 - S.δ ≤ okPolls S.empty ((X.tr (S.prod a)).take jl)
      by omega) with h | h
    · rw [← hnq]
      exact (MbarRing.Poll.nth_lt_nth h hlt).le
    · rw [h, hnq]
  obtain ⟨pcw, pw, acqw, scw, hew, -⟩ := MbarRing.Poll.nth_spec (X := X)
    (m := S.empty) (g := S.prod a) (n := t + 1 - S.δ) (by omega)
  obtain ⟨rfl, rfl⟩ := H.empty_acq hew
  have hnp := object_record_present hX.tma (List.mem_of_getElem? hi)
  rw [hid] at hnp
  exact ⟨(wE X S a (t + 1)).2, hwpos, _, S.empty,
    ⟨cmE X S 0 t, sp, rank0, rfl, ⟨rfl, hkc, hR, sp, pcc, hcm⟩, ⟨pcc, hcm⟩, htg, hnp⟩,
    ⟨⟨pcw, pw, hew⟩, hupd⟩⟩

/-- **A read before a copy.** A read of the MMA lane is ordered before a copy of the loader's
elected lane, at a byte both cover, when the lane's commits to the slot up to the read are fewer
than the copy's use; and a wait observes the read's completion. -/
theorem read_before_copy (H : Hyp L K A X S sc₀) {km : Nat} (hR : X.TcAsync (S.cm, km))
    {kl pcl al : Nat} {spl : TensorCopy.Spec}
    (hel : X.get (S.cp, kl) = some ⟨pcl, .tensorIssue al spl⟩) (hml : spl.mbar = S.full)
    (hcnt : ((X.tr S.cm).take (km + 1)).countP (commitsTo S.empty) + 1 ≤ copyUse X S (S.cp, kl))
    {x y z : Nat} {l : Loc} {isB : Bool} {idx : Nat}
    (hca : AsyncCovers X (S.cm, km) (.mmaRead isB idx) l)
    (hcb : AsyncCovers X (S.cp, kl) (.write (.load x y z)) l) :
    AsyncBefore L X l ((S.cm, km), .mmaRead isB idx) ((S.cp, kl), .write (.load x y z)) ∧
      ∃ w ws, AsyncObserved X (S.cm, km) .mmaDone w true ws := by
  have hδ := H.δ_le
  have hnp : ¬ (S.δ = 1 ∧ ∃ i : Fin S.n, (S.cp, kl) = S.pCp i) := by
    rintro ⟨hδ1, i, hi⟩
    exact (H.pre_ne hδ1).2 i (congrArg Prod.fst hi).symm
  have hcu : copyUse X S (S.cp, kl) =
      ((X.tr S.cp).take kl).countP (issuesTo S.full) / S.n + S.δ := by
    simp [copyUse, hnp]
  have hb : ((X.tr S.cp).take kl).countP (issuesTo S.full) + 1 ≤
      S.n * okPolls S.empty ((X.tr S.cp).take kl) := by
    rcases H.issue hel hml with ⟨-, hb⟩ | ⟨hδ1, i, hi⟩
    · exact hb
    · exact absurd ⟨hδ1, i, hi⟩ hnp
  rw [hcu] at hcnt
  have hn0 : 0 < S.n := by
    rcases Nat.eq_zero_or_pos S.n with h0 | h0
    · rw [h0] at hb; omega
    · exact h0
  have hm1 : ((X.tr S.cp).take kl).countP (issuesTo S.full) / S.n + 1 ≤
      okPolls S.empty ((X.tr S.cp).take kl) :=
    (Nat.div_lt_iff_lt_mul hn0).mpr (by rw [Nat.mul_comm]; omega)
  obtain ⟨jl, pc, p, acq, sc, hjl, hwl, hcl⟩ := MbarRing.Poll.exists_nth (X := X)
    (g := S.cp) (k := kl) (m := S.empty)
    (n := okPolls S.empty ((X.tr S.cp).take kl) - 1) (by omega)
  have hwl' : X.get (S.prod 1, jl) = some ⟨pc, .wait S.empty p true acq sc⟩ := by
    rw [prod_one]; exact hwl
  obtain ⟨jw, hjw, hom⟩ := read_observed hX hP H (a := 1) hR hwl'
    (q := okPolls S.empty ((X.tr S.cp).take kl) + S.δ - 2)
    (by rw [prod_one, hcl]; omega) (by omega)
  rw [prod_one] at hom
  have hkl : kl < (X.tr S.cp).length := (List.getElem?_eq_some_iff.mp hel).1
  have hbo : baseCausality L X (S.cp, jw) (S.cp, kl) :=
    Relation.TransGen.single (Or.inl (po_of_source_not_access rfl (by omega) hkl
    hom.not_access))
  have hsm : ScopesMeet L .cluster S.cm sc₀ S.cp := by
    have := H.cta 1
    rw [prod_one] at this
    exact scopesMeet ⟨this.2.1, this.1, this.2.2.symm⟩ _ _
  exact ⟨⟨hca, hcb, Or.inl ⟨_, .inr ⟨sc₀, hom, hsm⟩, hbo⟩⟩, _, _, hom⟩

/-! ### Copies and reads are ordered by their uses -/

/-- **A copy and a read of one byte are ordered by their uses.** A copy on the full barrier and a
read of the MMA lane that has polled the full barrier successfully more times than its earlier
commits to the slot, at a byte both cover: the copy is before the read when the copy's use is at
most the read's (RAW, `kv_ready`), the read is before the copy when its use is below the copy's
(WAR, `kv_empty`). -/
theorem copy_read_order (H : Hyp L K A X S sc₀) {km : Nat} (hR : X.TcAsync (S.cm, km))
    (hcR : readUse X S (S.cm, km) + 1 ≤ okPolls S.full ((X.tr S.cm).take km)) {gl kl pcl al : Nat}
    {spl : TensorCopy.Spec} (hel : X.get (gl, kl) = some ⟨pcl, .tensorIssue al spl⟩)
    (hml : spl.mbar = S.full) {x y z : Nat} {l : Loc} {isB : Bool} {idx : Nat}
    (hca : AsyncCovers X (gl, kl) (.write (.load x y z)) l)
    (hcb : AsyncCovers X (S.cm, km) (.mmaRead isB idx) l) :
    (copyUse X S (gl, kl) ≤ readUse X S (S.cm, km) →
      AsyncBefore L X l ((gl, kl), .write (.load x y z)) ((S.cm, km), .mmaRead isB idx)) ∧
    (readUse X S (S.cm, km) < copyUse X S (gl, kl) →
      AsyncBefore L X l ((S.cm, km), .mmaRead isB idx) ((gl, kl), .write (.load x y z))) := by
  refine ⟨fun hle => copy_before_read hX hP H (tcAsync_lt hR) hel hml (by omega) hca hcb,
    fun hlt => ?_⟩
  rcases H.issue hel hml with ⟨rfl, -⟩ | ⟨hδ1, i, hi⟩
  · refine (read_before_copy hX hP H hR hel hml ?_ hcb hca).1
    rw [commits_tcAsync_succ hR]
    exact hlt
  · exfalso
    have : copyUse X S (gl, kl) = 0 := by simp [copyUse, hδ1, hi]
    omega

end
end PTX.SingleTmaRing
