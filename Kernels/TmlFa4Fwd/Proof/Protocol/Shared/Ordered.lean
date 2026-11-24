-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Lib.TmemAccess
public import Kernels.TmlFa4Fwd.Proof.Protocol.Bias.Ordered
public import Kernels.TmlFa4Fwd.Proof.Protocol.Shared.AllocWord
public import Kernels.TmlFa4Fwd.Proof.Protocol.Shared.ShFrame
public import Kernels.TmlFa4Fwd.Proof.Protocol.Shared.StatWord
public import Lemmas.Protocol.RegionByte
import Kernels.TmlFa4Fwd.Proof.Protocol.KV.CopyOrder
import Kernels.TmlFa4Fwd.Proof.Protocol.Q.Ordered
import Kernels.TmlFa4Fwd.Proof.Protocol.Staging.KvFinal
import Kernels.TmlFa4Fwd.Proof.Protocol.Staging.QFinal
import Kernels.TmlFa4Fwd.Proof.Protocol.Staging.Read
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # Shared memory is ordered

The shared accesses lie in the allocation word, the statistics words, the staging and K/V bytes
`[sb + 3072, sb + 166912)` and the bias stages (`sh_region`). In the third the accesses are final O
stores, row copies, Q copies, operand reads and tensor-store reads (`MidAcc`), ordered pair by pair
(`mid_ordered`); so all conflicts of shared memory are (`shared_ordered`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow AsyncCopy

noncomputable section

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- A byte of the staging, Q and K/V slots. -/
def InMid (L : Launch) (l : Loc) : Prop :=
  l.space = .shared ∧ L.sharedBase + 3072 ≤ l.addr ∧ l.addr < L.sharedBase + 166912

/-- The accesses of a byte of `InMid`. -/
inductive MidAcc (L : Launch) (X : Execution) (l : Loc) : Ref → Acc → Bool → Prop
  | fst {h i pc a bs} (hw : 8 ≤ Prologue.warpIndex L h) (hw1 : Prologue.warpIndex L h ≤ 11)
      (he : X.get (h, i) = some ⟨pc, .wr a bs⟩) (hc : l.cta = h / L.block) :
      MidAcc L X l (.thread (h, i)) a true
  | row {y jc pc sp} (he : X.get (y, jc) = some ⟨pc, .copy sp⟩) (hc : l.cta = y / L.block)
      (hlo : L.sharedBase + 68608 ≤ l.addr) :
      MidAcc L X l (.async (y, jc) (.write .copy)) sp.dst true
  | tma {e pc al s x y z a} (he : X.get e = some ⟨pc, .tensorIssue al s⟩)
      (hl : TensorCopy.writeLoc s x y z = some l) (hc : l.cta = e.1 / L.block)
      (hhi : l.addr < L.sharedBase + 68608) : MidAcc L X l (.async e (.write (.load x y z))) a true
  | mmaA {g k idx a st u j} (hst : st < 2) (h : Tm.Qk L X g k st u j) (hc : l.cta = g / L.block)
      (hlo : L.sharedBase + 3072 + 32768 * st ≤ l.addr)
      (hhi : l.addr < L.sharedBase + 3072 + 32768 * st + 32768) :
      MidAcc L X l (.async (g, k) (.mmaRead false idx)) a false
  | mmaB {g k idx a} (hm : Tmem1.IsMma X (g, k)) (hc : l.cta = g / L.block)
      (hlo : L.sharedBase + 68608 ≤ l.addr) :
      MidAcc L X l (.async (g, k) (.mmaRead true idx)) a false
  | st {o kt addr s x y z a} (hi : X.TensorStoreIssue (o, kt) addr s)
      (hr : TensorStore.readLoc s x y z = some l) (hc : l.cta = o / L.block) :
      MidAcc L X l (.async (o, kt) (.read (.store x y z))) a false

/-- A one-byte access is at the byte it covers. -/
theorem loc_of_one {a : Acc} {l : Loc} (hz : a.size = 1) (hc : a.Covers l) : a.loc = l := by
  obtain ⟨⟨s1, c1, a1⟩, n, e1, e2, e3, e4⟩ := a
  obtain ⟨s2, c2, a2⟩ := l
  obtain ⟨h1, h2, h3, h4⟩ := hc
  simp only at hz h1 h2 h3 h4
  simp only [Loc.mk.injEq]
  exact ⟨h1.symm, h2.symm, by omega⟩

section
variable (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow p L X)
include hp hX hFw

/-- **The regions of the shared accesses.** -/
theorem sh_region {r : Ref} {a : Acc} {w : Bool} {l : Loc} (hi : X.Intent r a w)
    (hc : a.Covers l) (hl : l.space = .shared) :
    InAlloc L l ∨ InStat L l ∨ InBias L l ∨ InMid L l ∧ MidAcc L X l r a w := by
  have hs : a.loc.space = .shared := hc.1.symm.trans hl
  have hA := sh_intent hp hX hFw hi hs
  obtain ⟨-, c2, c3, c4⟩ := id hc
  have hwr : ∀ {g k : Nat}, r = .thread (g, k) → w = true → ∃ pc bs,
      X.get (g, k) = some ⟨pc, .wr a bs⟩ := by
    rintro g k rfl rfl
    rcases hi with ⟨bs, -, h⟩ | ⟨bs, ⟨pc, he⟩, -⟩ | ⟨o, n, pc, he⟩
    · cases h
    · exact ⟨pc, bs, he⟩
    · exact (no_rmw hX he).elim
  cases hA with
  | allocWr hw h | allocRd hw h =>
    obtain ⟨hz, hloc⟩ := h
    rw [hloc] at c3 c4
    rw [hz] at c4
    exact .inl ⟨hl, c3, c4⟩
  | @statWr g k a hw h =>
    obtain ⟨hz, n, hn, hloc⟩ := h
    have hst : Softmax.stN L g ≤ 1 := by unfold Softmax.stN; split <;> omega
    have := Nat.mod_lt (g % L.block) (show 0 < 128 by decide)
    rw [hloc] at c3 c4
    rw [hz] at c4
    simp only at c3 c4
    exact .inr (.inl ⟨hl, by omega, by omega⟩)
  | @statRd g k a hw hw1 n st h =>
    have := Nat.mod_lt (g % L.block) (show 0 < 128 by decide)
    have hn := n.isLt
    have hst := st.isLt
    obtain ⟨hz, hloc⟩ := h
    rw [hloc] at c3 c4
    rw [hz] at c4
    simp only [Correction.rowN] at c3 c4
    exact .inr (.inl ⟨hl, by omega, by omega⟩)
  | @biasRd g k a hw h =>
    obtain ⟨hz, -, -, h3, h4⟩ := h
    have hst : Softmax.stN L g ≤ 1 := by unfold Softmax.stN; split <;> omega
    exact .inr (.inr (.inl ⟨hl, by omega, by omega⟩))
  | @fstWr g k a hw hw1 st h =>
    obtain ⟨pc, bs, he⟩ := hwr rfl rfl
    obtain ⟨hz, q, hq, w, hw', hloc⟩ := h
    have := Nat.mod_lt (g % L.block) (show 0 < 128 by decide)
    have hst := st.isLt
    rw [hloc] at c2 c3 c4
    rw [hz] at c4
    simp only [Correction.rowN] at c2 c3 c4
    exact .inr (.inr (.inr ⟨⟨hl, by omega, by omega⟩, .fst hw hw1 he c2⟩))
  | @rowCp g k pc sp hw he h =>
    obtain ⟨i, j, -, hloc⟩ := h.dst
    have hcl := Loader.rowCol_lt _ (Nat.mod_lt (g % L.block) (show 0 < 64 by decide))
    have hi := i.isLt
    have hj := j.isLt
    have h3 := Nat.mod_lt (pkt X g k) (show 0 < 3 by decide)
    rw [hloc] at c2 c3 c4
    simp only [Loader.cpAddr] at c2 c3 c4
    exact .inr (.inr (.inr ⟨⟨hl, by omega, by omega⟩, .row he c2 (by omega)⟩))
  | @tmaWr g k pc al sp x y z a hw he hz hloc hcta j hlo hhi =>
    obtain rfl := loc_of_one hz hc
    rcases tload_off_apart j with h | h
    · exact .inr (.inr (.inr ⟨⟨hl, by omega, by omega⟩, .tma he hloc hcta (by omega)⟩))
    · exact .inr (.inr (.inl ⟨hl, by omega, by omega⟩))
  | @mmaA g k idx a st u j off hst h hz ho hloc =>
    obtain rfl := loc_of_one hz hc
    rw [hloc] at c3 ⊢
    simp only at c3
    exact .inr (.inr (.inr ⟨⟨rfl, by simp only; omega, by simp only; omega⟩,
      .mmaA hst h rfl (by simp only; omega) (by simp only; omega)⟩))
  | @mmaB g k idx a st u j off t hst h hz ho hloc =>
    obtain rfl := loc_of_one hz hc
    have h3 := Nat.mod_lt t (show 0 < 3 by decide)
    have hm : Tmem1.IsMma X (g, k) := by
      rcases h with ⟨h, -⟩ | ⟨h, -⟩
      · obtain ⟨pc, _, _, he⟩ := h.issue
        exact ⟨_, _, _, _, pc, he⟩
      · obtain ⟨pc, _, he⟩ := h.issue
        exact ⟨_, _, _, _, pc, he⟩
    rw [hloc]
    exact .inr (.inr (.inr ⟨⟨rfl, by simp only; omega, by simp only; omega⟩,
      .mmaB hm rfl (by simp only; omega)⟩))
  | @storeRd g k pc al sp x y z a hw he hz hloc st bx hcta hlo hhi =>
    obtain rfl := loc_of_one hz hc
    have := st.isLt
    have := bx.isLt
    exact .inr (.inr (.inr ⟨⟨hl, by omega, by omega⟩, .st ⟨pc, he⟩ hloc hcta⟩))

/-- **A write and an access of one byte of the middle region are ordered.** -/
theorem mid_pair {e f : Ref} {a b : Acc} {wf : Bool} {l : Loc} (hl : InMid L l)
    (hne : e ≠ f) (he : X.Intent e a true) (hf : X.Intent f b wf) (ha : a.Covers l)
    (hb : b.Covers l) (hE : MidAcc L X l e a true) (hF : MidAcc L X l f b wf) :
    ByteCausality L X l e f ∨ ByteCausality L X l f e := by
  obtain ⟨hsp, hl1, hl2⟩ := hl
  cases hE with
  | fst hw hw1 hge hcta =>
    cases hF with
    | fst hw' hw1' hge' _ =>
      exact (fst_fst hp hX hFw hw hw1 hw' hw1' hge hge' hsp ha hb
        (fun h => hne (congrArg Ref.thread h))).imp (fun h => .direct (.of_base L h))
        (fun h => .direct (.of_base L h))
    | row hcp hc' _ =>
      exact .inr (kv_copy_fst hp hX hFw hcp hb ⟨_, _, hf, hb⟩ ⟨_, hf, hb⟩ hw hw1 hge hsp ha
        (hc'.symm.trans hcta))
    | tma hce hwl _ hhi =>
      exact .inr (q_copy_fst hp hX hFw hce hwl hl1 hhi hw hw1 hge hsp ha)
    | mmaA hst h hc' _ _ =>
      obtain ⟨pcq, _, _, hq⟩ := h.issue
      exact .inr (.direct (mma_fst hp hX hFw hw hw1 hge hsp ha ⟨_, _, _, _, pcq, hq⟩
        (hc'.symm.trans hcta) ⟨_, _, hf, hb⟩))
    | mmaB hm hc' _ =>
      exact .inr (.direct (mma_fst hp hX hFw hw hw1 hge hsp ha hm (hc'.symm.trans hcta)
        ⟨_, _, hf, hb⟩))
    | st hi hr _ => exact .inl (.direct (fst_store hp hX hFw hw hw1 hge ha hi hr))
  | row hcp hcta hlo =>
    cases hF with
    | fst hw hw1 hge hc' =>
      exact .inl (kv_copy_fst hp hX hFw hcp ha ⟨_, _, he, ha⟩ ⟨_, he, ha⟩ hw hw1 hge hsp hb
        (hcta.symm.trans hc'))
    | row hcp' _ _ =>
      exact (kv_row_row hp hX hFw hcp hcp' ha hb ⟨_, _, he, ha⟩ ⟨_, _, hf, hb⟩
        (fun h => hne (by rw [h]))).imp .direct .direct
    | tma _ _ _ hhi => omega
    | mmaA hst _ _ _ hhi => omega
    | mmaB =>
      exact (kv_row_mma hp hX hFw he hf ha hb ⟨_, _, _, _, rfl, hcp, rfl⟩
        ⟨_, _, _, rfl⟩).imp .direct .direct
    | st hi hr hc' =>
      exact .inl (.direct (kv_copy_store hp hX hFw hcp ha ⟨_, _, he, ha⟩ hi hr
        (hcta.symm.trans hc')))
  | tma hce hwl hcta hhi =>
    cases hF with
    | fst hw hw1 hge _ => exact .inl (q_copy_fst hp hX hFw hce hwl hl1 hhi hw hw1 hge hsp hb)
    | row _ _ hlo => omega
    | tma hce' hwl' _ _ => exact (hne (q_copy_unique hp hX hFw hce hce' hwl hwl' hl1 hhi)).elim
    | mmaA hst h hc' h1 h2 =>
      exact .inl (.direct (q_copy_read hp hX hFw hce hwl h hst ⟨_, _, hf, hb⟩ hc' h1 h2))
    | mmaB _ _ hlo => omega
    | st hi hr hc' =>
      exact .inl (.direct (q_copy_store hp hX hFw hce hwl hl1 hhi hi hr (hcta.symm.trans hc')))

/-- **Shared memory is ordered.** -/
theorem shared_ordered : ByteOrdered L X fun l => l.space = .shared := by
  intro e f a b l hcon ha hb hl hE
  obtain ⟨hne, we, wf, he, hf, hw, -⟩ := id hcon
  rcases sh_region hp hX hFw he ha hl with h | h | h | ⟨hm, hMe⟩
  · exact (alloc_ordered hp hX hFw).byte e f a b l hcon ha hb h hE
  · exact (stat_ordered hp hX hFw).byte e f a b l hcon ha hb h hE
  · exact (bias_ordered hp hX hFw).byte e f a b l hcon ha hb h hE
  · rcases sh_region hp hX hFw hf hb hl with h | h | h | ⟨-, hMf⟩
    · exact (alloc_ordered hp hX hFw).byte e f a b l hcon ha hb h hE
    · exact (stat_ordered hp hX hFw).byte e f a b l hcon ha hb h hE
    · exact (bias_ordered hp hX hFw).byte e f a b l hcon ha hb h hE
    · rcases hw with rfl | rfl
      · exact mid_pair hp hX hFw hm hne he hf ha hb hMe hMf
      · exact (mid_pair hp hX hFw hm hne.symm hf he hb ha hMf hMe).symm

end

end
end PTX.Kernels.TmlFa4Fwd.Proof
