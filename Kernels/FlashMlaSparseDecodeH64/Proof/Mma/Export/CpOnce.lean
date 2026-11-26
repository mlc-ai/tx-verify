-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MemRows.Base
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MbarRows.Mma
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Where
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.MmaLane
import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.EvKind
import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Desc
import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.TmemCode
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.MmaFoot
import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.MmaCover
import Lemmas.Protocol.CountNth

@[expose] public section

/-! # The MMA lane's copies come once each, before its MMAs

For a lane with copies (`tcgen05.cp`) at MMA pcs, from the role's counts (`Mma/Ref.lean`: before
copy `k` the lane has made `k` copies, in the block loop all sixteen):

* `mma_cp_once`: two copies of the lane to one Tensor Memory address are one event;
* `mma_cp_first`: a copy of the lane precedes every MMA of the lane. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow MbarRow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- An event of a list counted by `p` raises the count of every longer prefix. -/
private theorem count_step {l : List Event} {p : Event → Bool} {i j : Nat} {f : Event}
    (hf : l[i]? = some f) (hp : p f = true) (hij : i < j) :
    (l.take i).countP p + 1 ≤ (l.take j).countP p := by
  have hi : i < l.length := (List.getElem?_eq_some_iff.mp hf).1
  have h1 : l.take (i + 1) = l.take i ++ [f] := by
    rw [List.take_add_one, hf]
    rfl
  have h2 := (List.take_sublist_take_left (l := l) (show i + 1 ≤ j by omega)).countP_le (p := p)
  rw [h1, List.countP_append] at h2
  simpa [hp] using h2

/-- The tiles of the shared workspace start at a multiple of 128 bytes. -/
theorem shared_base_128 (hp : Pre P L m) : L.sharedBase % 128 = 0 := by
  simpa only [Nat.add_zero] using Mma.base_128 hp 0 rfl

section
variable (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow P L X)
include hp hX hFw

/-- A copy of the lane is copy `k` of the prologue, after `k` copies, to column `256 + 8 k`. -/
private theorem cp_site {i pc : Nat} {c : TcCopy.Spec}
    (hi : X.get (g, i) = some ⟨pc, .tc (.cp c)⟩) (hr : 1850 ≤ pc ∧ pc < 2162) :
    ∃ k : Fin 16, c.address = 256 + 8 * k.val ∧ Mma.cls .cp ⟨pc, .tc (.cp c)⟩ = true ∧
      ((X.tr g).take i).countP (Mma.cls .cp) = k.val := by
  obtain ⟨d, hR, ⟨hpc, hE⟩, hl, -⟩ := mma_at hp hX hFw hi (fun _ h => by cases h) hr
  have hc := hR (take_noUb hX hi)
  obtain ⟨site, l0, l1, neg, cnt, pha, par⟩ := d
  cases site <;> simp [Mma.EvK, Mma.PollEv, Mma.CommitEv, Mma.MmaEv] at hE
  case leave s => exact absurd rfl (hl s)
  case qCopy k =>
    obtain ⟨-, -, ha, -⟩ := hE
    have hn := Mma.pro_cnt hc ⟨rfl, by simp, by simp⟩ (c := .cp) (by simp)
    refine ⟨k, by simpa [Mma.cpCol] using ha, ?_, ?_⟩
    · have hin : 1853 ≤ pc ∧ pc ≤ 2160 := by
        simp only [Mma.Site.pc] at hpc
        split at hpc <;> omega
      simp [Mma.cls, Mma.inRole, Mma.kindOf, hin]
    · rw [hn]
      simp [Mma.cntAt, Mma.proCnt, Mma.loopCnt, Mma.Site.pro]

/-- **Two copies of the lane to one address are one event.** -/
theorem mma_cp_once {i j pc pc' : Nat} {c c' : TcCopy.Spec}
    (hi : X.get (g, i) = some ⟨pc, .tc (.cp c)⟩) (hj : X.get (g, j) = some ⟨pc', .tc (.cp c')⟩)
    (hr : 1850 ≤ pc ∧ pc < 2162) (hr' : 1850 ≤ pc' ∧ pc' < 2162) (ha : c.address = c'.address) :
    i = j := by
  obtain ⟨k, hk, hci, hni⟩ := cp_site hp hX hFw hi hr
  obtain ⟨k', hk', hcj, hnj⟩ := cp_site hp hX hFw hj hr'
  have hkk : k.val = k'.val := by omega
  rcases Nat.lt_trichotomy i j with h | h | h
  · have := count_step (l := X.tr g) hi hci h
    simp only at this
    omega
  · exact h
  · have := count_step (l := X.tr g) hj hcj h
    simp only at this
    omega

/-- **A copy of the lane precedes every MMA of the lane.** -/
theorem mma_cp_first {i j pc pc' : Nat} {c : TcCopy.Spec} {dc : Nat} {s : TcMma.OperandSpec}
    {acc : Bool} {mask : List Nat}
    (hi : X.get (g, i) = some ⟨pc, .tc (.cp c)⟩)
    (hj : X.get (g, j) = some ⟨pc', .tc (.mma dc s acc mask)⟩)
    (hr : 1850 ≤ pc ∧ pc < 2162) (hr' : 1850 ≤ pc' ∧ pc' < 2162) : i < j := by
  obtain ⟨k, -, hci, hni⟩ := cp_site hp hX hFw hi hr
  obtain ⟨d, hR, ⟨-, hE⟩, hl, -⟩ := mma_at hp hX hFw hj (fun _ h => by cases h) hr'
  have hc := hR (take_noUb hX hj)
  have h16 : ((X.tr g).take j).countP (Mma.cls .cp) = 16 := by
    obtain ⟨site, l0, l1, neg, cnt, pha, par⟩ := d
    cases site <;> simp [Mma.EvK, Mma.PollEv, Mma.CommitEv, Mma.MmaEv] at hE
    case leave s => exact absurd rfl (hl s)
    all_goals
      obtain ⟨-, hn⟩ := (Mma.core_loop (by rfl)).mp hc
      rw [hn _ (by simp)]
      simp [Mma.cntAt, Mma.proCnt, Mma.loopCnt]
  rcases Nat.lt_trichotomy i j with h | rfl | h
  · exact h
  · rw [hi] at hj
    cases hj
  · have := (List.take_sublist_take_left (l := X.tr g) h.le).countP_le (p := Mma.cls .cp)
    have := k.isLt
    omega

/-- Copy `k` of the prologue: its source descriptor and its CTA. -/
private theorem cp_src {i pc : Nat} {c : TcCopy.Spec}
    (hi : X.get (g, i) = some ⟨pc, .tc (.cp c)⟩) (hr : 1850 ≤ pc ∧ pc < 2162) :
    ∃ k : Fin 16, ((X.tr g).take i).countP (Mma.cls .cp) = k.val ∧
      c.shape = .s128x256b ∧ c.src = MmaFoot.keyDesc L.sharedBase k.val ∧
      c.ctas = [g / L.block] ∧ warp L g = 4 ∧ 1853 < pc ∧ c.fmt = none := by
  obtain ⟨d, hR, ⟨hpc, hE⟩, hl, hw⟩ := mma_at hp hX hFw hi (fun _ h => by cases h) hr
  have hc := hR (take_noUb hX hi)
  have hg : g < L.threads := Frame.lt_of_get hX hi
  have hb : 0 < L.block := by rw [hp.block]; decide
  have hgs : L.ctaGroup (g / L.block) .one = some [g / L.block] :=
    ctaGroup_self hp ((Nat.div_lt_iff_lt_mul hb).2 hg)
  obtain ⟨site, l0, l1, neg, cnt, pha, par⟩ := d
  cases site <;> simp only [Mma.EvK] at hE
  case qCopy k =>
    rcases hE with ⟨s', hk, hsh, hfmt, -, hct, hsrc⟩ | ⟨f, hf⟩
    · cases hk
      rw [hgs] at hct
      rw [Mma.cpW_decode hp k.isLt] at hsrc
      have hpc' : 1853 < pc := by
        simp only [Mma.Site.pc] at hpc
        have := k.isLt
        split at hpc <;> omega
      refine ⟨k, ?_, hsh, (Option.some.inj hsrc).symm, (Option.some.inj hct).symm, hw, hpc', hfmt⟩
      rw [Mma.pro_cnt hc ⟨rfl, by simp, by simp⟩ (c := .cp) (by simp)]
      simp [Mma.cntAt, Mma.proCnt, Mma.loopCnt, Mma.Site.pro]
    · cases hf
  case leave k => exact absurd rfl (hl k)
  all_goals simp [Mma.PollEv, Mma.CommitEv, Mma.MmaEv] at hE

/-- **The spec of a copy of the lane**: shape `128x256b`, source descriptor of copy `k` of the
query tile, the lane's CTA only. -/
theorem mma_cp_spec {i pc : Nat} {c : TcCopy.Spec}
    (hi : X.get (g, i) = some ⟨pc, .tc (.cp c)⟩) (hr : 1850 ≤ pc ∧ pc < 2162) :
    ∃ k : Fin 16, c.shape = .s128x256b ∧ c.src = MmaFoot.keyDesc L.sharedBase k.val ∧
      c.ctas = [g / L.block] := by
  obtain ⟨k, -, hsh, hsrc, hct, -⟩ := cp_src hp hX hFw hi hr
  exact ⟨k, hsh, hsrc, hct⟩

/-- **A copy of the lane does not decompress**: its words are its source bytes. -/
theorem mma_cp_fmt {i pc : Nat} {c : TcCopy.Spec}
    (hi : X.get (g, i) = some ⟨pc, .tc (.cp c)⟩) (hr : 1850 ≤ pc ∧ pc < 2162) :
    c.fmt = none := by
  obtain ⟨-, -, -, -, -, -, -, h⟩ := cp_src hp hX hFw hi hr
  exact h

/-- A commit of the lane follows all sixteen copies. -/
private theorem commit_cps {i pc : Nat} {sp : TcCommit.Spec}
    (hi : X.get (g, i) = some ⟨pc, .tc (.commit sp)⟩) (hr : 1850 ≤ pc ∧ pc < 2162) :
    ((X.tr g).take i).countP (Mma.cls .cp) = 16 := by
  obtain ⟨d, hR, hev, hl, -⟩ := mma_at hp hX hFw hi (fun _ h => by cases h) hr
  have hc := hR (take_noUb hX hi)
  rcases Mma.ev_commit hl hev with ⟨hs, -⟩ | ⟨hs, -⟩ | ⟨hs, -⟩
  · rw [Mma.pro_cnt hc (by rw [hs]; exact ⟨rfl, by simp, by simp⟩) (c := .cp) (by simp), hs]
    simp [Mma.cntAt, Mma.proCnt, Mma.loopCnt, Mma.Site.pro]
  all_goals
    obtain ⟨-, hn⟩ := (Mma.core_loop (by rw [hs]; rfl)).mp hc
    rw [hn _ (by simp)]
    simp [Mma.cntAt, Mma.proCnt, Mma.loopCnt]

/-- **The sixteen copies cover the query tile before any commit of the lane**: a byte of the
dequantized tile 0 of the lane's CTA is a source byte of a copy before the commit. -/
theorem mma_cp_cover {i pc : Nat} {sp : TcCommit.Spec}
    (hi : X.get (g, i) = some ⟨pc, .tc (.commit sp)⟩) (hr : 1850 ≤ pc ∧ pc < 2162)
    {l : Loc} (hl : MemRow.LocIn L (g / L.block) (.dequant 0) l) :
    ∃ j < i, ∃ pc' c idx, X.get (g, j) = some ⟨pc', .tc (.cp c)⟩ ∧ MmaAt L g pc' ∧
      X.MmaFootprint (g, j) false idx l := by
  obtain ⟨hsp, hcta, hlo, hhi⟩ := hl
  simp only [Region.lo, Region.size] at hlo hhi
  have hB := Mma.base_128 hp 0 rfl
  simp only [Nat.add_zero] at hB hlo hhi
  obtain ⟨k, idx, hk, hidx, hb⟩ := MmaFoot.copy_cover (cta := l.cta) hB hlo (by omega)
  have h16 := commit_cps hp hX hFw hi hr
  obtain ⟨j, x, hj, hx, hcnt⟩ := MbarRing.Slot.exists_nth_countP (Mma.cls .cp) (c := k)
    (xs := (X.tr g).take i) (by omega)
  have hji : j < i := by
    have := (List.getElem?_eq_some_iff.mp hj).1
    simp only [List.length_take] at this
    omega
  rw [List.take_take, Nat.min_eq_left hji.le] at hcnt
  have hget : X.get (g, j) = some x := by
    change (X.tr g)[j]? = some x
    rw [← hj, List.getElem?_take, ite_eq_left hji]
  obtain ⟨pc', kd⟩ := x
  have hl' : l = ⟨.shared, l.cta, l.addr⟩ := by
    obtain ⟨sp, c, a⟩ := l
    simp only at hsp ⊢
    rw [hsp]
  have hs4 : idx % 4096 = idx := Nat.mod_eq_of_lt hidx
  have hin : 1850 ≤ pc' ∧ pc' < 2162 := by
    simp only [Mma.cls, Bool.and_eq_true, Mma.inRole, decide_eq_true_eq] at hx
    omega
  cases kd <;> try (simp [Mma.cls, Mma.kindOf] at hx; done)
  case wait q p ok a sc => cases ok <;> simp [Mma.cls, Mma.kindOf] at hx
  case tc t =>
    cases t <;> try (simp [Mma.cls, Mma.kindOf] at hx; done)
    case cp c =>
      obtain ⟨k', hk', hsh, hsrc, hct, hw, -, -⟩ := cp_src hp hX hFw hget hin
      obtain rfl : k'.val = k := by omega
      refine ⟨j, hji, pc', c, idx, hget, ⟨hw, hin⟩, ?_⟩
      refine Or.inr ⟨c, 0, l.cta, ⟨pc', hget⟩, rfl, ?_, ?_, ?_⟩
      · rw [hct]
        simp [hcta]
      · simp [hsh, TcCpShape.sourceBytes, TcCpShape.rows, TcCpShape.rowBytes]
        omega
      · rw [hsh, hsrc]
        simp only [TcCpShape.sourceBytes, TcCpShape.rows, TcCpShape.rowBytes]
        rw [hs4, hl']
        exact hb

/-- **Copy `k` precedes every MMA of the lane**: it exists, in the lane, at a pc of the MMA code,
to column `256 + 8 k`. -/
theorem mma_cp_exists {j pc' dc : Nat} {s : TcMma.OperandSpec} {acc : Bool} {mask : List Nat}
    (hj : X.get (g, j) = some ⟨pc', .tc (.mma dc s acc mask)⟩) (hr' : 1850 ≤ pc' ∧ pc' < 2162)
    {k : Nat} (hk : k < 16) :
    ∃ i < j, ∃ pc c, X.get (g, i) = some ⟨pc, .tc (.cp c)⟩ ∧ (1850 ≤ pc ∧ pc < 2162) ∧
      c.address = 256 + 8 * k := by
  obtain ⟨d, hR, ⟨-, hE⟩, hl, -⟩ := mma_at hp hX hFw hj (fun _ h => by cases h) hr'
  have hc := hR (take_noUb hX hj)
  have h16 : ((X.tr g).take j).countP (Mma.cls .cp) = 16 := by
    obtain ⟨site, l0, l1, neg, cnt, pha, par⟩ := d
    cases site <;> simp [Mma.EvK, Mma.PollEv, Mma.CommitEv, Mma.MmaEv] at hE
    case leave s => exact absurd rfl (hl s)
    all_goals
      obtain ⟨-, hn⟩ := (Mma.core_loop (by rfl)).mp hc
      rw [hn _ (by simp)]
      simp [Mma.cntAt, Mma.proCnt, Mma.loopCnt]
  obtain ⟨i, x, hi, hx, hcnt⟩ := MbarRing.Slot.exists_nth_countP (Mma.cls .cp) (c := k)
    (xs := (X.tr g).take j) (by omega)
  have hij : i < j := by
    have := (List.getElem?_eq_some_iff.mp hi).1
    simp only [List.length_take] at this
    omega
  rw [List.take_take, Nat.min_eq_left hij.le] at hcnt
  have hget : X.get (g, i) = some x := by
    change (X.tr g)[i]? = some x
    rw [← hi, List.getElem?_take, ite_eq_left hij]
  obtain ⟨pc, kd⟩ := x
  have hin : 1850 ≤ pc ∧ pc < 2162 := by
    simp only [Mma.cls, Bool.and_eq_true, Mma.inRole, decide_eq_true_eq] at hx
    omega
  cases kd <;> try (simp [Mma.cls, Mma.kindOf] at hx; done)
  case wait q p ok a sc => cases ok <;> simp [Mma.cls, Mma.kindOf] at hx
  case tc t =>
    cases t <;> try (simp [Mma.cls, Mma.kindOf] at hx; done)
    case cp c =>
      obtain ⟨k', ha, -, hn'⟩ := cp_site hp hX hFw hget hin
      have hkk : k'.val = k := by omega
      exact ⟨i, hij, pc, c, hget, hin, by rw [ha, hkk]⟩

/-- **A copy of the lane is after the election** (`MmaOn`). -/
theorem mma_cp_on {i pc : Nat} {c : TcCopy.Spec}
    (hi : X.get (g, i) = some ⟨pc, .tc (.cp c)⟩) (hat : MmaAt L g pc) : 1853 < pc := by
  obtain ⟨-, -, -, -, -, -, h, -⟩ := cp_src hp hX hFw hi ⟨hat.2.1, hat.2.2⟩
  exact h

/-- **Every copy of the lane precedes every commit of the lane.** -/
theorem mma_cp_before_commit {j ic pc pc' : Nat} {c : TcCopy.Spec} {sp : TcCommit.Spec}
    (hj : X.get (g, j) = some ⟨pc, .tc (.cp c)⟩) (hr : 1850 ≤ pc ∧ pc < 2162)
    (hi : X.get (g, ic) = some ⟨pc', .tc (.commit sp)⟩) (hr' : 1850 ≤ pc' ∧ pc' < 2162) :
    j < ic := by
  obtain ⟨k, -, -, hk⟩ := cp_site hp hX hFw hj hr
  have h16 := commit_cps hp hX hFw hi hr'
  by_contra hh
  have := (List.take_sublist_take_left (l := X.tr g) (Nat.le_of_not_lt hh)).countP_le
    (p := Mma.cls .cp)
  have := k.isLt
  omega

end

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
