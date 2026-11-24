-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.Shared.Global
import Kernels.TmlFa4Fwd.Proof.Common.Open
import Kernels.TmlFa4Fwd.Proof.Epilogue.Export.MemStore
import Kernels.TmlFa4Fwd.Proof.Protocol.Mbar.Init
import Kernels.TmlFa4Fwd.Proof.Protocol.Mbar.InitOne
import Kernels.TmlFa4Fwd.Proof.Protocol.Shared.Lifetime

@[expose] public section

/-! # Every accessed byte is allocated

ERR-UNALLOCATED-ACCESS from the maps of the accesses (`no_unalloc`): a shared byte lies in the
232448 bytes of a launched CTA's window (`ShAcc.window`), a local byte in the lane's 128 bytes, a
global byte in an input array, the O or the LSE region. Open in it: where a row copy's source lies
(`CpSrc`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow AsyncCopy

noncomputable section

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g k : Nat}

theorem cta_lt {g c : Nat} (hp : Pre p L m) (hg : g < L.threads) (hc : c = g / L.block) :
    c < L.grid := by
  have hb := hp.block
  subst hc
  exact (Nat.div_lt_iff_lt_mul (by omega)).mpr hg

/-- An access's issuer is a thread of the launch. -/
theorem intent_lt (hX : Consistent L kernel Assumptions.all m X) {r : Ref} {a : Acc} {w : Bool}
    (hi : X.Intent r a w) : r.issuer.1 < L.threads := by
  obtain ⟨e, he, -⟩ := Frame.intent_issuer hi
  exact Frame.lt_of_get hX (g := r.issuer.1) (k := r.issuer.2) he

theorem rowN_lt (L : Launch) (g : Nat) : Correction.rowN L g < 128 := Nat.mod_lt _ (by decide)

/-- **An access of shared memory lies in a window**, the issuer's CTA's. -/
theorem ShAcc.window (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) {r : Ref}
    {a : Acc} {w : Bool} (hi : X.Intent r a w) (h : ShAcc L X r a w) :
    a.loc.space = .shared ∧ a.loc.cta = r.issuer.1 / L.block ∧ r.issuer.1 < L.threads ∧
      L.sharedBase ≤ a.loc.addr ∧ a.loc.addr + a.size ≤ L.sharedBase + 232448 := by
  have hlt := intent_lt hX hi
  cases h with
  | allocWr _ h | allocRd _ h =>
    rw [h.2, h.1]; exact ⟨rfl, rfl, hlt, by simp only; omega, by simp only; omega⟩
  | @statWr g k a _ h =>
    obtain ⟨hz, n, hn, hl⟩ := h
    have hr : g % L.block % 128 < 128 := Nat.mod_lt _ (by decide)
    have hst : Softmax.stN L g ≤ 1 := by unfold Softmax.stN; split <;> omega
    rw [hl, hz]; exact ⟨rfl, rfl, hlt, by simp only; omega, by simp only; omega⟩
  | @statRd g k a _ _ n st h =>
    have hr := rowN_lt L g
    have := n.isLt
    have := st.isLt
    rw [h.2, h.1]; exact ⟨rfl, rfl, hlt, by simp only; omega, by simp only; omega⟩
  | @biasRd g k a _ h =>
    obtain ⟨hz, h1, h2, h3, h4⟩ := h
    have hst : Softmax.stN L g ≤ 1 := by unfold Softmax.stN; split <;> omega
    exact ⟨h1, h2, hlt, by omega, by omega⟩
  | @fstWr g k a _ _ st h =>
    obtain ⟨hz, q, hq, w, hw, hl⟩ := h
    have hr := rowN_lt L g
    have := st.isLt
    rw [hl, hz]; exact ⟨rfl, rfl, hlt, by simp only; omega, by simp only; omega⟩
  | @rowCp g k pc sp _ _ h =>
    obtain ⟨i, j, -, hl⟩ := h.dst
    have hcl := Loader.rowCol_lt _ (Nat.mod_lt (g % L.block) (show 0 < 64 by decide))
    have h3 := Nat.mod_lt (pkt X g k) (show 0 < 3 by decide)
    have := i.isLt
    have := j.isLt
    rw [hl]
    exact ⟨rfl, rfl, hlt, by simp only [Loader.cpAddr]; omega,
      by simp only [Loader.cpAddr]; omega⟩
  | tmaWr _ he hz hl hc j hlo hhi =>
    obtain ⟨-, h1, -⟩ := tload_box hp hX hFw he hl
    exact ⟨h1, hc, hlt, by omega, by rcases tload_off_apart j with h | h <;> omega⟩
  | mmaA hst _ hz ho hl =>
    rw [hl, hz]; exact ⟨rfl, rfl, hlt, by simp only; omega, by simp only; omega⟩
  | @mmaB _ _ _ _ _ _ _ _ t _ _ hz ho hl =>
    have h3 := Nat.mod_lt t (show 0 < 3 by decide)
    rw [hl, hz]; exact ⟨rfl, rfl, hlt, by simp only; omega, by simp only; omega⟩
  | storeRd hw he hz hl st bx hc hlo hhi =>
    have := st.isLt
    have := bx.isLt
    obtain ⟨st', bx', h⟩ := storeRead_box hp hX hw ⟨_, he⟩
    obtain ⟨h1, -⟩ := h _ _ _ _ hl
    exact ⟨h1, hc, hlt, by omega, by omega⟩

section
variable (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow p L X)
include hp hX hFw

theorem no_unalloc (hS : CpSrc p X) : ¬ Unalloc m X := by
  have hcov : ∀ {a : Acc} {l : Loc}, a.Covers l → ∃ y < a.size, l = a.loc.at y := by
    rintro ⟨⟨s1, c1, a1⟩, z⟩ ⟨s2, c2, a2⟩ ⟨h1, h2, h3, h4⟩
    simp only at h1 h2 h3 h4
    subst h1 h2
    exact ⟨a2 - a1, by show a2 - a1 < z; omega, by simp only [Loc.at]; congr 1; omega⟩
  have hval : ∀ {l : Loc} {v : Value} {y : Nat}, HasValue m l v → y < v.bytes →
      m (l.at y) ≠ none := fun h hy hn => by rw [h _ hy] at hn; cases hn
  rintro (⟨r, a, l, ht, hc, hn⟩ | ⟨e, o, l, hu, hc, hn⟩)
  · rcases ht with ⟨w, hi⟩ | ⟨i, bs, -, pc, he⟩
    swap
    · exact no_nc hX he
    obtain ⟨y, hy, rfl⟩ := hcov hc
    by_cases hs : a.loc.space = .shared
    · obtain ⟨h1, h2, h3, h4, h5⟩ := (sh_intent hp hX hFw hi hs).window hp hX hFw hi
      have h := hp.shared.2.2 a.loc.cta (cta_lt hp h3 h2) (a.loc.addr - L.sharedBase + y) (by omega)
      apply h
      rw [← hn]
      obtain ⟨⟨s1, c1, a1⟩, z⟩ := a
      simp only at h1 h4
      subst h1
      simp only [Loc.at]
      congr 2
      omega
    have hloc : ∀ g k, r = .thread (g, k) → LocalAt L g a → False := by
      rintro g k rfl ⟨o, hl, ho⟩
      have hg : g < L.threads := by
        rcases hi with ⟨bs, ⟨pc, he⟩, -⟩ | ⟨bs, ⟨pc, he⟩, -⟩ | ⟨o, n, pc, he⟩ <;>
          exact Frame.lt_of_get hX he
      apply hp.localMemory.2.2 g hg (o + y) (by omega)
      rw [← hn, hl]
      simp only [Loc.at, Nat.add_assoc]
    cases w with
    | true =>
      rcases outside_write hp hX hFw hi hs with hg | ⟨g, k, hr, h⟩
      · exact hp.outputs _ (global_write_region hp hX hFw hi hc hg) hn
      · exact hloc g k hr h
    | false =>
      rcases outside_read hp hX hFw hi hs with ⟨hz, h⟩ | ⟨g, k, hr, h⟩ | ⟨i, s, hcp, rfl⟩ | ⟨hz, h⟩
      · rcases h with ⟨i, hi', hl⟩ | ⟨i, hi', hl⟩ | ⟨i, hi', q, hq, hl⟩
        · rw [hl] at hn
          exact hval (hp.cuQ i hi') (by rw [hz] at hy; exact hy) hn
        · rw [hl] at hn
          exact hval (hp.usedK i hi') (by rw [hz] at hy; exact hy) hn
        · rw [hl] at hn
          exact hval (hp.pageBytes i hi' q hq) (by rw [hz] at hy; exact hy) hn
      · exact hloc g k hr h
      · obtain ⟨page, hpg, h, hh, rw', hr, d, hd, z, hz, hl⟩ := hS i s _ hcp hc
        obtain ⟨h1, h2⟩ := hp.kvBytes page hpg h hh rw' hr d hd
        rcases hl with hl | hl <;> rw [hl] at hn
        · exact hval h1 hz hn
        · exact hval h2 hz hn
      · rw [hz] at hy
        obtain rfl : y = 0 := by omega
        change m a.loc = none at hn
        rcases h with ⟨q, hq, h, hh, d, hd, z, hz, hl⟩ | ⟨q, hq, h, hh, d, hd, z, hz, hl⟩ <;>
          rw [hl] at hn
        · exact hval (hp.qBytes q hq h hh d hd) hz hn
        · refine hval (hp.biasBytes q hq h hh d hd) ?_ hn
          cases p.bias q h d <;> exact hz
  · obtain ⟨ev, he, hm⟩ := Frame.usesMbar_mbarOf hu
    obtain ⟨h, i⟩ := e
    have hh := Frame.lt_of_get hX he
    obtain ⟨j, c, hinit⟩ : ∃ j c, X.MbInit j o c := by
      by_cases hi : ∃ c, ev.kind = .mbInit o c
      · obtain ⟨c, hc⟩ := hi
        obtain ⟨pc, kd⟩ := ev
        simp only at hc
        subst hc
        exact ⟨_, c, pc, he⟩
      · have hub : ∀ f, ev.kind ≠ .ub f := by
          obtain ⟨pc, kd⟩ := ev
          rintro f rfl
          simp only [Frame.MbarOf] at hm
        obtain ⟨σ, n, hσ, -, hJ, hinv, hev⟩ := ev_open hp hX hFw he hub
        obtain ⟨j, c, hj, -⟩ := use_pub hp hX hFw hh he hσ hJ hinv hev hm
          fun c h => hi ⟨c, h⟩
        exact ⟨j, c, hj⟩
    obtain ⟨pcj, hj⟩ := hinit
    have hjl := Frame.lt_of_get hX (g := j.1) (k := j.2) hj
    obtain ⟨-, q, -, -, -, -, rfl, -⟩ := init_event hp hX hFw (h := j.1) (k := j.2) hjl hj
    have hq := initOff_apart q
    obtain ⟨y, hy, rfl⟩ := hcov hc
    simp only at hy
    refine hp.shared.2.2 (j.1 / L.block) (cta_lt hp hjl rfl) (initOff q + y) (by omega) ?_
    rw [← hn]
    simp only [Loc.at, Nat.add_assoc]

end

end
end PTX.Kernels.TmlFa4Fwd.Proof
