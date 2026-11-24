-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Protocol.SxTClass
public import Kernels.InklingRelDecode.Proof.Protocol.FrLdL

@[expose] public section

/-!
# The softmax region's accesses to the scratch words, pairwise

The softmax region of a default thread touches the scratch `[sharedBase + 212992,
sharedBase + 213008)` twice per iteration: `store10` writes the word of its warp, then `bar23`,
then `ldL` reads the word `tid % 4` (`SmAcc`). Two such accesses of two threads of one CTA that
conflict are ordered, or are the stores of one warp in one iteration, which write the same value
(`sm_pair`):

* two stores of iterations `j < i`: the first is before the other's thread's `bar23` of iteration
  `j`, which precedes its store (`Lk.earlier_before`);
* two stores of one iteration on one word: the warp's lanes store one number (`StoreWord`), so the
  bytes and the footprint agree (`SameValueWrites`);
* a store of iteration `j` and a load of iteration `i ≥ j`: the store is before the loading
  thread's `bar23` of iteration `j` (`store_before`, the argument of `Lk.earlier_before` with any
  later state of the loading thread);
* a load of iteration `i` and a store of iteration `j > i`: `Lk.later_after`.

The barrier-0 facts (`B0At`, `B0Pos`) and `StoreWord` are premises here; `sm_facts` gives them
from `ScratchIt` of every iteration and `Rs.SmBaseZero`.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Safety
open PTX PTX.Proof PTX.Flow PTX.Assumption PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX.Kernels.InklingRelDecode.Proof.Interface.Lk PTX.Kernels.InklingRelDecode.Proof.Sm

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- An access of the softmax region to the scratch: a `store10` (a write) or an `ldL` (a read). -/
def SmAcc (Q : Params) (L : Launch) (X : Execution) (g k : Nat) (w : Bool) : Prop :=
  ∃ d : Sm.D, St Q L X g k = some (some (.d (.sm d))) ∧
    ((d.site = .store10 ∧ w = true) ∨ (d.site = .ldL ∧ w = false))

/-- A thread's write intent is a write event. -/
theorem wr_of_intent (hX : Consistent L kernel Interface.asms mem0 X) {i : EvId} {a : Acc}
    (h : X.Intent (.thread i) a true) : ∃ pc bs, X.get i = some ⟨pc, .wr a bs⟩ := by
  rcases h with ⟨bs, -, h⟩ | ⟨bs, ⟨pc, h⟩, -⟩ | ⟨o, n, pc, h⟩
  · cases h
  · exact ⟨pc, bs, h⟩
  · exact absurd h (no_rmw hX)

/-- A thread's read intent is a read event. -/
theorem rd_of_intent (hX : Consistent L kernel Interface.asms mem0 X) {i : EvId} {a : Acc}
    (h : X.Intent (.thread i) a false) : ∃ pc bs, X.get i = some ⟨pc, .rd a bs⟩ := by
  rcases h with ⟨bs, ⟨pc, h⟩, -⟩ | ⟨bs, -, h⟩ | ⟨o, n, pc, h⟩
  · exact ⟨pc, bs, h⟩
  · cases h
  · exact absurd h (no_rmw hX)

/-- `SameValueWrites` is symmetric. -/
theorem svw_symm {e f : AsyncCopy.Ref} {a b : Acc} (h : SameValueWrites X e f a b) :
    SameValueWrites X f e b a :=
  ⟨h.2.1, h.1, ⟨h.2.2.1.1.symm, h.2.2.1.2.symm⟩, fun bs bs' h1 h2 => (h.2.2.2 bs' bs h2 h1).symm⟩

theorem rank_ldL {d : Sm.D} (hs : d.site = .ldL) : d.rank = 64 * d.i + 18 := by
  simp [D.rank, hs, Site.ord]

variable (hpre : Pre Q L mem0) (hX : Consistent L kernel Interface.asms mem0 X)
  (hf : ThreadFacts Q L mem0 X)
include hpre hX hf

/-- **A `store10` of iteration `j` is before every softmax state past `bar23` of iteration `j` of a
thread of its CTA**: the storing thread's `bar23` of iteration `j` follows its store and is in the
generation of the other thread's (`member23`). -/
theorem store_before {c j : Nat} (hP : B0Pos Q L X c j) {t a1 : Nat} {dt : Sm.D}
    (ht : t < L.threads) (htc : t / L.block = c)
    (hσt : St Q L X t a1 = some (some (.d (.sm dt)))) (ha1 : a1 < (X.tr t).length)
    (hr : 64 * j + 17 < dt.rank)
    {μ kμ : Nat} {dμ : Sm.D} (hμ : μ < L.threads) (hμc : μ / L.block = c)
    (hσμ : St Q L X μ kμ = some (some (.d (.sm dμ)))) (hkμ : kμ < (X.tr μ).length)
    (hsμ : dμ.site = .store10) (hj : dμ.i = j) :
    baseCausality L X (μ, kμ) (t, a1) := by
  have htd := sm_default (by omega) hσt
  have hμd := sm_default (by omega) hσμ
  have hj1 : 1 ≤ j := by
    have := midOk_state kμ (by omega) hσμ (by rw [hsμ]; trivial)
    omega
  obtain ⟨b', db, hb'lt, hσb, hsb, hib⟩ := back23 hj1 a1 (by omega) hσt hr
  obtain ⟨aμ, dm, hσa, hsa, hia, hcnt, hgeta⟩ := member23 hpre hX hf hP ht htc hσb hsb hib
    (by omega) hμ hμc hμd
  have hka : kμ < aμ := by
    by_contra hc
    rcases Nat.lt_or_ge aμ kμ with h | h
    · have := rank_mono_m hpre hX hf.sound hσa kμ (by omega) (by omega) hσμ
      rw [rank_bar23 hsa, rank_store10 hsμ] at this
      omega
    · have hak : aμ = kμ := by omega
      subst hak
      rw [hσa] at hσμ
      simp only [Option.some.injEq, TSt.d.injEq, DComp.St.sm.injEq] at hσμ
      subst hσμ
      rw [hsa] at hsμ
      cases hsμ
  obtain ⟨eb, heb⟩ : ∃ e, (X.tr t)[b']? = some e := ⟨_, List.getElem?_eq_getElem (by omega)⟩
  have hevb := bar_event hpre hX hf ht heb hσb (by rw [hsb]; trivial)
  rw [hsb] at hevb
  have hgetb : X.get (t, b') = some ⟨Sm.Site.bar23.pc, .bar 0 (some 128) .sync⟩ := by
    rw [show X.get (t, b') = some eb from heb, hevb]
  exact Bar.bar128Causal hpre hX hf.sound hf.tracked hμ ht (by rw [hμc, htc]) hμd htd hgeta hgetb
    hcnt hka hb'lt ha1

/-- **A `store10` against a conflicting softmax access of another thread of its CTA**: ordered,
or the same value. -/
theorem store_vs (hB : ∀ c i, B0At Q L X c i) (hP : ∀ c i, B0Pos Q L X c i)
    (hW : ∀ c i, StoreWord Q L X c i) {g k g' k' : Nat} {a b : Acc} {wf : Bool}
    (hg : g < L.threads) (hg' : g' < L.threads) (hk : k < (X.tr g).length)
    (hk' : k' < (X.tr g').length) (hcta : g / L.block = g' / L.block)
    (hie : X.Intent (.thread (g, k)) a true) (hif : X.Intent (.thread (g', k')) b wf)
    (hov : a.Overlap b) {d : Sm.D} (hσ : St Q L X g k = some (some (.d (.sm d))))
    (hs : d.site = .store10) (h2 : SmAcc Q L X g' k' wf)
    (hS : ¬ SameValueWrites X (.thread (g, k)) (.thread (g', k')) a b) :
    baseCausality L X (g, k) (g', k') ∨ baseCausality L X (g', k') (g, k) := by
  have hgc' : g' / L.block = g / L.block := hcta.symm
  obtain ⟨d', hσ', hc2⟩ := h2
  rcases hc2 with ⟨hs', rfl⟩ | ⟨hs', rfl⟩
  · rcases lt_trichotomy d.i d'.i with hlt | heq | hgt
    · exact .inl (earlier_before hpre hX hf (hP _ d.i) hg' hgc' hσ' hk' hs' rfl hg rfl hσ hk hs
        rfl hlt)
    · exfalso
      apply hS
      obtain ⟨pc1, bs1, he1⟩ := wr_of_intent hX hie
      obtain ⟨pc2, bs2, he2⟩ := wr_of_intent hX hif
      obtain ⟨u1, hF1⟩ := fired_cont hX hf hg he1 hσ (by simp [ExitState])
      obtain ⟨u2, hF2⟩ := fired_cont hX hf hg' he2 hσ' (by simp [ExitState])
      obtain ⟨v1, hv1, hev1⟩ := shape_store10_val (ProA.sharedOk_of_pre hpre) (fired_sm hF1) hs
      obtain ⟨v2, hv2, hev2⟩ := shape_store10_val (ProA.sharedOk_of_pre hpre) (fired_sm hF2) hs'
      simp only [Event.mk.injEq, Kind.wr.injEq] at hev1 hev2
      obtain ⟨-, rfl, rfl⟩ := hev1
      obtain ⟨-, rfl, rfl⟩ := hev2
      have hd1 := sm_default hk.le hσ
      have hd2 := sm_default hk'.le hσ'
      have hr1 : g % L.block / 32 < 4 := by omega
      have hr2 : g' % L.block / 32 < 4 := by omega
      have hrr : g' % L.block / 32 = g % L.block / 32 := by
        obtain ⟨l, ⟨-, -, h1, h2⟩, ⟨-, -, h3, h4⟩⟩ := hov
        simp only [EvD.wordAcc] at h1 h2 h3 h4
        omega
      obtain ⟨w, -, hw⟩ := hW (g / L.block) d.i _ hr1
      have hc1 := hw hg rfl rfl hσ hs rfl
      have hc2 := hw hg' hgc' hrr hσ' hs' heq.symm
      rw [hc1] at hv1
      rw [hc2, hv1] at hv2
      cases hv2
      exact same_value hX he1 he2 (by simp [EvD.wordAcc, hcta, hrr]) rfl
    · exact .inr (earlier_before hpre hX hf (hP _ d'.i) hg rfl hσ hk hs rfl hg' hgc' hσ' hk' hs'
        rfl hgt)
  · rcases Nat.lt_or_ge d'.i d.i with hgt | hle
    · obtain ⟨pc2, bs2, hrd2⟩ := rd_of_intent hX hif
      have hi1 : 1 ≤ d'.i := by
        have := midOk_state k' hk'.le hσ' (by rw [hs']; trivial)
        omega
      rcases Sv.pred_sm hk'.le hσ' with ⟨dt, rfl⟩ | ⟨k2, d2, e2, rfl, he2, hσ2, hn2⟩
      · simp [SmEntry.d0] at hs'
      obtain ⟨hs2, hi2⟩ := prev_ldL hn2 hs'
      exact .inr (later_after hpre hX hf (hB _ d'.i) (hP _ d'.i) hi1 hg' hgc' hσ2 hs2
        (by omega) hk' (fun h => by rw [hrd2] at h; simp at h) hg rfl hσ hk hs (by omega))
    · have hr : 64 * d.i + 17 < d'.rank := by rw [rank_ldL hs']; omega
      exact .inl (store_before hpre hX hf (hP _ d.i) hg' hgc' hσ' hk' hr hg rfl hσ hk hs rfl)

/-- **Two conflicting softmax accesses of two threads of one CTA are ordered**, but for the stores
of one warp in one iteration. -/
theorem sm_pair (hB : ∀ c i, B0At Q L X c i) (hP : ∀ c i, B0Pos Q L X c i)
    (hW : ∀ c i, StoreWord Q L X c i) {g k g' k' : Nat} {a b : Acc} {we wf : Bool}
    (hg : g < L.threads) (hg' : g' < L.threads) (hk : k < (X.tr g).length)
    (hk' : k' < (X.tr g').length) (hcta : g / L.block = g' / L.block)
    (hie : X.Intent (.thread (g, k)) a we) (hif : X.Intent (.thread (g', k')) b wf)
    (hw : we = true ∨ wf = true) (hov : a.Overlap b) (h1 : SmAcc Q L X g k we)
    (h2 : SmAcc Q L X g' k' wf)
    (hS : ¬ SameValueWrites X (.thread (g, k)) (.thread (g', k')) a b) :
    baseCausality L X (g, k) (g', k') ∨ baseCausality L X (g', k') (g, k) := by
  obtain ⟨d, hσ, ⟨hs, rfl⟩ | ⟨hs, rfl⟩⟩ := id h1
  · exact store_vs hpre hX hf hB hP hW hg hg' hk hk' hcta hie hif hov hσ hs h2 hS
  · obtain ⟨d', hσ', ⟨hs', rfl⟩ | ⟨hs', rfl⟩⟩ := id h2
    · exact (store_vs hpre hX hf hB hP hW hg' hg hk' hk hcta.symm hif hie hov.symm hσ' hs' h1
        (fun h => hS (svw_symm h))).symm
    · rcases hw with h | h <;> cases h

/-- **The barrier-0 facts and the scratch stores' values** from `ScratchIt` of every iteration and
`Rs.SmBaseZero`. -/
theorem sm_facts (hI : ∀ i, ScratchIt Q L X i) (hz : Rs.SmBaseZero Q L X) :
    (∀ c i, B0At Q L X c i) ∧ (∀ c i, B0Pos Q L X c i) ∧ (∀ c i, StoreWord Q L X c i) := by
  have hD : ∀ c j, DecAgree Q L X c j := decAgree_every hpre hX hf hI
  exact ⟨fun c _ => B0N.b0At_of hpre hX hf (fun j _ => hD c j),
    fun c _ => B0N.b0Pos_of hpre hX hf (fun j _ => hD c j), storeWord_all hpre hX hf hz⟩

end
end PTX.Kernels.InklingRelDecode.Proof.Safety
