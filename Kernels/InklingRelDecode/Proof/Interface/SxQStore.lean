-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.LpQTile

@[expose] public section

/-!
# A query store is before every MMA of its CTA, in any execution

`Lp.stq_before_mmaRead` orders a query store before the MMAs of its CTA from the store thread's
fence `fnc1` and first barrier-1 event. This file finds them for a store event of any consistent
execution, complete or not:

* `stq_fence`: from a query store at site `i` the thread steps through the remaining stores to the
  fence `fnc1`, `32 - i` events later and still before its first barrier-1 event; the event there
  is the `fence.proxy.async` of the CTA's shared memory. Each step has its event, because it is
  before the barrier-1 event (`lt_bar`);
* `stq_before_mma`: the MMA thread has made a barrier-1 event, so the store's thread has made its
  first one (`bar1_of_mma`), and `stq_proxyBefore` orders the store before the MMA's
  issue through the fence.

`stq_addr` is the address of a query store's byte (`ProA.shape_stq`, `ProA.qStoreBase_form`).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Lp
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof
open PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX.Kernels.InklingRelDecode.Proof.Ledger

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

theorem chainSite_ne_bar18 : ∀ j ≤ 32, ProA.chainSite j ≠ .bar18 := by decide

/-- **From a query store to the fence `fnc1`**, before the thread's first barrier-1 event. -/
theorem stq_fence (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hT : ∀ g < L.threads, (threadCode L g Q).TmplOk)
    (hg : g < L.threads) (hdef : g % L.block < 128) {k i i0 pc0 : Nat} {dt : ProA.Dat}
    (hi : i < 32) (hσ : St Q L X g k = some (some (.d (.pro ⟨ProA.stqSite i, dt⟩))))
    (hbar : X.IsBarrier (g, i0) 1 none pc0) :
    k + (32 - i) < i0 ∧
      X.IsProxyFence (g, k + (32 - i)) (.async (some (.shared .cta))) none := by
  have hi0 : i0 < (X.tr g).length :=
    (List.getElem?_eq_some_iff.mp (show (X.tr g)[i0]? = _ from hbar)).1
  have chain : ∀ n, n ≤ 32 - i →
      St Q L X g (k + n) = some (some (.d (.pro ⟨ProA.chainSite (i + n), dt⟩))) ∧
        k + n < i0 := by
    intro n
    induction n with
    | zero =>
      intro _
      have h0 : St Q L X g (k + 0) =
          some (some (.d (.pro ⟨ProA.chainSite (i + 0), dt⟩))) := by
        simpa [ProA.chainSite_stq hi] using hσ
      exact ⟨h0, lt_bar hpre hX hf hdef hbar h0 (chainSite_ne_bar18 _ (by omega))⟩
    | succ n ih =>
      intro hn
      obtain ⟨h1, hlt⟩ := ih (by omega)
      have hst : ProA.chainSite (i + n) = ProA.stqSite (i + n) :=
        ProA.chainSite_stq (by omega)
      rw [hst] at h1
      have h2 := pro_step (by omega) h1 (by
        rw [← hst]; exact chainSite_ne_bar18 _ (by omega))
        (fun e => ProA.next_stq_fwd (by omega) dt e)
      rw [show k + n + 1 = k + (n + 1) by omega, show i + n + 1 = i + (n + 1) by omega] at h2
      exact ⟨h2, lt_bar hpre hX hf hdef hbar h2 (chainSite_ne_bar18 _ (by omega))⟩
  obtain ⟨h32, hlt⟩ := chain (32 - i) le_rfl
  rw [show i + (32 - i) = 32 by omega, ProA.chainSite_fnc1] at h32
  obtain ⟨e, he⟩ : ∃ e, X.get (g, k + (32 - i)) = some e :=
    ⟨_, List.getElem?_eq_getElem (show k + (32 - i) < (X.tr g).length by omega)⟩
  obtain ⟨pcf, hev⟩ := fnc_event hX hf.sound hT hg he h32 (Or.inr rfl)
  exact ⟨hlt, ⟨pcf, by rw [he, hev]⟩⟩

/-- **A query store is before the issue of every MMA of its CTA**, through its fence, for every
shared byte of the CTA (`ProxyBefore`). -/
theorem stq_before_mma (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hT : ∀ g < L.threads, (threadCode L g Q).TmplOk)
    (hR : RoleReads L X) (hE : Bar1Exits L X) (hg : g < L.threads)
    (hdef : g % L.block < 128) {k i : Nat} {dt : ProA.Dat} (hi : i < 32)
    (hσ : St Q L X g k = some (some (.d (.pro ⟨ProA.stqSite i, dt⟩))))
    {m : EvId} {dm : Mma.D} {P : Loader.Pro} (hml : m.1 < L.threads)
    (hn : m.2 < (X.tr m.1).length) (hm : St Q L X m.1 m.2 = some (some (.w (.mma dm P))))
    (hmc : m.1 / L.block = g / L.block) {l : Loc} (hls : l.space = .shared)
    (hlc : l.cta = g / L.block) : ProxyBefore L X (g, k) m l := by
  have hb1 := mma_b1 hpre hX hf hR hn.le hm
  obtain ⟨i0, pc', hfi, hc0⟩ := bar1_of_mma hpre hX hf hR hE hn hm hmc.symm
  obtain ⟨hlt, hfence⟩ := stq_fence hpre hX hf hT hg hdef hi hσ hfi
  exact stq_proxyBefore hpre hX hE hg hfi hc0 hlt (by omega) hfence hml hmc hn hb1 hls hlc

/-- **The address of a query store**: a store at site `i` of a default thread `g` covers the four
bytes of word `i % 4` of store `i / 4` at the thread's swizzled row. -/
theorem stq_addr (hX : Consistent L kernel asms mem0 X) (hf : ThreadFacts Q L mem0 X)
    (hsb : ProA.SbRoom L) (hg : g < L.threads) (hdef : g % L.block < 128) {k pc i : Nat}
    {dt : ProA.Dat} {a : Acc} {bs : List Byte} (hi : i < 32)
    (he : X.get (g, k) = some ⟨pc, .wr a bs⟩)
    (hσ : St Q L X g k = some (some (.d (.pro ⟨ProA.stqSite i, dt⟩)))) :
    a.loc = ⟨.shared, g / L.block, L.sharedBase + 196608 + 2048 * ProA.qGroup (i / 4) +
      ProA.qSwz (ProA.tidOf L g) + 4 * (i % 4)⟩ ∧ a.size = 4 := by
  obtain ⟨u, hF⟩ := fired_cont hX hf hg he hσ (by simp [ExitState])
  have hm : i / 4 < 8 := by omega
  have hw : i % 4 < 4 := by omega
  obtain ⟨v, -, hev⟩ := ProA.shape_stq hm hw (fired_pro hF) (by simp only; congr 1; omega)
  simp only [Event.mk.injEq, Kind.wr.injEq] at hev
  obtain ⟨-, hfp, -⟩ := hev
  rw [hfp]
  simp only [EvD.wordAcc]
  rw [ProA.qStoreBase_form L g dt hdef hsb hm]
  exact ⟨rfl, trivial⟩

end
end PTX.Kernels.InklingRelDecode.Proof.Lp
