-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.Lk5WTrace
public import Kernels.InklingRelDecode.Proof.Interface.Lk5VChain

@[expose] public section

/-!
# The two lanes of a row share their numbers and `alpha`, by iteration

For the lane `g` and its partner `x` (`x % 256 = (g % 256) ^ 16`, same warp), without the lockstep:

* `wit_recv`: at their exchanges of the row maximum of one iteration each receives the other's
  maximum (the source lane's state is found by the count of shuffles, `sm_shfl_peer_d`, and is the
  thread's only state there, `sm_shfl_unique`);
* `pair_iter`: their states at `shfl5` of one iteration have the same shared numbers `Sm.pf`, by
  induction on the iteration (the first states: `entry_pf`; the step: `Sm.afterS_pf`, on any
  words);
* `al_pair`: their states between the stage's second exchange and the update of one iteration have
  the same `alpha` (`Sm.afterS_al_pair`, on any words).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Interface.Lk
open PTX PTX.Proof PTX.Flow PTX.Assumption PTX.Kernels.InklingRelDecode.Proof.Sm

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **What the exchange of the row maximum received**: the partner's state at `shfl5` of the same
iteration, the only one. -/
theorem recv_partner (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) {g x k0 j0 : Nat} {d0 dp0 : Sm.D} {r : Value} {o : Bool}
    {ep : Event} (hg : g < L.threads) (hw : SameWarp L g x)
    (hx : x % L.block = (g % L.block) ^^^ 16)
    (hσ0 : St Q L X g k0 = some (some (.d (.sm d0)))) (hs0 : d0.site = .shfl5)
    (he0 : X.get (g, k0) = some ⟨d0.site.pc, .shfl .bfly d0.ownW 16 31 r o⟩)
    (hσp : St Q L X x j0 = some (some (.d (.sm dp0)))) (hsp : dp0.site = .shfl5)
    (hip : dp0.i = d0.i) (hep : X.get (x, j0) = some ep) :
    r = dp0.ownW := by
  have hb : L.block = 256 := hpre.block
  obtain ⟨recv, ok, x', j2, d2, he, -, hx', hσ2, hs2, hi2, hrecv, -, -, r2, o2, he2⟩ :=
    sm_shfl_peer_d hpre hX hf hb (fld := fun d => ownV fun k => (d.stg.fsv k).1) (k := 16)
      (by rw [hs0]; exact shflShape_5 L) hg he0 hσ0
  have hxx : x' = x := hx'.trans (partner_src hb hw hx)
  subst hxx
  have hr : r = recv := by
    have := he
    simp only [Event.mk.injEq, Kind.shfl.injEq] at this
    exact this.2.2.2.2.2.1
  have hj : j2 = j0 := sm_shfl_unique hpre hX hf hw.1.2.1 he2 (event_le hep) hσ2 hσp
    (by rw [hs2, hs0]; rfl) (hsp.trans (hs2.trans hs0).symm) (hip.trans hi2.symm)
  subst hj
  have hd : d2 = dp0 := by
    have := hσ2.symm.trans hσp
    simp only [Option.some.injEq, TSt.d.injEq, DComp.St.sm.injEq] at this
    exact this
  subst hd
  rw [hr, hrecv]

theorem partner_warp {g x : Nat} (hc : g / L.block = x / L.block) (hg : g < L.threads)
    (hx : x < L.threads) (hb : L.block = 256) (hp : x % L.block = (g % L.block) ^^^ 16) :
    SameWarp L g x := by
  refine ⟨⟨hg, hx, hc⟩, ?_⟩
  have h : ∀ T < 256, (T ^^^ 16) / 32 = T / 32 := by decide
  rw [hp, h _ (by rw [hb] at *; omega)]

/-- **The partners' states at `shfl5` of one iteration have the same shared numbers.** -/
theorem pair_iter (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hz : Rs.SmBaseZero Q L X) :
    ∀ i, ∀ {g x k j : Nat} {d dp : Sm.D} {e e' : Event}, g < L.threads → x < L.threads →
      g / L.block = x / L.block → x % L.block = (g % L.block) ^^^ 16 →
      X.get (g, k) = some e → X.get (x, j) = some e' →
      St Q L X g k = some (some (.d (.sm d))) → St Q L X x j = some (some (.d (.sm dp))) →
      d.site = .shfl5 → dp.site = .shfl5 → d.i = i → dp.i = i → pf d = pf dp := by
  have hb : L.block = 256 := hpre.block
  intro i
  induction i with
  | zero =>
    intro g x k j d dp e e' hg hx hc hp he he' hσ hσ' hs hs' hi hi'
    have hl : Late d.site = false := by rw [hs]; rfl
    have hl' : Late dp.site = false := by rw [hs']; rfl
    obtain ⟨k1, d1, hk1, h1, h2, h3⟩ := (wInv hX hf hg k (event_le he) hσ).1 hl hi
    obtain ⟨j1, d2, hj1, h1', h2', h3'⟩ := (wInv hX hf hx j (event_le he') hσ').1 hl' hi'
    rw [h3, h3']
    exact entry_pf hf hz hg hx hc (by have := event_le he; omega)
      (by have := event_le he'; omega) h1 h1' h2 h2'
  | succ i ih =>
    intro g x k j d dp e e' hg hx hc hp he he' hσ hσ' hs hs' hi hi'
    have hl : Late d.site = false := by rw [hs]; rfl
    have hl' : Late dp.site = false := by rw [hs']; rfl
    obtain ⟨k0, d0, r, o, -, h1, h2, h3, h4, h5, h6⟩ :=
      (wInv hX hf hg k (event_le he) hσ).2.1 hl (by omega)
    obtain ⟨j0, dp0, rp, op, -, h1', h2', h3', h4', h5', h6'⟩ :=
      (wInv hX hf hx j (event_le he') hσ').2.1 hl' (by omega)
    rw [hi, Nat.add_sub_cancel] at h3
    rw [hi', Nat.add_sub_cancel] at h3'
    have hw := partner_warp hc hg hx hb hp
    have hpf := ih hg hx hc hp h4 h4' h1 h1' h2 h2' h3 h3'
    have hr := recv_partner hpre hX hf hg hw hp h1 h2 h4 h1' h2' (h3'.trans h3.symm) h4'
    have hrp := recv_partner hpre hX hf hx (sameWarp_symm hw) (partner_symm hp) h1' h2' h4' h1
      h2 (h3.trans h3'.symm) h4
    rw [h6, h6', hr, hrp]
    exact pfU_congr (Sm.afterS_pf L hpf h5 h5')

/-- **The partners' `alpha` from the stage's second exchange to the update of an iteration.** -/
theorem al_pair (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hz : Rs.SmBaseZero Q L X) {g x k j : Nat} {d dp : Sm.D}
    (hg : g < L.threads) (hx : x < L.threads) (hc : g / L.block = x / L.block)
    (hp : x % L.block = (g % L.block) ^^^ 16) (hk : k ≤ (X.tr g).length)
    (hj : j ≤ (X.tr x).length) (hσ : St Q L X g k = some (some (.d (.sm d))))
    (hσ' : St Q L X x j = some (some (.d (.sm dp)))) (hl : Late d.site = true)
    (hq : PostU d.site = false) (hl' : Late dp.site = true) (hq' : PostU dp.site = false)
    (hi : dp.i = d.i) : dp.stg.al = d.stg.al ∧ dp.stg.alr = d.stg.alr := by
  have hb : L.block = 256 := hpre.block
  obtain ⟨k0, d0, r, o, -, h1, h2, h3, h4, h5, -, h6, h7⟩ := (wInv hX hf hg k hk hσ).2.2.1 hl hq
  obtain ⟨j0, dp0, rp, op, -, h1', h2', h3', h4', h5', -, h6', h7'⟩ :=
    (wInv hX hf hx j hj hσ').2.2.1 hl' hq'
  have hw := partner_warp hc hg hx hb hp
  have hpf := pair_iter hpre hX hf hz d.i hg hx hc hp h4 h4' h1 h1' h2 h2' h3 (h3'.trans hi)
  have hr := recv_partner hpre hX hf hg hw hp h1 h2 h4 h1' h2' (h3'.trans (hi.trans h3.symm)) h4'
  have hrp := recv_partner hpre hX hf hx (sameWarp_symm hw) (partner_symm hp) h1' h2' h4' h1
    h2 (h3.trans (hi.symm.trans h3'.symm)) h4
  unfold pf at hpf
  simp only [Prod.mk.injEq] at hpf
  obtain ⟨ha, hr'⟩ := Sm.afterS_al_pair L (g := g) (g' := x) hpf.1 hpf.2.1 h5 h5'
  rw [h6, h7, h6', h7', hr, hrp]
  exact ⟨ha.symm, hr'.symm⟩

end
end PTX.Kernels.InklingRelDecode.Proof.Interface.Lk
