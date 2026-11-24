-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.WkWarpBar
public import Kernels.InklingRelDecode.Proof.Protocol.LpCount

@[expose] public section

/-!
# The warp barriers of a loader thread, counted by its state

A loader iteration has five warp barriers (`wb0` … `wb4`). `wbOff` is the number of them before a
site of the loop, in its iteration. Before the loop's anchor (`bar0`) a loader thread has made no
warp barrier: a warp barrier is a loader or MMA state's (`Interface.warpBar_event_state`), the MMA
role is warp 7's and the loader's warp 6's (`roleWarp_inv`), and a loader warp-barrier state before
the anchor would have its own anchor before it (`Lp.loader_bar0_back`, `loader_bar0_unique`).
So at a loader state of the loop with iteration counter `i`, the warp barriers before it are
`5 (i - num_pre) + wbOff site` (`wb_inv`, written without subtraction).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Wk
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof
open PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX.Kernels.InklingRelDecode.Proof.Lp (PreSite)
open PTX.Kernels.InklingRelDecode.Proof.Ledger

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

/-- `num_pre` of the thread's CTA. -/
abbrev np (Q : Params) (L : Launch) (g : Nat) : Nat :=
  ProA.numPre Q (ProA.cta L g .z) (ProA.cta L g .x)

/-- The warp barriers of a loader iteration before the site. -/
def wbOff : Loader.Site → Nat
  | .arrive | .ldb0 | .wb1 => 1
  | .el0 | .cp0a | .cp0b | .wb2 => 2
  | .el1 | .cp1a | .cp1b | .ldb1 | .wb3 => 3
  | .el2 | .cp2a | .cp2b | .wb4 => 4
  | .el3 | .cp3a | .cp3b => 5
  | _ => 0

/-- The warp-barrier bit of a loader site. -/
def wbB (s : Loader.Site) : Nat := if s.isWb then 1 else 0

/-- **One step of the loader in the loop** adds the warp-barrier bit of the site. -/
theorem wb_next {d0 d : Loader.D} {e : Event} (hn : Loader.next L g d0 e = some (some d))
    (hp : ¬ PreSite d0.site) :
    5 * d.i + wbOff d.site = 5 * d0.i + wbOff d0.site + wbB d0.site := by
  obtain ⟨s, pro, i, n, p0, p1, ln⟩ := d0
  simp only [PreSite, not_or] at hp
  obtain ⟨h1, h2, h3⟩ := hp
  cases s <;> simp only [Loader.next, Loader.afterIter] at hn <;> (repeat' split at hn) <;>
    first
    | (simp at h1; done) | (simp at h2; done) | (simp at h3; done)
    | (simp at hn; done)
    | (obtain rfl := Option.some.inj (Option.some.inj hn)
       simp_all [wbOff, wbB, Loader.Site.isWb]; done)
    | (obtain rfl := Option.some.inj (Option.some.inj hn)
       simp_all [wbOff, wbB, Loader.Site.isWb]; omega)

/-- The event of a loader state is a warp barrier exactly at a warp-barrier site. -/
theorem wb_event (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) {k : Nat} {e : Event} {d : Loader.D} {P : Loader.Pro}
    (he : X.get (g, k) = some e) (hσ : St Q L X g k = some (some (.w (.loader d P)))) :
    (if Execution.isWarpBar e then 1 else 0) = wbB d.site := by
  have hsh := Lp.loader_ev_shape hpre hX hf he hσ
  unfold EvW.LdShape at hsh
  obtain ⟨s, pro, i, n, p0, p1, ln⟩ := d
  cases s <;> simp only at hsh <;>
    first
    | (obtain ⟨_, rfl⟩ := hsh; rfl)
    | (obtain ⟨_, _, rfl, -⟩ := hsh; rfl)

/-- **No warp barrier of a loader thread before the anchor of its loop.** -/
theorem wb_zero (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hR : RoleReads L X) {k0 : Nat} {d0 : Loader.D}
    {P0 : Loader.Pro} (hk0 : k0 < (X.tr g).length)
    (h0 : St Q L X g k0 = some (some (.w (.loader d0 P0)))) (hs0 : d0.site = .bar0) :
    warpBars X g k0 = 0 := by
  have hg : g < L.threads := by
    obtain ⟨e, he⟩ : ∃ e, X.get (g, k0) = some e := ⟨_, List.getElem?_eq_getElem hk0⟩
    exact Frame.lt_of_get hX he
  unfold warpBars
  rw [List.countP_eq_zero]
  intro e hmem hwb
  obtain ⟨j, hj, hje⟩ := List.getElem_of_mem hmem
  rw [List.length_take] at hj
  rw [List.getElem_take] at hje
  have hjl : j < (X.tr g).length := by omega
  have he : X.get (g, j) = some e := by
    show (X.tr g)[j]? = some e
    rw [List.getElem?_eq_getElem hjl, hje]
  rcases (warpBar_event_state hpre hX hf.sound hf.tracked hg he hwb).1 with
    ⟨d, P, hσ, hs⟩ | ⟨d, P, hσ, -⟩
  · have hp : ¬ PreSite d.site := by
      rintro (h | h | h) <;> rw [h] at hs <;> cases hs
    obtain ⟨k1, d1, hk1, hσ1, hs1, -⟩ := Lp.loader_bar0_back hX hf.ldRng j hjl hσ hp
    have := Lp.loader_bar0_unique hpre hX hf hR (by omega) hk0 hσ1 hs1 h0 hs0
    omega
  · have h6 := roleWarp_inv hf.roleWarp k0 _ hk0.le h0
    have h7 := roleWarp_inv hf.roleWarp j _ hjl.le hσ
    simp only [RoleWarp, roleWarp] at h6 h7
    omega

/-- **The warp barriers before a loader state of the loop**: `5 (i - num_pre) + wbOff site`. -/
theorem wb_inv (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hR : RoleReads L X) (hp : NumPreRead Q L X) :
    ∀ k, k < (X.tr g).length → ∀ {d : Loader.D} {P : Loader.Pro},
      St Q L X g k = some (some (.w (.loader d P))) → ¬ PreSite d.site →
      warpBars X g k + 5 * np Q L g = 5 * d.i + wbOff d.site := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk d P hσ hnp
    by_cases hb : d.site = .bar0
    · have h0 := wb_zero hpre hX hf hR hk hσ hb
      have hi : d.i = np Q L g := Interface.Lk.ipre_inv hpre hX hf hp k _ hσ (.inr hb)
      rw [h0, hi, hb]
      simp [wbOff]
    · obtain ⟨k0, e, d0, hadj, -, he, hσ0, hn⟩ :=
        Lp.loader_state_pred_adj hX hk hσ (fun h => hnp (.inl h))
      obtain ⟨-, -, -, h4, h5, h6⟩ := Lp.next_pre hn
      have hp0 : ¬ PreSite d0.site := by
        rintro (h | h | h)
        · exact hnp (.inr (.inl (h4 h)))
        · exact hnp (.inr (.inr (h5 h)))
        · exact hb (h6 h)
      have ih0 := ih k0 (by omega) (by omega) hσ0 hp0
      have hstep := wb_next hn hp0
      have hev := wb_event hpre hX hf he hσ0
      have hsucc : warpBars X g k = warpBars X g k0 + (if Execution.isWarpBar e then 1 else 0) := by
        subst hadj
        unfold warpBars
        have he' : (X.tr g)[k0]? = some e := he
        rw [List.take_add_one, he', Option.toList_some, List.countP_append]
        simp
      rw [hsucc, hev]
      omega

end
end PTX.Kernels.InklingRelDecode.Proof.Wk
