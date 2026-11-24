-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.WkWarpBar
public import Kernels.InklingRelDecode.Proof.Interface.WvAnchor

@[expose] public section

/-!
# The warp barriers of an MMA lane, counted by its state

The MMA warp's iteration `i` has the warp barriers `qkBar`, `qkBar2` of its QK half when `i < n`
and `pvBar`, `pvBar2` of its PV half when `i ≥ 1`; after the loop it has `finBar`. So before the
top of iteration `i ≥ 1` a lane has made `top i = 4 i - 2` of them (`2` in iteration 0, `4` in
each later one), and `wbM d` is the count before an MMA state `d` (`mma_wb_inv`). Before the role's
entry (`setMaxReg`) the lane has made none: a warp barrier is a loader or MMA state's
(`Interface.warpBar_event_state`), the loader is warp 6's (`roleWarp_inv`), and an MMA state before
the entry would have its own entry before it (`Rd.mma_back`, `Rd.mma_entry_unique`).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Wm
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof
open PTX.Kernels.InklingRelDecode.Proof.Interface PTX.Kernels.InklingRelDecode.Proof.Ledger

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

/-- The warp barriers before the top of iteration `i`. -/
def top (i : Nat) : Nat := 4 * i - 2

/-- The warp barriers of the QK half of the state's iteration: two when it runs. -/
def qkB (d : Mma.D) : Nat := if d.i < d.n then 2 else 0

/-- **The warp barriers before an MMA state.** -/
def wbM (d : Mma.D) : Nat :=
  match d.site with
  | .setMaxReg | .ldNum | .bar0 => 0
  | .qkBar => top d.i
  | .kvWait | .qkShfl | .qkBar2 | .qkSkip => top d.i + 1
  | .qkElect | .qk _ | .qkCommit => top d.i + 2
  | .pvBar => top d.i + qkB d
  | .pWait | .pvShfl | .pvBar2 | .pvSkip => top d.i + qkB d + 1
  | .pvElect | .pv _ | .pvCommit1 | .pvCommit2 => top d.i + qkB d + 2
  | .finBar => 4 * d.i - 4
  | .finElect | .finCommit | .bar1 | .setMaxRegInc => 4 * d.i - 4 + 1

/-- The warp-barrier bit of an MMA site. -/
def wbB (s : Mma.Site) : Nat := if s.isWb then 1 else 0

/-- **One step of the MMA lane** adds the warp-barrier bit of the site. -/
theorem wbM_next {d0 d : Mma.D} {e : Event} (hI : Mma.Inv d0)
    (hn : Mma.next L g d0 e = some (some d)) : wbM d = wbM d0 + wbB d0.site := by
  obtain ⟨s, i, n, tm, pro⟩ := d0
  have hq := hI.qk
  have hp := hI.pv
  have hpr := hI.pre
  simp only at hq hp hpr
  cases s <;>
    simp only [Mma.next, Mma.iterNext, Mma.afterQk, Mma.start, Mma.qkNext, Mma.pvNext] at hn <;>
    (repeat' split at hn) <;>
    first
    | (simp at hn; done)
    | (obtain rfl := Option.some.inj (Option.some.inj hn)
       simp_all [wbM, wbB, top, qkB, Mma.Site.isWb, Mma.QkSite, Mma.PvSite, Mma.PreSite]
       done)
    | (obtain rfl := Option.some.inj (Option.some.inj hn)
       simp_all [wbM, wbB, top, qkB, Mma.Site.isWb, Mma.QkSite, Mma.PvSite, Mma.PreSite]
       (repeat' split) <;> omega)

/-- The event at an MMA state has the site's shape. -/
theorem mma_ev_shape (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) {k : Nat} {e : Event} {d : Mma.D} {P : Loader.Pro}
    (he : X.get (g, k) = some e) (hσ : St Q L X g k = some (some (.w (.mma d P)))) :
    EvW.MmShape L g d e := by
  have hg : g < L.threads := Frame.lt_of_get hX he
  obtain ⟨u, hF⟩ := fired_cont hX hf hg he hσ (by simp [ExitState])
  obtain ⟨t, hgd, hfire⟩ := hF
  exact EvW.mma_shape hpre hg (d := d) (P := P) (u := u) ⟨t, ⟨hgd.1, hgd.2.2⟩, hfire⟩

/-- The event of an MMA state is a warp barrier exactly at a warp-barrier site. -/
theorem wbM_event (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) {k : Nat} {e : Event} {d : Mma.D} {P : Loader.Pro}
    (he : X.get (g, k) = some e) (hσ : St Q L X g k = some (some (.w (.mma d P)))) :
    (if Execution.isWarpBar e then 1 else 0) = wbB d.site := by
  have hsh := mma_ev_shape hpre hX hf he hσ
  unfold EvW.MmShape at hsh
  obtain ⟨s, i, n, tm, pro⟩ := d
  cases s <;> simp only at hsh <;>
    first
    | (obtain ⟨_, rfl⟩ := hsh; rfl)
    | (obtain ⟨_, _, rfl⟩ := hsh; rfl)
    | (obtain ⟨_, _, rfl, -⟩ := hsh; rfl)
    | (obtain ⟨_, _, _, -, -, -, rfl⟩ := hsh; rfl)

/-- **No warp barrier of an MMA lane before its role's entry.** -/
theorem wbM_zero (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hR : RoleReads L X) {k0 : Nat} {d0 : Mma.D}
    {P0 : Loader.Pro} (hk0 : k0 < (X.tr g).length)
    (h0 : St Q L X g k0 = some (some (.w (.mma d0 P0)))) (hs0 : d0.site = .setMaxReg) :
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
    ⟨d, P, hσ, -⟩ | ⟨d, P, hσ, -⟩
  · have h7 := roleWarp_inv hf.roleWarp k0 _ hk0.le h0
    have h6 := roleWarp_inv hf.roleWarp j _ hjl.le hσ
    simp only [RoleWarp, roleWarp] at h6 h7
    omega
  · obtain ⟨k1, d1, hk1, hσ1, hs1, -⟩ := Rd.mma_back hX hf j hjl hσ
    have := Rd.mma_entry_unique hpre hX hf hR (by omega) hk0 hσ1 hs1 h0 hs0
    omega

/-- **The warp barriers before an MMA state**, at an index up to the trace's length. -/
theorem mma_wb_inv (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hR : RoleReads L X) :
    ∀ k, k ≤ (X.tr g).length → ∀ {d : Mma.D} {P : Loader.Pro},
      St Q L X g k = some (some (.w (.mma d P))) → d.site ≠ .setMaxReg →
      warpBars X g k = wbM d := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk d P hσ hs
    obtain ⟨k0, e, d0, hadj, -, he, hσ0, hn⟩ := Wv.mma_pred_le hX hk hσ hs
    have hk0 : k0 < (X.tr g).length := by omega
    have hI0 : Mma.Inv d0 := mma_inv_at hX hf hk0 hσ0
    have ih0 : warpBars X g k0 = wbM d0 := by
      by_cases h0 : d0.site = .setMaxReg
      · rw [wbM_zero hpre hX hf hR hk0 hσ0 h0]
        simp [wbM, h0]
      · exact ih k0 (by omega) (by omega) hσ0 h0
    have hstep := wbM_next hI0 hn
    have hev := wbM_event hpre hX hf he hσ0
    have hsucc : warpBars X g k = warpBars X g k0 + (if Execution.isWarpBar e then 1 else 0) := by
      subst hadj
      unfold warpBars
      have he' : (X.tr g)[k0]? = some e := he
      rw [List.take_add_one, he', Option.toList_some, List.countP_append]
      simp
    rw [hsucc, hev, ih0, hstep]

end
end PTX.Kernels.InklingRelDecode.Proof.Wm
