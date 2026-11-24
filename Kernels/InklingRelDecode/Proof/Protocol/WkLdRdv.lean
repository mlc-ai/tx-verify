-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Kernel.Progress.Warp
public import Kernels.InklingRelDecode.Proof.Protocol.WkLdCount
public import Kernels.InklingRelDecode.Proof.Safety.Static
public import Kernels.InklingRelDecode.Proof.Protocol.LpEvents

@[expose] public section

/-!
# Every loader lane's poll precedes lane 0's arrival of the same block

Lane 0 of the loader warp (`ldThread c`) arrives on `kv_ready s` for the loader's `N`-th block of
slot `s` after its `bar.warp.sync` `wb0` of that iteration (`arrive_pred`). That warp barrier has a
partner in every lane `h` of the warp (`WarpBar.partner`; the masks are full,
`Interface.warpBar_mask`), with the same ordinal (`WarpBar.ordinal_eq`). The ordinal is a function
of the loader state (`wb_inv`: `5 (i - num_pre) + wbOff site`), so the partner is `h`'s own `wb0`
of the same iteration (`wb_site`), which follows `h`'s successful poll of `kv_empty s` for that
block (`wb0_pred`), the poll with `N` earlier ones (`Ring.loader_poll_exec`, `loader_arrive_exec`:
both are the loader's `N`-th block of slot `s`). So in the dependency order lane `h`'s poll with `N`
earlier successful polls precedes lane 0's arrival (`lane_rdv`): the poll returns before `h`'s
warp barrier is issued (the spin's guard, `MbarRing.Poll.guard`), the warp barrier's arrival
precedes lane 0's return from its partner (`WarpBar.depStep`), which precedes lane 0's arrival
(`WarpBar.resumes`).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Wk
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof
open PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX.Kernels.InklingRelDecode.Proof.Lp (PreSite ldThread)
open PTX.Kernels.InklingRelDecode.Proof.Ledger
open PTX.Kernels.InklingRelDecode.Proof.EvW (kvReady kvEmpty)

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

/-- The state before a loader `arrive` state is `wb0` of the same iteration. -/
theorem arrive_pred (hX : Consistent L kernel asms mem0 X) {k : Nat} {d : Loader.D}
    {P : Loader.Pro} (hk : k < (X.tr g).length) (hσ : St Q L X g k = some (some (.w (.loader d P))))
    (hs : d.site = .arrive) :
    ∃ k0 e d0, k0 + 1 = k ∧ X.get (g, k0) = some e ∧
      St Q L X g k0 = some (some (.w (.loader d0 P))) ∧ d0.site = .wb0 ∧ d0.i = d.i := by
  obtain ⟨k0, e, d0, hadj, -, he, hσ0, hn⟩ :=
    Lp.loader_state_pred_adj hX hk hσ (by rw [hs]; nofun)
  refine ⟨k0, e, d0, hadj, he, hσ0, ?_⟩
  obtain ⟨s, pro, i, n, p0, p1, ln⟩ := d0
  cases s <;> simp only [Loader.next, Loader.afterIter, Loader.readI, Loader.readN] at hn <;>
    (repeat' split at hn) <;>
    first
    | (simp at hn; done)
    | (obtain rfl := Option.some.inj (Option.some.inj hn); simp_all)

/-- The state before a loader `wb0` state is `wait` of the same iteration, whose event is a
successful poll. -/
theorem wb0_pred (hX : Consistent L kernel asms mem0 X) {k : Nat} {d : Loader.D}
    {P : Loader.Pro} (hk : k < (X.tr g).length) (hσ : St Q L X g k = some (some (.w (.loader d P))))
    (hs : d.site = .wb0) :
    ∃ k0 e d0, k0 + 1 = k ∧ X.get (g, k0) = some e ∧
      St Q L X g k0 = some (some (.w (.loader d0 P))) ∧ d0.site = .wait ∧ d0.i = d.i ∧
      ∀ l p ok acq sc, e.kind = .wait l p ok acq sc → ok = true := by
  obtain ⟨k0, e, d0, hadj, -, he, hσ0, hn⟩ :=
    Lp.loader_state_pred_adj hX hk hσ (by rw [hs]; nofun)
  refine ⟨k0, e, d0, hadj, he, hσ0, ?_⟩
  obtain ⟨s, pro, i, n, p0, p1, ln⟩ := d0
  cases s <;> simp only [Loader.next, Loader.afterIter, Loader.readI, Loader.readN] at hn <;>
    (repeat' split at hn) <;>
    first
    | (simp at hn; done)
    | (obtain rfl := Option.some.inj (Option.some.inj hn); simp_all)

/-- A warp-barrier site whose offset is a multiple of five is `wb0`. -/
theorem wb_site {s : Loader.Site} (h : s.isWb = true) {a b : Nat}
    (he : 5 * a + wbOff s = 5 * b) : s = .wb0 ∧ a = b := by
  cases s <;> simp only [Loader.Site.isWb, Bool.false_eq_true] at h <;> simp only [wbOff] at he <;>
    first | exact ⟨rfl, by omega⟩ | omega

/-- The `kv_empty` poll of a loader thread at the loop's `wait` is the thread's `N`-th of the
slot's when the iteration is the loader's `N`-th block of the slot. -/
theorem poll_index (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hR : RoleReads L X) (hp : NumPreRead Q L X) {k : Nat}
    {d : Loader.D} {P : Loader.Pro} (hσ : St Q L X g k = some (some (.w (.loader d P))))
    {s pc p : Nat} {acq : Bool} {sc : MbarScope}
    (he : X.get (g, k) = some ⟨pc, .wait (kvEmpty L (g / L.block) s) p true acq sc⟩) :
    d.i = Ring.loaderBlock (np Q L g) s
      (okPolls (kvEmpty L (g / L.block) s) ((X.tr g).take k)) := by
  have hg : g < L.threads := Frame.lt_of_get hX he
  have hk : k < (X.tr g).length := len_of_get he
  have hnp : ¬ PreSite d.site := Lp.loader_ev_notPre hpre hX hf he hσ
    (.inr (.inr ⟨_, _, _, _, _, rfl⟩))
  obtain ⟨hw4, k0, d0, hk0, h0, hd, hs0, hi0, hin, -, hP, -⟩ :=
    Lp.loader_anchor hpre hX hf hR hp hk hσ hnp
  have hpo : Ring.Ld.polled d0 = d0.i := by simp [Ring.Ld.polled, Ring.Ld.afterWait, hs0]
  obtain ⟨-, -, -, h, -⟩ := Ring.loader_poll_exec hpre hw4 hg hX hk0 h0 hd (hf.ldRng hg hσ) hin
    (by rw [hpo, hi0]; exact Lp.numPre_le _ _ _) (hP _) he
  rw [hpo, hi0] at h
  exact h

/-- **A loader lane's poll precedes lane 0's arrival of the same block.** Lane 0 of the loader
warp of CTA `c` arrives on `kv_ready s` with `N` earlier arrivals on it; every lane `h` of the warp
has made its successful poll of `kv_empty s` with `N` earlier ones, and that poll precedes the
arrival in the dependency order. -/
theorem lane_rdv (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hR : RoleReads L X) (hp : NumPreRead Q L X) {c s : Nat}
    (hc : c < L.grid) (hs : s < 3) {h : Nat} (hsw : SameWarp L h (ldThread L c)) {z pc tx cnt : Nat}
    {rel : Bool} {sc : MbarScope}
    (hz : X.get (ldThread L c, z) = some ⟨pc, .arrive (kvReady L c s) tx cnt rel sc⟩) :
    Relation.TransGen (DepStep L kernel X)
      (.thread (h, MbarRing.Poll.nth X (kvEmpty L c s) h
        (arrivals (kvReady L c s) ((X.tr (ldThread L c)).take z))), true)
      (.thread (ldThread L c, z), false) := by
  set ap := ldThread L c with hap
  have hb : L.block = 256 := hpre.block
  obtain ⟨hapt, hapc, hap192⟩ := Lp.ldThread_props hb hc
  rw [← hap] at hapt hapc hap192
  have hzl : z < (X.tr ap).length := len_of_get hz
  obtain ⟨-, -, -, hst⟩ := Lp.arrive_kvReady hpre hX hf hs hz
  obtain ⟨da, Pa, hσa, hsa⟩ : ∃ da Pa, St Q L X ap z = some (some (.w (.loader da Pa))) ∧
      da.site = .arrive := by
    rcases hst with ⟨d, hσ⟩ | ⟨d, P, hσ, hsd, -⟩
    · have := (cls_inv (Q := Q) (X := X) _ _ hzl.le hσ).mp trivial
      omega
    · exact ⟨d, P, hσ, hsd⟩
  -- lane 0's block
  have hnpa : ¬ PreSite da.site := by rw [hsa]; rintro (h | h | h) <;> cases h
  obtain ⟨hw4, k0, d0, hk0, h0, hd, hs0, hi0, hin, hA, hP, -⟩ :=
    Lp.loader_anchor hpre hX hf hR hp hzl hσa hnpa
  have hz' : X.get (ap, z) =
      some ⟨pc, .arrive (kvReady L (ap / L.block) s) tx cnt rel sc⟩ := by rw [hapc]; exact hz
  obtain ⟨-, hmod, -, -, -, -, -, hblk, -⟩
    := Ring.loader_arrive_exec hpre hw4 hapt hX hk0 h0 hd (hf.ldRng hapt hσa) hin
    hs0 (by rw [hi0]; exact Lp.numPre_le _ _ _) hs (hA _) (hP _) hz'
  rw [hi0, hapc] at hblk
  -- lane 0's warp barrier `wb0` of that iteration
  obtain ⟨z0, ew, dw, hz0, hew, hσw, hsw0, hiw⟩ := arrive_pred hX hzl hσa hsa
  have hshw := Lp.loader_ev_shape hpre hX hf hew hσw
  unfold EvW.LdShape at hshw
  rw [hsw0] at hshw
  obtain ⟨inst, rfl⟩ := hshw
  have hwb : X.WarpBar (ap, z0) 4294967295 inst := ⟨_, hew⟩
  have hcnt := wb_inv hpre hX hf hR hp z0 (by omega) hσw (by rw [hsw0]; rintro (h | h | h) <;>
    cases h)
  rw [hsw0] at hcnt
  simp only [wbOff, Nat.add_zero] at hcnt
  -- its partner in lane `h`
  have hsw' : SameWarp L ap h := sameWarp_symm hsw
  have hht : h < L.threads := hsw.1.1
  have hmem : ∀ y, y < L.threads → electMember 4294967295 (laneOf L y) := fun y _ =>
    Sched.full_member (Nat.mod_lt _ (by decide))
  obtain ⟨x, hpart⟩ := WarpBar.partner hX hsw' hwb (hmem h hht)
  have hord := WarpBar.ordinal_eq hX hsw'
    (fun j m i hj => by rw [warpBar_mask hpre hX hf.sound hf.tracked hj]; exact hmem h hht)
    (fun j m i hj => by rw [warpBar_mask hpre hX hf.sound hf.tracked hj]; exact hmem ap hapt)
    hpart
  obtain ⟨m', inst', -, ⟨pcx, hx⟩⟩ := id hpart
  have hxl : x < (X.tr h).length := len_of_get hx
  -- lane `h`'s state there: `wb0` of the same iteration
  rcases (warpBar_event_state hpre hX hf.sound hf.tracked hht hx rfl).1 with
    ⟨dx, Px, hσx, hwx⟩ | ⟨dx, Px, hσx, -⟩
  swap
  · have h7 := roleWarp_inv hf.roleWarp x _ hxl.le hσx
    have h6 := roleWarp_inv hf.roleWarp z _ hzl.le hσa
    simp only [RoleWarp, roleWarp] at h6 h7
    have := hsw.2
    omega
  have hnpx : ¬ PreSite dx.site := by
    rintro (h | h | h) <;> rw [h] at hwx <;> cases hwx
  have hcx := wb_inv hpre hX hf hR hp x hxl hσx hnpx
  have hnpe : np Q L h = np Q L ap := by
    simp only [np, ProA.cta, hsw.1.2.2]
  have hcx' : warpBars X h x + 5 * np Q L ap = 5 * dx.i + wbOff dx.site := by
    rw [← hnpe]; exact hcx
  obtain ⟨hsx, hix⟩ := wb_site hwx (a := dx.i) (b := da.i) (by omega)
  -- lane `h`'s successful poll before it
  obtain ⟨x0, ep, dp, hx0, hep, hσp, hsp, hip, hok⟩ := wb0_pred hX hxl hσx hsx
  have hshp := Lp.loader_ev_shape hpre hX hf hep hσp
  unfold EvW.LdShape at hshp
  rw [hsp] at hshp
  obtain ⟨ok, rfl⟩ := hshp
  have hok' := hok _ _ _ _ _ rfl
  subst hok'
  have hhc : h / L.block = c := by rw [hsw.1.2.2, hapc]
  have hslot : dp.i % 3 = s := by rw [hip, hix, ← hmod]
  rw [hhc, hslot] at hep
  have hidx := poll_index hpre hX hf hR hp hσp (by rw [hhc]; exact hep)
  rw [hhc, hnpe, hip, hix, hblk] at hidx
  have hN : okPolls (kvEmpty L c s) ((X.tr h).take x0) =
      arrivals (kvReady L c s) ((X.tr ap).take z) := by
    unfold Ring.loaderBlock Ring.loaderUse Ring.blockOf at hidx
    split at hidx <;> omega
  have hpx : okPolls (kvEmpty L c s) ((X.tr h).take x) =
      okPolls (kvEmpty L c s) ((X.tr h).take x0) + 1 := by
    subst hx0
    unfold okPolls
    have hep' : (X.tr h)[x0]? = some _ := hep
    rw [List.take_add_one, hep', Option.toList_some, List.countP_append]
    simp [okPoll_wait rfl]
  -- the path
  have g1 : Resumes kernel X (h, MbarRing.Poll.nth X (kvEmpty L c s) h
      (arrivals (kvReady L c s) ((X.tr ap).take z))) (h, x) :=
    MbarRing.Poll.guard (fun w pc m q acq sc he => Safety.poll_spins hX he) hxl (by omega)
  have g2 := WarpBar.depStep hX hsw hpart.symm
  have g3 := WarpBar.resumes (L := L) (K := kernel) hwb (show z0 < z by omega) hzl
  exact (Relation.TransGen.single (DepStep.of_resumes L g1)).tail g2 |>.tail g3

end
end PTX.Kernels.InklingRelDecode.Proof.Wk
