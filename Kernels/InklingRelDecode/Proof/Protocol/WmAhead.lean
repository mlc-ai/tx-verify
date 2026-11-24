-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Kernel.Progress.Warp
public import Kernels.InklingRelDecode.Proof.Protocol.WmMmaCount
public import Kernels.InklingRelDecode.Proof.Protocol.RingCommitLe

@[expose] public section

/-!
# No lane of the MMA warp commits a block its warp has not polled

A lane `g` of the MMA warp at its poll of `kv_ready (i % 3)` at the end of its trace has made
`top i + 1` warp barriers (`Wm.mma_wb_inv`: `qkBar` of iteration `i` is its last). A commit to
`kv_empty (i % 3)` with at least `i / 3` earlier ones is the commit of a block `j - 1 ≥ i` at
`pvCommit1` of iteration `j ≥ i + 1` (`Lp.commit_lead`, the commits counted by the state on the
anchored run, `mma_kv_commits_at`), after `top j + 2 ≥ 4 i + 4` warp barriers of its thread. That
thread's warp barrier with `top i + 1` earlier ones has a partner in `g` with the same ordinal
(`WarpBar.partner`, `WarpBar.ordinal_eq`; every warp barrier has the full mask,
`Interface.warpBar_mask`), so `g` would have made more than `top i + 1` warp barriers
(`no_commit_ahead`). This is the reuse path of `kv_ready` through `qkBar2` for every lane of the
MMA warp, read by counting.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Wm
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof
open PTX.Kernels.InklingRelDecode.Proof.Interface PTX.Kernels.InklingRelDecode.Proof.Ledger
open PTX.Kernels.InklingRelDecode.Proof.EvW (kvReady kvEmpty)

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

/-- **The commits of an MMA lane to `kv_empty` before one of its events** are at most
`below s (Mm.done d)` (`Ring.mma_commits_le`). -/
theorem mma_kv_commits_at (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hR : RoleReads L X) {k : Nat} {d : Mma.D} {P : Loader.Pro}
    (hk : k < (X.tr g).length) (hσ : St Q L X g k = some (some (.w (.mma d P))))
    (hs : d.site ≠ .setMaxReg) :
    ∀ s < 3, ((X.tr g).take k).countP (commitsTo (kvEmpty L (g / L.block) s)) ≤
      Ring.below s (Ring.Mm.done d) := by
  intro s hs3
  obtain ⟨hg, hw, k0, d0, hk0, -, h0, hd, hs0, hin, hC, -⟩ :=
    Proof.Wv.mma_anchor_le hpre hX hf hR hk.le hσ hs
  obtain ⟨hT, hend, hin'⟩ := SO.mma_exec_run hpre hw hg hX hk0 h0 hd hin
  have h := Ring.mma_commits_le hpre hg hT hin' hend hs3
  have hz : Ring.Mm.done d0 = 0 := by simp [Ring.Mm.done, hs0]
  have hb0 : Ring.below s 0 = 0 := by unfold Ring.below; omega
  rw [hz, hb0, Nat.add_zero] at h
  rw [Ring.countP_take_split _ _ hk0, hC, Nat.zero_add]
  exact h

/-- **A lane with `W` warp barriers in all has no partner of a warp barrier with `W` earlier
ones**: a lane `y` of its warp has made at most `W` warp barriers before each of its events. -/
theorem warpBars_le_peer (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) {y : Nat} (hsw : SameWarp L y g) (k : Nat) :
    warpBars X y k ≤ warpBars X g (X.tr g).length := by
  by_contra hlt
  push Not at hlt
  set W := warpBars X g (X.tr g).length with hW
  obtain ⟨j, e, hj, he, hp, hc⟩ :=
    Flow.exists_nthEv (X := X) (p := Execution.isWarpBar) (g := y) (k := k) (n := W)
      (by unfold warpBars at hlt; omega)
  have hk' : ∃ m inst, e.kind = .warpBar m inst := by
    obtain ⟨pc, kd⟩ := e
    cases kd <;> simp_all [Execution.isWarpBar]
  obtain ⟨m, inst, hke⟩ := hk'
  have hwb : X.WarpBar (y, j) m inst := by
    obtain ⟨pc, kd⟩ := e
    simp only at hke
    subst hke
    exact ⟨pc, he⟩
  have hgt : g < L.threads := hsw.1.2.1
  have hyt : y < L.threads := hsw.1.1
  have hmem : ∀ z, z < L.threads → electMember 4294967295 (laneOf L z) := fun z _ =>
    Sched.full_member (Nat.mod_lt _ (by decide))
  have hm : m = 4294967295 := warpBar_mask hpre hX hf.sound hf.tracked hwb
  subst hm
  obtain ⟨x, hpart⟩ := WarpBar.partner hX hsw hwb (hmem g hgt)
  have hord := WarpBar.ordinal_eq hX hsw
    (fun j m i hj => by rw [warpBar_mask hpre hX hf.sound hf.tracked hj]; exact hmem g hgt)
    (fun j m i hj => by rw [warpBar_mask hpre hX hf.sound hf.tracked hj]; exact hmem y hyt)
    hpart
  obtain ⟨m', inst', -, hgx⟩ := hpart
  have hxs := WarpBar.warpBars_succ hgx
  have hxl := WarpBar.lt_len hgx
  have hmono : warpBars X g (x + 1) ≤ W := by
    unfold warpBars
    exact (List.take_sublist_take_left (by simpa using hxl)).countP_le
  have hyj : warpBars X y j = W := hc
  omega

/-- **No lane of the MMA warp commits a block its warp has not polled.** For a lane `g` at its
poll of `kv_ready (i % 3)` at the end of its trace, no lane `y` of its warp has a commit to
`kv_empty (i % 3)` with at least `i / 3` earlier ones. -/
theorem no_commit_ahead (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hR : RoleReads L X) {d : Mma.D} {P : Loader.Pro}
    (hσ : St Q L X g (X.tr g).length = some (some (.w (.mma d P)))) (hw : d.site = .kvWait)
    {y : Nat} (hsw : SameWarp L y g) {k pc : Nat} {sp : TcCommit.Spec}
    (he : X.get (y, k) = some ⟨pc, .tc (.commit sp)⟩)
    (hm : sp.mbar = kvEmpty L (g / L.block) (d.i % 3))
    (hcnt : d.i / 3 ≤ ((X.tr y).take k).countP (commitsTo (kvEmpty L (g / L.block) (d.i % 3)))) :
    False := by
  have hcy : y / L.block = g / L.block := hsw.1.2.2
  have hs3 : d.i % 3 < 3 := Nat.mod_lt _ (by omega)
  rw [← hcy] at hm hcnt
  obtain ⟨dc, Pc, hσc, hsc, -⟩ := Lp.commit_lead hpre hX hf hs3 he hm
  have hkl : k < (X.tr y).length := len_of_get he
  have hc := mma_kv_commits_at hpre hX hf hR hkl hσc (by rw [hsc]; nofun) _ hs3
  have hsh := mma_ev_shape hpre hX hf he hσc
  unfold EvW.MmShape at hsh
  rw [hsc] at hsh
  simp only [Event.mk.injEq, Kind.tc.injEq, TcKind.commit.injEq] at hsh
  obtain ⟨-, rfl⟩ := hsh
  have hslot : (dc.i - 1) % 3 = d.i % 3 := by
    have h1 : (EvW.commitSpec (y / L.block)
        (kvEmpty L (y / L.block) ((dc.i - 1) % 3))).mbar =
        kvEmpty L (y / L.block) ((dc.i - 1) % 3) := rfl
    rw [h1] at hm
    exact Ring.kvEmpty_inj hm
  have hdone : Ring.Mm.done dc = dc.i - 1 := by simp [Ring.Mm.done, hsc]
  rw [hdone, Ring.below_of_slot hs3 hslot] at hc
  have hI : Mma.Inv dc := mma_inv_at hX hf hkl hσc
  have hpv := hI.pv (by rw [hsc]; trivial)
  have hji : d.i + 1 ≤ dc.i := by omega
  have hwy := Wm.mma_wb_inv hpre hX hf hR k hkl.le hσc (by rw [hsc]; nofun)
  have hwg := Wm.mma_wb_inv hpre hX hf hR _ le_rfl hσ (by rw [hw]; nofun)
  have hle := warpBars_le_peer hpre hX hf hsw k
  rw [hwy, hwg] at hle
  simp only [wbM, hsc, hw, top, qkB] at hle
  split at hle <;> omega

end
end PTX.Kernels.InklingRelDecode.Proof.Wm
