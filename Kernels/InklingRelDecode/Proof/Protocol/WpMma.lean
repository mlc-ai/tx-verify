-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Protocol.HsPkg
public import Kernels.InklingRelDecode.Proof.Interface.WpSynced

@[expose] public section

/-!
# The MMA warp's `kv_ready` and `p_ready` polls, met through its shuffles

The MMA role broadcasts the warp index once in each QK half (`qkShfl`) and once in each PV half
(`pvShfl`). Along a thread's run of the role, from its entry (`setMaxReg`), the shuffles made
before a state are `shfls` of the state (`shfl_cnt`, with `SO.mma_count` as for the elections of
`Vx.elect_cnt`): `i + (i - 1)` at `kvWait` of iteration `i`, `min (i + 1) n + (i - 1)` at `pWait`.
Both grow with the iteration.

The lanes of a warp have made equally many shuffles before their entries (`entry_cnt`): the entry
is a synchronizing state (`setmaxnreg`), and a lane whose entry has a smaller synchronizing
ordinal than another lane's would, by the lockstep (`Interface.Lk.lock_kernel`), see the other
lane at a synchronizing state at the entry's position before the other's entry: that is a second
entry of the role (excluded by `Rd.mma_entry_unique`) or the dispatch's `toMma` site, after which
the machine stops. At one ordinal the counts agree (`Interface.Lk.lock_count`).

So of two lanes of the warp at `kvWait` (or both at `pWait`), the lane in the earlier iteration has
made fewer shuffles than the other, and `meet_shfl` orders its poll before the other's
(`mma_met`).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Wp
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof
open PTX.Kernels.InklingRelDecode.Proof.Interface PTX.Kernels.InklingRelDecode.Proof.Interface.Lk
open PTX.Kernels.InklingRelDecode.Proof.Ring (wAt)

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

/-! ### The shuffles along the role -/

/-- The two shuffle sites of the MMA role. -/
def shSite : Mma.Site → Bool
  | .qkShfl | .pvShfl => true
  | _ => false

/-- The shuffles made from the entry of the role to state `d`: one per QK half and one per PV
half that reached its broadcast. -/
def shfls (d : Mma.D) : Nat :=
  match d.site with
  | .setMaxReg | .ldNum | .bar0 => 0
  | .qkBar | .kvWait | .qkShfl => d.i + (d.i - 1)
  | .qkBar2 | .qkElect | .qk _ | .qkCommit | .qkSkip => d.i + (d.i - 1) + 1
  | .pvBar | .pWait | .pvShfl => min (d.i + 1) d.n + (d.i - 1)
  | .pvBar2 | .pvElect | .pv _ | .pvCommit1 | .pvCommit2 | .pvSkip =>
    min (d.i + 1) d.n + (d.i - 1) + 1
  | .finBar | .finElect | .finCommit | .bar1 | .setMaxRegInc => if d.i = 0 then 0 else d.n + d.n

set_option linter.unusedTactic false in
/-- **A step of the MMA warp, for the shuffles.** -/
theorem next_shfls {d d' : Mma.D} {e : Event} (hi : Mma.Inv d)
    (hne : d.site ≠ .setMaxRegInc) (h : Mma.next L g d e = some (some d')) :
    shfls d' = shfls d + if shSite d.site then 1 else 0 := by
  have hq := hi.qk
  have hp := hi.pv
  have hpre := hi.pre
  obtain ⟨site, i, n, tm, pro⟩ := d
  simp only [Mma.QkSite, Mma.PvSite, Mma.PreSite] at hq hp hpre
  simp only at hne
  cases site
  case setMaxRegInc => exact absurd rfl hne
  all_goals
    simp only [Mma.next] at h
    (repeat' split at h)
    all_goals try (obtain rfl := Option.some.inj (Option.some.inj h))
    all_goals try (cases h)
    all_goals try simp only [Mma.start, Mma.afterQk, Mma.iterNext, Mma.qkNext, Mma.pvNext]
    all_goals (repeat' split)
    all_goals simp_all [shfls, shSite]
    all_goals omega

/-- At a shuffle site a step is a shuffle. -/
theorem next_shfl_kind {d d' : Mma.D} {e : Event} (hs : shSite d.site = true)
    (h : Mma.next L g d e = some (some d')) : Execution.isShfl e = true := by
  obtain ⟨site, i, n, tm, pro⟩ := d
  obtain ⟨pc, k⟩ := e
  cases site <;> simp only [shSite, Bool.false_eq_true] at hs
  all_goals
    simp only [Mma.next] at h
    cases k <;> simp_all [Execution.isShfl]

/-- The event of a state is a shuffle exactly at the shuffle sites. -/
theorem shape_isShfl {d : Mma.D} {e : Event} (hsh : EvW.MmShape L g d e) :
    Execution.isShfl e = shSite d.site := by
  obtain ⟨site, i, n, tm, pro⟩ := d
  cases site <;> simp only [EvW.MmShape, EvW.QkIssue, EvW.PvIssue] at hsh
  all_goals first
    | (subst hsh; rfl)
    | (obtain ⟨_, rfl⟩ := hsh; rfl)
    | (obtain ⟨_, _, rfl⟩ := hsh; rfl)
    | (obtain ⟨_, _, rfl, -⟩ := hsh; rfl)
    | (obtain ⟨_, _, -, -, rfl⟩ := hsh; rfl)
    | (obtain ⟨_, _, _, -, -, -, rfl⟩ := hsh; rfl)

/-- **The shuffles of an MMA-warp thread at a state**: those before the entry of its run, plus
`shfls` of the state. -/
theorem shfl_cnt (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hR : RoleReads L X) (hg : g < L.threads) {k : Nat}
    {d : Mma.D} {P : Loader.Pro} (hk : k < (X.tr g).length)
    (hσ : St Q L X g k = some (some (.w (.mma d P)))) :
    ∃ (k0 : Nat) (d0 : Mma.D), k0 ≤ k ∧ St Q L X g k0 = some (some (.w (.mma d0 P))) ∧
      d0.site = .setMaxReg ∧
      cnt Execution.isShfl X g k = cnt Execution.isShfl X g k0 + shfls d := by
  have hw : 4 ≤ WComp.warpOf L g := (Rd.mma_anchor hpre hX hf hR hg hk hσ).1
  obtain ⟨k0, d0, hk0, h0, hs0, hch⟩ := Rd.mma_back hX hf k hk hσ
  have h0w : wAt Q L X g k0 = some (some (.mma d0 P)) := Rd.wAt_of_st k0 (by omega) h0
  have hdw : wAt Q L X g k = some (some (.mma d P)) := Rd.wAt_of_st k (by omega) hσ
  have hin : ∀ j, k0 ≤ j → j < k → ∃ d', wAt Q L X g j = some (some (.mma d' P)) ∧
      Mma.Inv d' ∧ d'.site ≠ .setMaxRegInc := by
    intro j hj1 hj2
    obtain ⟨dj, hdj, hI, hne⟩ := hch j hj1 hj2
    exact ⟨dj, Rd.wAt_of_st j (by omega) hdj, hI, hne⟩
  obtain ⟨hT, hend, hin'⟩ := SO.mma_exec_run hpre hw hg hX hk0 h0w hdw hin
  have hc := SO.mma_count hT Execution.isShfl shfls (fun _ => True) (fun _ _ => trivial) ?_
    hin' hend
  · have hz : shfls d0 = 0 := by simp [shfls, hs0]
    refine ⟨k0, d0, hk0, h0, hs0, ?_⟩
    unfold cnt
    rw [Ring.countP_take_split _ _ hk0, ← hc, hz, Nat.add_zero]
  · intro d1 d' e hin1 hne _ hev hn
    rw [next_shfls hin1 hne hn]
    have hk : Execution.isShfl e = shSite d1.site := by
      rcases hev with ⟨u, hF⟩ | hend
      · exact shape_isShfl (EvW.mma_shape hpre hg hF)
      · cases hs : shSite d1.site
        · obtain ⟨pc, k⟩ := e
          rcases hend with ⟨f, h⟩ | h <;> simp only at h <;> subst h <;> rfl
        · have := next_shfl_kind hs hn
          obtain ⟨pc, k⟩ := e
          rcases hend with ⟨f, h⟩ | h <;> simp only at h <;> subst h <;>
            simp [Execution.isShfl] at this
    rw [hk]

/-! ### The entries of the lanes of a warp -/

theorem mma_pc_entry (s : Mma.Site) (h : s.pc = Mma.Site.setMaxReg.pc) : s = .setMaxReg := by
  revert h
  cases s
  all_goals try (rename_i j; revert j)
  all_goals decide +kernel

theorem worker_pc_entry (s : Worker.Site) (h : s.pc = Mma.Site.setMaxReg.pc) : s = .toMma := by
  revert h
  cases s
  all_goals decide +kernel

theorem idle_pc_entry (s : Worker.Idle.Site) : s.pc ≠ Mma.Site.setMaxReg.pc := by
  cases s
  all_goals decide +kernel

theorem loader_pc_entry (s : Loader.Site) : s.pc ≠ Mma.Site.setMaxReg.pc := by
  cases s
  all_goals decide +kernel

theorem exit_pc_entry (s : WComp.ExitSite) : s.pc ≠ Mma.Site.setMaxReg.pc := by
  cases s
  all_goals decide +kernel

/-- A worker state at the position of the MMA role's entry is that entry, or the dispatch's
`toMma` site. -/
theorem entry_state {s : WComp.WSt} (h : WComp.pc s = Mma.Site.setMaxReg.pc) :
    (∃ d P, s = .mma d P ∧ d.site = .setMaxReg) ∨ ∃ P, s = .worker ⟨.toMma, P⟩ := by
  cases s with
  | worker w =>
    obtain ⟨site, P⟩ := w
    exact .inr ⟨P, by rw [worker_pc_entry site h]⟩
  | idle d => exact absurd h (idle_pc_entry d.site)
  | loader d _ => exact absurd h (loader_pc_entry d.site)
  | mma d P => exact .inl ⟨d, P, rfl, mma_pc_entry d.site h⟩
  | exit x => exact absurd h (exit_pc_entry x.site)

/-- The entry of the MMA role is a synchronizing state. -/
theorem entry_sy {d : Mma.D} {P : Loader.Pro} (hs : d.site = .setMaxReg) :
    (kernelSkel Q L).sy (.w (.mma d P)) := by
  show PTX.Kernels.InklingRelDecode.Proof.Lk.wSy (.mma d P) = true
  simp only [PTX.Kernels.InklingRelDecode.Proof.Lk.wSy,
    PTX.Kernels.InklingRelDecode.Proof.Lk.isLdRole, WComp.pc, WComp.sub, hs, Bool.or_false]
  decide +kernel

/-- A lane's MMA entry has no larger synchronizing ordinal than another lane's of its warp. -/
theorem entry_sy_le (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hA : LaneAgree Q L X) (hR : RoleReads L X) {h k0 k0' : Nat}
    {d0 d0' : Mma.D} {P P' : Loader.Pro} (hw : SameWarp L g h) (hk0 : k0 < (X.tr g).length)
    (hk0' : k0' < (X.tr h).length) (h0 : St Q L X g k0 = some (some (.w (.mma d0 P))))
    (hs0 : d0.site = .setMaxReg) (h0' : St Q L X h k0' = some (some (.w (.mma d0' P'))))
    (hs0' : d0'.site = .setMaxReg) :
    ¬ syN (kernelSkel Q L) X g k0 < syN (kernelSkel Q L) X h k0' := by
  intro hlt
  have ht := hf.tracked
  have hL := lock_kernel ht hA
  have hh : h < L.threads := hw.1.2.1
  obtain ⟨b0, hb0, hsy0, hn0⟩ := exists_ordinal (kernelSkel Q L) (X := X) h
    (syN (kernelSkel Q L) X h k0' - syN (kernelSkel Q L) X g k0) (a := k0')
    (n := syN (kernelSkel Q L) X g k0) ⟨_, h0', entry_sy hs0'⟩ (by omega)
  have hb0' : b0 < k0' := by
    rcases Nat.lt_or_eq_of_le hb0 with h1 | h1
    · exact h1
    · subst h1; omega
  obtain ⟨sb, hsb, hsyb⟩ := hsy0
  have hkey := hL _ hw (by omega) (by omega) h0 hsb (entry_sy hs0) hsyb rfl hn0
  have hp1 := (kernelSkel Q L).pc_key (g := g) (entry_sy (P := P) hs0)
  have hp2 := (kernelSkel Q L).pc_key (g := h) hsyb
  have hpc : TSt.pc sb = Mma.Site.setMaxReg.pc := by
    rw [← hp2, ← hkey, hp1]
    show d0.site.pc = _
    rw [hs0]
  have hwg : ¬ g % L.block < 128 := fun hc =>
    by simpa [TSt.isD] using (cls_inv k0 _ (by omega) h0).mpr hc
  have hwh : ¬ h % L.block < 128 := by
    have := hw.2
    omega
  cases sb with
  | d sd => exact hwh ((cls_inv b0 _ (by omega) hsb).mp trivial)
  | w sw =>
    rcases entry_state (s := sw) hpc with ⟨db, Pb, rfl, hsb'⟩ | ⟨Pb, rfl⟩
    · have := Rd.mma_entry_unique hpre hX hf hR (by omega) hk0' hsb hsb' h0' hs0'
      omega
    · obtain ⟨t, htt⟩ := Frame.stateAt_live (C := code L Q) ht hh h0' (show b0 + 1 ≤ k0' by omega)
      obtain ⟨e, he⟩ : ∃ e, (X.tr h)[b0]? = some e := ⟨_, List.getElem?_eq_getElem (by omega)⟩
      have hn := next_of_st_succ he hsb htt
      obtain ⟨a, ha, -⟩ := next_w_inv hn
      simp [WComp.next, Worker.next] at ha

/-- **The lanes of a warp have made equally many shuffles before their MMA entries.** -/
theorem entry_cnt (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hA : LaneAgree Q L X) (hR : RoleReads L X) {h k0 k0' : Nat}
    {d0 d0' : Mma.D} {P P' : Loader.Pro} (hw : SameWarp L g h) (hk0 : k0 < (X.tr g).length)
    (hk0' : k0' < (X.tr h).length) (h0 : St Q L X g k0 = some (some (.w (.mma d0 P))))
    (hs0 : d0.site = .setMaxReg) (h0' : St Q L X h k0' = some (some (.w (.mma d0' P'))))
    (hs0' : d0'.site = .setMaxReg) :
    cnt Execution.isShfl X g k0 = cnt Execution.isShfl X h k0' := by
  have h1 := entry_sy_le hpre hX hf hA hR hw hk0 hk0' h0 hs0 h0' hs0'
  have h2 := entry_sy_le hpre hX hf hA hR (sameWarp_symm hw) hk0' hk0 h0' hs0' h0 hs0
  exact lock_count (kernelSkel Q L) hf.tracked (lock_kernel hf.tracked hA) (isShfl_state hX hf)
    (fun hs => shflSt_sy hs) shflKey_class _ hw (by omega) (by omega) h0 h0' (entry_sy hs0)
    (entry_sy hs0') rfl (by omega)

/-! ### The polls -/

/-- **Two lanes of the MMA warp at `kvWait`, or both at `pWait`**: the poll of the lane in the
earlier iteration is ordered before the other's. -/
theorem mma_met (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hA : LaneAgree Q L X) (hR : RoleReads L X) {h k k' : Nat}
    {e : Event} {d d' : Mma.D} {P P' : Loader.Pro} (hw : SameWarp L g h)
    (he : X.get (g, k) = some e) (hne : Execution.isShfl e = false)
    (hσ : St Q L X g k = some (some (.w (.mma d P))))
    (hσ' : St Q L X h k' = some (some (.w (.mma d' P')))) (hk' : k' < (X.tr h).length)
    (hs : (d.site = .kvWait ∧ d'.site = .kvWait) ∨ (d.site = .pWait ∧ d'.site = .pWait))
    (hlt : d.i < d'.i) : PollBefore L kernel X (g, k) (h, k') := by
  have hk : k < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  have hg : g < L.threads := hw.1.1
  have hh : h < L.threads := hw.1.2.1
  obtain ⟨k0, d0, hk0, h0, hs0, hc⟩ := shfl_cnt hpre hX hf hR hg hk hσ
  obtain ⟨k0', d0', hk0', h0', hs0', hc'⟩ := shfl_cnt hpre hX hf hR hh hk' hσ'
  have hE := entry_cnt hpre hX hf hA hR hw (by omega) (by omega) h0 hs0 h0' hs0'
  have hI' := mma_inv_at hX hf hk' hσ'
  have hlt' : shfls d < shfls d' := by
    rcases hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · simp only [shfls, h1, h2]
      omega
    · have hp' := hI'.pv (by simp [Mma.PvSite, h2])
      have hp := (mma_inv_at hX hf hk hσ).pv (by simp [Mma.PvSite, h1])
      simp only [shfls, h1, h2]
      omega
  exact meet_shfl hX hf hA hw he hne (le_of_eq hc) (by omega) hk'

end
end PTX.Kernels.InklingRelDecode.Proof.Wp
