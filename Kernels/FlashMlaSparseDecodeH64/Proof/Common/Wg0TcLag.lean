-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Wg0TcCnt
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.LastTime
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Wg0BarLag
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Where
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.RegTime
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.TcCmp
import Kernels.FlashMlaSparseDecodeH64.Proof.Startup.TcOrd
import Lemmas.Kernel.VoteSame

@[expose] public section

/-! # The collective lag of warps 0–3 on the time table

Lanes of one warp of warps 0–3 receive the same results from their votes (`voteRes_same`, by
`Step.voteMode_same`: every full-mask vote of these warps is warpgroup 0's `.any` vote). Hence a
lane of the warp of a lane at its `k`-th collective, with at most `k` collectives, is no later
than that lane's state (`w0_tcLag`): its states are startup states (no later, by the count of
paired operations, `Startup.time_refT`) or warpgroup-0 states, which a later place would put
past `k` collectives (`Wg0.tcOrd_le_of`, with the arms of the two lanes equal below the votes
both made). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32 MbarRow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {g h y : Nat}

/-- Lanes of one warp have one warp word. -/
theorem warpW_same (hp : Pre P L m) (hw : SameWarp L g h) :
    warp L g = warp L h ∧ warpW L g = warpW L h := by
  obtain ⟨-, hs⟩ := hw
  have hx : warp L g = warp L h := by simp only [warp, tidOf_x_eq hp, ← hp.block]; exact hs
  refine ⟨hx, ?_⟩
  simp only [warp] at hx
  simp only [warpW, warpOf, tidOf, hx]

section
variable (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow P L X)
  (hnu : ¬ HasUb X)
include hp hX hFw hnu

/-- A full-mask vote of a lane of warps 0–3 is warpgroup 0's `.any` vote, at pc 578. -/
theorem w0_voteKind (hw : warp L y < 4) (hy : y < L.threads) {k : Nat} {e : Event}
    (he : X.get (y, k) = some e) (hv : voteWith (2 ^ 32 - 1) e = true) :
    e.pc = 578 ∧ ∃ a r, e.kind = .voteMode .any (2 ^ 32 - 1) a r := by
  have hub := noUb_kind hnu he
  obtain ⟨σ, hσ, -, -, hev, hpcσ⟩ := ev_at hp hX hFw he hub
  rcases w0_bst hFw hnu hw hy hσ with ⟨d, n, rfl, hxd⟩ | ⟨d, n, rfl, -⟩
  · have hx : ∀ r, d.site ≠ .enter r := fun r h => by simp [Startup.exitOf, h] at hxd
    have := (Startup.ev_tc hx hev).2
    rw [hv] at this
    cases this
  · obtain ⟨-, hK⟩ : Wg0.Ev P L y (warpW L y) d e := hev
    have hs := Wg0.evK_vote hub hK
    rw [hv] at hs
    have hs' : d.site = .vote := by simpa using hs.symm
    have hpc : e.pc = d.site.pc := hpcσ
    refine ⟨by rw [hpc, hs']; rfl, ?_⟩
    simp only [Wg0.EvK, hs'] at hK
    rcases hK with ⟨a, r, h⟩ | ⟨f, h⟩
    · exact ⟨a, r, h⟩
    · exact absurd h (hub f)

/-- **Lanes of one warp of warps 0–3 receive the same vote results**, for votes both made. -/
theorem voteRes_same (hw : warp L g < 4) (hsw : SameWarp L g h) {n : Nat}
    (hng : n < vCnt X g (X.tr g).length) (hnh : n < vCnt X h (X.tr h).length) :
    voteRes X g n = voteRes X h n := by
  have hg : g < L.threads := hsw.1.1
  obtain ⟨j, e, -, he, hv, hc⟩ := exists_nthEv (X := X) (p := voteWith (2 ^ 32 - 1)) (g := g)
    (k := (X.tr g).length) (n := n) hng
  obtain ⟨j', e', -, he', hv', hc'⟩ := exists_nthEv (X := X) (p := voteWith (2 ^ 32 - 1)) (g := h)
    (k := (X.tr h).length) (n := n) hnh
  rw [voteRes_of he hv hc, voteRes_of he' hv' hc']
  obtain ⟨-, a, r, hk⟩ := w0_voteKind hp hX hFw hnu hw hg he hv
  obtain ⟨-, a', r', hk'⟩ := w0_voteKind hp hX hFw hnu (by rw [← (warpW_same hp hsw).1]; exact hw)
    hsw.1.2.1 he' hv'
  obtain ⟨pc, kd⟩ := e
  obtain ⟨pc', kd'⟩ := e'
  simp only at hk hk'
  subst hk hk'
  simp only [Wg0.vres]
  refine Step.voteMode_same hX (by rw [hp.block]) hg ?_ hsw he he'
    ⟨⟨_, _, he, rfl, rfl⟩, hc⟩ ⟨⟨_, _, he', rfl, rfl⟩, hc'⟩
  intro y k f p hy hf hp' hm
  have hvy : voteWith (2 ^ 32 - 1) f = true := by simp [voteWith, hp', hm]
  obtain ⟨-, b, s, hfk⟩ := w0_voteKind hp hX hFw hnu (by rw [← (warpW_same hp hy).1]; exact hw)
    hy.1.2.1 hf hvy
  rw [hfk] at hp'
  simp only [voteClass, Option.some.injEq] at hp'
  rw [← hp']

omit hp hX in
/-- A warpgroup-0 state's place facts. -/
private theorem w0_core (hw : warp L y < 4) (hy : y < L.threads) {i : Nat} {d : Wg0.Control.D}
    {n : Cls → Nat}
    (hs : Frame.stateAt (thread P L) X y i = some (some (.inr ⟨.inl .wg0, d⟩, n))) :
    (∃ c, Wg0.RefCore L y d c) ∧ Wg0.LaunchOk P L y d ∧
      (d.site = .dealloc → scmpi .ne .b (warpW L y) 0 = false) := by
  rcases w0_bst hFw hnu hw hy hs with ⟨_, _, hx, -⟩ | ⟨d', n', hx, hC, hL, -⟩
  · cases hx
  simp only [Prod.mk.injEq, Sum.inr.injEq, Sigma.mk.inj_iff, heq_eq_eq, true_and] at hx
  obtain ⟨rfl, rfl⟩ := hx
  refine ⟨⟨_, hC⟩, hL, fun hd => ?_⟩
  obtain ⟨-, ⟨-, hTm⟩, -, -⟩ := (follow_iff.mp hFw y hy i).2 _ hs
  have hu : n .ub = 0 := (state_count hs .ub).trans
    (w0_noUbTakeW_pre (fun f h => by obtain ⟨pc, kd⟩ := f; cases kd <;> simp [cls] at h ⊢)
      (noUbBefore_of_noUb hnu))
  have ht := hTm hu
  simp only [Wg0.TmemAt, hd, ↓reduceIte] at ht
  exact ht.1

omit hp hX hFw hnu in
/-- The count of a whole trace by its last event. -/
private theorem cnt_last {f : Event} (hf : (X.tr y)[(X.tr y).length - 1]? = some f)
    (c : Event → Bool) : (X.tr y).countP c =
      ((X.tr y).take ((X.tr y).length - 1)).countP c + if c f then 1 else 0 := by
  have hpos : 0 < (X.tr y).length := by
    have := (List.getElem?_eq_some_iff.mp hf).1
    omega
  conv => lhs; rw [← List.take_length (l := X.tr y),
    show (X.tr y).length = (X.tr y).length - 1 + 1 by omega]
  rw [List.take_add_one, hf, Option.toList_some, List.countP_append]
  simp [List.countP_singleton]

/-- **A startup collective of a lane of warps 0–3**: the allocation (`k = 0`) or the
relinquishment (`k = 1`), in warp 0. -/
theorem w0_tcStart (hw : warp L g < 4) (hg : g < L.threads) {j k : Nat} {d0 : Startup.D}
    {n0 : Cls → Nat} {e : Event}
    (hσ : Frame.stateAt (thread P L) X g j = some (some (.inl d0, n0)))
    (hxd : Startup.exitOf d0 = none) (hev : Startup.Ev L g d0 e) (hce : isTcColl e = true)
    (hcnt : tcCnt X g j = k) :
    (d0.site = .alloc ∧ k = 0 ∨ d0.site = .relinq ∧ k = 1) ∧
      scmpi .ne .b (warpW L g) 0 = false := by
  have hx : ∀ r, d0.site ≠ .enter r := fun r h => by simp [Startup.exitOf, h] at hxd
  have hsite := Startup.ev_tmem hx hev
  rw [← (Startup.ev_tc hx hev).1, hce] at hsite
  obtain ⟨-, hW, hT⟩ := (follow_iff.mp hFw g hg j).2 _ hσ
  have hc0 := state_count hσ .tmem
  obtain ⟨g1, -⟩ := w0_tc hp hX hFw hw hg j (noUbBefore_of_noUb hnu) _ hσ
  rw [hcnt] at g1
  simp only at hc0
  try simp only [cls] at hc0
  rw [← g1] at hc0
  have hsite' := hsite.symm
  simp only [Bool.or_eq_true, decide_eq_true_eq] at hsite'
  rcases hsite' with hs | hs <;> simp only [Startup.RefT, Startup.RefW, hs] at hT hW <;>
    rw [← hW.2.2.1]
  · exact ⟨.inl ⟨hs, by omega⟩, hT.2⟩
  · exact ⟨.inr ⟨hs, by omega⟩, hT.2⟩


/-- **The comparison of two lanes of a warp at a collective of warpgroup 0**: a state of the
other lane at a place no earlier has made more collectives, or as many when it is at the same
place at a collective site (`Wg0.tcOrd_le_of`, the arms equal below the votes both made). -/
theorem w0_tcKey (hw : warp L g < 4) (hsw : SameWarp L g h) {j k : Nat} {d : Wg0.Control.D}
    {n : Cls → Nat}
    (hσ : Frame.stateAt (thread P L) X g j = some (some (.inr ⟨.inl .wg0, d⟩, n)))
    (htc : d.site.isTc = true) (hcnt : tcCnt X g j = k) {i : Nat} {s : Wg0.Control.D}
    {n' : Cls → Nat}
    (hs : Frame.stateAt (thread P L) X h i = some (some (.inr ⟨.inl .wg0, s⟩, n')))
    (hpl : Wg0.place d ≤ Wg0.place s) :
    (Wg0.place d < Wg0.place s ∧ k + 1 ≤ tcCnt X h i) ∨
      (Wg0.place s = Wg0.place d ∧ s.site.isTc = true ∧ k ≤ tcCnt X h i) := by
  have hg : g < L.threads := hsw.1.1
  have hh : h < L.threads := hsw.1.2.1
  obtain ⟨hwe, hWe⟩ := warpW_same hp hsw
  have hwh : warp L h < 4 := hwe ▸ hw
  obtain ⟨g1, g2, gV, gA⟩ := w0_tc hp hX hFw hw hg j (noUbBefore_of_noUb hnu) _ hσ
  rw [hcnt] at g1
  obtain ⟨⟨_, hC⟩, hL, -⟩ := w0_core hFw hnu hw hg hσ
  have hRd := Wg0.rounds_blocks hL (Wg0.lens_two (Wg0.tc_reg htc))

  obtain ⟨h1, h2, hV, hA⟩ := w0_tc hp hX hFw hwh hh i (noUbBefore_of_noUb hnu) _ hs
  obtain ⟨⟨_, hC'⟩, hL', hD⟩ := w0_core hFw hnu hwh hh hs
  have hR' : s.site.reg ≠ .setup → Wg0.rounds s.l0 s.l1 = Wg0.rounds d.l0 d.l1 := fun hr => by
    rw [Wg0.rounds_blocks hL' (Wg0.lens_two hr), hRd, hsw.1.2.2]
  have hvo := Wg0.vOrd_le_of hC hC' hR' htc hpl
  have agree : ∀ r < Wg0.vOrd d, voteRes X g r = voteRes X h r := fun r hr => by
    refine voteRes_same hp hX hFw hnu hw hsw ?_ ?_
    · have : vCnt X g j ≤ vCnt X g (X.tr g).length := by
        simp only [vCnt, List.take_length]; exact (List.take_sublist _ _).countP_le
      omega
    · have : vCnt X h i ≤ vCnt X h (X.tr h).length := by
        simp only [vCnt, List.take_length]; exact (List.take_sublist _ _).countP_le
      omega
  have hH : ∀ r ≤ Wg0.vOrd d, armH X g r = armH X h r := fun r hr => by
    unfold armH
    congr 1
    refine List.filter_congr fun r' hr' => ?_
    rw [agree r' (by simp only [List.mem_range] at hr'; omega)]
  have hVd : Wg0.VtOk d (voteRes X h) := fun hk ho => by
    rw [gV hk ho]
    apply agree
    simp only [Wg0.vOrd, hk, ho, ↓reduceIte]
    omega
  have hcmp := Wg0.tcOrd_le_of (w := warpW L g) hC hC' hR' htc hpl (fun r => armH_succ r) hVd
    hV gA (by rw [hWe]; exact hD)
  rw [← Wg0.tcOrd_congr hH] at hcmp
  have hb : tcBase L g = tcBase L h := by simp only [tcBase, hWe]
  rw [h1, ← hWe, ← hb]
  rcases hcmp with ⟨h3, h4⟩ | ⟨h3, h4, h5⟩
  · exact .inl ⟨h3, by omega⟩
  · exact .inr ⟨h3, h4, by omega⟩

/-- **The lag at a warp-collective event of warps 0–3**: a lane of the warp with at most the
lane's earlier collectives is no later than the lane's state. -/
theorem w0_tcLag (hw : warp L g < 4) (hsw : SameWarp L g h) {j k : Nat}
    {σ : (thread P L g).D} (hσ : Frame.stateAt (thread P L) X g j = some (some σ))
    (hk : X.TcK (g, j) k) (hle : (X.tr h).countP isTcColl ≤ k) :
    Sched.threadTime (timed P L) X h ≤ time P L g σ := by
  have hg : g < L.threads := hsw.1.1
  have hh : h < L.threads := hsw.1.2.1
  obtain ⟨hwe, hWe⟩ := warpW_same hp hsw
  have hwh : warp L h < 4 := hwe ▸ hw
  obtain ⟨⟨e, he, hce⟩, hcnt⟩ := hk
  have hub := noUb_kind hnu he
  obtain ⟨σ0, hσ0, -, -, hev, -⟩ := ev_at hp hX hFw he hub
  rw [hσ] at hσ0
  cases hσ0
  have hG := w0_tc hp hX hFw hw hg j (noUbBefore_of_noUb hnu) σ hσ
  have hall : ∀ c : Event → Bool, (X.tr h).countP c = ((X.tr h).take (X.tr h).length).countP c :=
    fun c => by rw [List.take_length]
  rcases w0_bst hFw hnu hw hg hσ with ⟨d0, n0, rfl, hxd⟩ | ⟨d, n, rfl, -⟩
  · -- a startup collective: the allocation (`k = 0`) or the relinquishment (`k = 1`), warp 0
    have hev' : Startup.Ev L g d0 e := hev
    obtain ⟨hK, hW0⟩ := w0_tcStart hp hX hFw hnu hw hg hσ hxd hev' hce hcnt
    have h92 : d0.site = .alloc → Startup.time d0 = 92 := fun hs0 => by
      unfold Startup.time; rw [hs0]
    have h98 : d0.site = .relinq → Startup.time d0 = 98 := fun hs0 => by
      rw [Startup.time_of_ne (by rw [hs0]; simp), hs0]; rfl
    have hb2 : tcBase L h = 2 := by simp [tcBase, ← hWe, hW0]
    have hst : ∀ i s n', Frame.stateAt (thread P L) X h i = some (some (.inl s, n')) →
        Startup.exitOf s = none →
        Startup.RefT s (tcCnt X h i) ∧ ∀ r, s.site ≠ .enter r := fun i s n' hs hxs => by
      obtain ⟨-, hW', hT'⟩ := (follow_iff.mp hFw h hh i).2 _ hs
      obtain ⟨h1, -⟩ := w0_tc hp hX hFw hwh hh i (noUbBefore_of_noUb hnu) _ hs
      have hc := state_count hs .tmem
      try simp only [cls] at hc
      rw [hc, ← h1] at hT'
      exact ⟨hT', fun r h => by simp [Startup.exitOf, h] at hxs⟩
    have hbar : ∀ i s n', Frame.stateAt (thread P L) X h i = some (some (.inl s, n')) →
        s.site = .bar → scmpi .ne .b s.x2 0 = false := fun i s n' hs hb => by
      obtain ⟨-, hW', -⟩ := (follow_iff.mp hFw h hh i).2 _ hs
      simp only [Startup.RefW, hb] at hW'
      rw [hW'.2.2, ← hWe]
      exact hW0
    have hwg : ∀ i s n', Frame.stateAt (thread P L) X h i = some (some (.inr ⟨.inl .wg0, s⟩, n')) →
        2 ≤ tcCnt X h i := fun i s n' hs => by
      obtain ⟨h1, -⟩ := w0_tc hp hX hFw hwh hh i (noUbBefore_of_noUb hnu) _ hs
      omega
    refine time_last (Q := fun t => t ≤ time P L g (.inl d0, n0)) (Nat.zero_le _)
      (fun σ' hs => ?_) (fun σ' f hs hf hn => ?_)
    · rcases w0_bst hFw hnu hwh hh hs with ⟨s, n', rfl, hxs⟩ | ⟨s, n', rfl, -⟩
      · obtain ⟨hT', hx'⟩ := hst _ s n' hs hxs
        have ht := Startup.time_refT hT' hx' (hbar _ s n' hs)
        have hc : tcCnt X h (X.tr h).length ≤ k := by simp only [tcCnt, ← hall]; exact hle
        simp only [time]
        rcases hK with ⟨hs0, rfl⟩ | ⟨hs0, rfl⟩
        · have := ht.1 (by omega); rw [h92 hs0]; split_ifs at this <;> omega
        · have := ht.2 hc; rw [h98 hs0]; split_ifs at this <;> omega
      · have := hwg _ s n' hs
        simp only [tcCnt, ← hall] at this
        rcases hK with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> omega
    · have hget : X.get (h, (X.tr h).length - 1) = some f := hf
      have hubf := noUb_kind hnu hget
      have hl := cnt_last hf isTcColl
      rcases w0_bst hFw hnu hwh hh hs with ⟨s, n', rfl, hxs⟩ | ⟨s, n', rfl, -⟩
      · obtain ⟨hT', hx'⟩ := hst _ s n' hs hxs
        have ht := Startup.time_refT hT' hx' (hbar _ s n' hs)
        obtain ⟨σ1, hσ1, -, -, hev1, -⟩ := ev_at hp hX hFw hget hubf
        rw [hs] at hσ1
        cases hσ1
        have hev1' : Startup.Ev L h s f := hev1
        rw [(Startup.ev_tc hx' hev1').1, Startup.ev_tmem hx' hev1'] at hl
        simp only [tcCnt] at ht
        simp only [time]
        rcases hK with ⟨hs0, rfl⟩ | ⟨hs0, rfl⟩
        · have h0 := ht.1 (by split_ifs at hl <;> omega)
          rw [h92 hs0]
          by_cases ha : s.site = .alloc
          · simp [ha] at hl; omega
          · simp only [ha, ↓reduceIte] at h0; omega
        · have h1 := ht.2 (by split_ifs at hl <;> omega)
          rw [h98 hs0]
          by_cases hr : s.site = .relinq
          · simp only [Startup.RefT, hr] at hT'
            simp [hr] at hl
            simp only [tcCnt] at hT'
            omega
          · simp only [hr, ↓reduceIte] at h1; omega
      · have := hwg _ s n' hs
        simp only [tcCnt] at this
        rcases hK with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> split_ifs at hl <;> omega
  · obtain ⟨-, hK⟩ : Wg0.Ev P L g (warpW L g) d e := hev
    have htc : d.site.isTc = true := by rw [← Wg0.evK_tc hub hK]; exact hce
    have key : ∀ i s n', Frame.stateAt (thread P L) X h i = some (some (.inr ⟨.inl .wg0, s⟩, n')) →
        Wg0.place d ≤ Wg0.place s →
        (Wg0.place d < Wg0.place s ∧ k + 1 ≤ tcCnt X h i) ∨
          (Wg0.place s = Wg0.place d ∧ s.site.isTc = true ∧ k ≤ tcCnt X h i) :=
      fun i s n' hs hpl => w0_tcKey hp hX hFw hnu hw hsw hσ htc hcnt hs hpl
    refine time_last (Q := fun t => t ≤ time P L g (.inr ⟨.inl .wg0, d⟩, n)) (Nat.zero_le _)
      (fun σ' hs => ?_) (fun σ' f hs hf hn => ?_)
    · rcases w0_bst hFw hnu hwh hh hs with ⟨s, n', rfl, hxs⟩ | ⟨s, n', rfl, -⟩
      · have := Startup.time_lt hxs
        rw [w0_time]
        simp only [time] at this ⊢
        simp only [wg0Org]
        omega
      · rw [w0_time, w0_time]
        by_contra hlt
        rcases key _ s n' hs (by omega) with ⟨-, h1⟩ | ⟨h1, -⟩
        · simp only [tcCnt, ← hall] at h1
          omega
        · omega
    · rcases w0_bst hFw hnu hwh hh hs with ⟨s, n', rfl, hxs⟩ | ⟨s, n', rfl, -⟩
      · have := Startup.time_lt hxs
        rw [w0_time]
        simp only [time] at this ⊢
        simp only [wg0Org]
        omega
      · rw [w0_time, w0_time]
        by_contra hlt
        have hget : X.get (h, (X.tr h).length - 1) = some f := hf
        have hubf := noUb_kind hnu hget
        obtain ⟨σ1, hσ1, -, -, hev1, -⟩ := ev_at hp hX hFw hget hubf
        rw [hs] at hσ1
        cases hσ1
        obtain ⟨-, hK1⟩ : Wg0.Ev P L h (warpW L h) s f := hev1
        have hl := cnt_last hf isTcColl
        rw [Wg0.evK_tc hubf hK1] at hl
        rcases key _ s n' hs (by omega) with ⟨-, h1⟩ | ⟨-, h2, h1⟩
        · simp only [tcCnt] at h1
          split_ifs at hl <;> omega
        · simp only [tcCnt] at h1
          simp only [h2, ↓reduceIte] at hl
          omega

end

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
