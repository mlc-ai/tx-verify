-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Progress.LibTmem1Lanes
public import Lemmas.Step.TmemPair

@[expose] public section

/-!
# A `cta_group::1` operation whose 32 lanes have arrived is recorded (promotion candidate)

The library's `Step.warp_entry_counted` records a `cta_group::1` request when its warp's lanes all
sit at the operation, none covered, the earlier requests of the warp are covered, and the
allocator's replay accepts it. For a kernel whose Tensor Memory operations are one warp's
(`Tmem1Ops`: alloc of 512 columns, relinquish, dealloc, by shape), `tmem1_step` derives those
premises from the lanes having made their `n`-th operation: a thread that has made an operation
and a later event has had the operation performed (DEP-TMEM-ALLOC-WAIT), so every earlier request
is recorded and covered; every record of the CTA's history is an earlier request, so the history
is empty at an allocation and the other two requests are never blocked by the allocator
(`perform_ne_blocked`).

The statement of `tmem1_step`: for an unperformed `n`-th operation `(g, j)`, a counted extension
covers it, or a lane of its warp has made at most `n` operations.

Promote to `Lemmas/Tmem/PairProtocol.lean`, next to `pair_ready`.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Tmem1
open PTX Tmem.Pair Step

noncomputable section

variable {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0} {X : Execution} {w : Nat}

/-- The lane threads of the warp of `g` are launched threads of its warp. -/
theorem warpThread_mem (hg : g < L.threads) (hb : L.block % 32 = 0) {t : Nat} (ht : t < 32) :
    warpThread L g t < L.threads ∧ SameWarp L g (warpThread L g t) := by
  have hB : 0 < L.block := by
    rcases Nat.eq_zero_or_pos L.block with h | h
    · simp [Launch.threads, h] at hg
    · exact h
  have hr : g % L.block < L.block := Nat.mod_lt _ hB
  have hq : g / L.block < L.grid :=
    (Nat.div_lt_iff_lt_mul hB).mpr (by simpa [Launch.threads] using hg)
  have hlt : g % L.block / 32 * 32 + t < L.block := by omega
  have e : warpThread L g t = (g % L.block / 32 * 32 + t) + L.block * (g / L.block) := by
    simp only [warpThread]; ring
  have hdiv : warpThread L g t / L.block = g / L.block := by
    rw [e, Nat.add_mul_div_left _ _ hB, Nat.div_eq_of_lt hlt]; simp
  have hmod : warpThread L g t % L.block = g % L.block / 32 * 32 + t := by
    rw [e, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]
  have hthr : warpThread L g t < L.threads := by
    simp only [Launch.threads]
    have : g / L.block + 1 ≤ L.grid := hq
    nlinarith [Nat.div_add_mod' (warpThread L g t) L.block]
  refine ⟨hthr, ⟨⟨hg, hthr, hdiv.symm⟩, ?_⟩⟩
  rw [hmod]
  omega

/-- A lane's event is the warp request's event of that lane, for every thread of the warp of a
participating lane. -/
theorem participates_warp {grp : CtaGroup} {r : WarpRequest} (hv : r.Valid L X grp) {f : EvId}
    (hp : Participates L r f) {h : Nat} (hsw : SameWarp L f.1 h) :
    ∃ l : Fin 32, r.event L l = (h, r.indices l) := by
  obtain ⟨l0, rfl⟩ := hp
  obtain ⟨p1, p2, -⟩ := WarpRequest.event_props hv l0
  have hcta : h / L.block = r.cta := by rw [← hsw.1.2.2, p1]
  have hwarp : h % L.block / 32 = r.warp := by rw [← hsw.2, p2]
  refine ⟨⟨h % L.block % 32, Nat.mod_lt _ (by decide)⟩, ?_⟩
  have e1 := Nat.div_add_mod h L.block
  have e2 := Nat.div_add_mod (h % L.block) 32
  rw [hcta] at e1
  rw [hwarp] at e2
  show (r.cta * L.block + r.warp * 32 + h % L.block % 32, r.indices _) = (h, r.indices _)
  rw [Nat.mul_comm r.cta]
  congr 1
  omega

/-- **A lane's `n`-th operation performed means every lane's is**: a record is a valid warp
request, whose lanes' events are one collective instance. -/
theorem performed_all (hX : Consistent L K A mem0 X) (ht : Tmem1Ops L X w)
    (htc : ¬ AlignedMismatch L K X) {g h n j jh : Nat} (hw : SameWarp L g h)
    (hopg : TmemOp X g n j) (hoph : TmemOp X h n jh) (hp : Performed L X (h, jh)) :
    Performed L X (g, j) := by
  obtain ⟨cta, r, hr, hpa⟩ := hp
  have hv := ((hX.tmemPair.1 cta).1 r hr).2.2
  obtain ⟨k', hk'⟩ := hv.2.2.2
  obtain ⟨l0, hl0⟩ := hpa
  have hkk : k' = tcCount X h jh := by
    have := (hk' l0).2
    rw [hl0] at this
    exact this.symm
  have hsame := tcCount_eq1 ht htc hw hopg hoph
  obtain ⟨l, hl⟩ := participates_warp hv ⟨l0, hl0⟩ ⟨⟨hw.1.2.1, hw.1.1, hw.1.2.2.symm⟩, hw.2.symm⟩
  have hk2 := hk' l
  rw [hl] at hk2
  have hj : r.own.indices l = j := by
    have hA : X.TcK (g, r.own.indices l) k' := hk2
    have hB : X.TcK (g, j) k' := by rw [hkk, ← hsame]; exact tcK_of_op hopg
    exact Execution.TcK.unique hA hB
  exact ⟨cta, r, hr, l, by rw [hl, hj]⟩

/-- **An unperformed `n`-th operation of a warp is recorded, or a lane of the warp has not made
it**: if every lane of the warp has made its `n`-th operation, the owner warp's record is ready
(`Step.warp_entry_counted`), and recording it is a counted extension that covers the operation;
otherwise a lane has made at most `n` operations. -/
theorem tmem1_step (hX : Consistent L K A mem0 X) (ht : Tmem1Ops L X w)
    (htc : ¬ AlignedMismatch L K X) (hb : L.block % 32 = 0) {g n j : Nat} (hg : g < L.threads)
    (hop : TmemOp X g n j) (hnp : ¬ Performed L X (g, j))
    (hasm : ∀ a ∈ A, ∀ c r, a.wf L mem0 (X.recordEntry c r)) :
    (∃ Y, Consistent L K A mem0 Y ∧ X.le Y ∧ Covered L Y (g, j) ∧ X.size L < Y.size L) ∨
      ∃ h, SameWarp L g h ∧ tmemOps (X.tr h) ≤ n := by
  by_cases hall : ∀ h, SameWarp L g h → n < tmemOps (X.tr h)
  swap
  · right
    push Not at hall
    exact hall
  left
  have hlane : ∀ t : Fin 32,
      warpThread L g t.val < L.threads ∧ SameWarp L g (warpThread L g t.val) :=
    fun t => warpThread_mem hg hb t.isLt
  choose jt hjt using fun t : Fin 32 => tmemOp_exists (hall _ (hlane t).2)
  obtain ⟨pc, grp, dst, act, hge⟩ := hop.1
  obtain ⟨hwg, rfl, hsh0⟩ := ht.event hg hge
  have hsh : TmemShape n act := hop.2 ▸ hsh0
  have hgl : j + 1 = (X.tr g).length := last_of_not_performed hX hge hnp
  have hperf : ∀ t : Fin 32, ¬ Performed L X (warpThread L g t.val, jt t) :=
    fun t hp => hnp (performed_all hX ht htc (hlane t).2 hop (hjt t) hp)
  have hlast : ∀ t : Fin 32, jt t + 1 = (X.tr (warpThread L g t.val)).length := by
    intro t
    obtain ⟨pc', grp', dst', act', hget⟩ := (hjt t).1
    exact last_of_not_performed hX hget (hperf t)
  have hsame : ∀ t : Fin 32, X.get (warpThread L g t.val, jt t) = X.get (g, j) :=
    fun t => (lanes_same_event1 ht htc (hlane t).2 hop (hjt t)).symm
  have hops : ∀ t : Fin 32, X.get (warpThread L g t.val,
      (X.tr (warpThread L g t.val)).length - 1) =
        some ⟨pc, .tc (.resource .one dst (actOf act).request)⟩ := by
    intro t
    have h1 : (X.tr (warpThread L g t.val)).length - 1 = jt t := by have := hlast t; omega
    rw [h1, hsame t, actOf_request]
    exact hge
  have hk : ∃ k, ∀ t : Fin 32,
      X.TcK (warpThread L g t.val, (X.tr (warpThread L g t.val)).length - 1) k := by
    refine ⟨tcCount X g j, fun t => ?_⟩
    have h1 : (X.tr (warpThread L g t.val)).length - 1 = jt t := by have := hlast t; omega
    rw [h1, tcCount_eq1 ht htc (hlane t).2 hop (hjt t)]
    exact tcK_of_op (hjt t)
  have hfree : ∀ t : Fin 32,
      ¬ Covered L X (warpThread L g t.val, (X.tr (warpThread L g t.val)).length - 1) := by
    intro t hc
    have h1 : (X.tr (warpThread L g t.val)).length - 1 = jt t := by have := hlast t; omega
    rw [h1] at hc
    exact hperf t (hc.performed hX.tmemPair)
  have hw0 : warpThread L g 0 = g / L.block * L.block + w * 32 := by
    simp [warpThread, hwg]
  -- every record of the CTA's history is of an earlier operation
  have hbefore : ∀ x ∈ X.tmemHistory (g / L.block),
      opsAt X (warpThread L g 0) (x.own.indices 0) < n := by
    intro x hx
    obtain ⟨hc, hw1, hg1, hreq, hget, hsh'⟩ := record_info hX ht hx
    rw [← hw0] at hget hsh'
    obtain ⟨⟨pc1, grp1, dst1, act1, he1⟩, -⟩ : TmemOp X (warpThread L g 0) _ (x.own.indices 0) :=
      ⟨⟨_, _, _, _, hget⟩, rfl⟩
    have hlt1 : x.own.indices 0 < (X.tr (warpThread L g 0)).length := len_of_get hget
    rcases Nat.lt_trichotomy (opsAt X (warpThread L g 0) (x.own.indices 0)) n with h | h | h
    · exact h
    · exfalso
      have hu := tmemOp_unique (⟨⟨_, _, _, _, hget⟩, h⟩ : TmemOp X (warpThread L g 0) n _)
        (hjt 0)
      refine hperf 0 ⟨g / L.block, x, hx, 0, ?_⟩
      simp only [WarpRequest.event, hc, hw1, Fin.val_zero, Nat.add_zero]
      rw [hu, hw0]
    · exfalso
      have := tmemOp_lt (hjt 0) (⟨⟨_, _, _, _, hget⟩, rfl⟩ : TmemOp X (warpThread L g 0) _ _) h
      have h2 := hlast 0
      simp only [Fin.val_zero] at h2
      omega
  have hready : CompletionReady L X
      [(ownerRecord L X g pc dst (actOf act)).own] := by
    intro w0 hw0' w' grp' hv' hbef i hi
    rw [List.mem_singleton] at hw0'
    subst hw0'
    obtain ⟨hcta, hwarp, hidx⟩ := hbef
    simp only [ownerRecord, warpRequest] at hcta hwarp hidx
    have hev : w'.event L 0 = (warpThread L g 0, w'.indices 0) := by
      simp [WarpRequest.event, hcta, hwarp, warpThread]
    have hget := hv'.2.2.1 0
    have hlt : (w'.event L 0).2 + 1 < (X.tr (w'.event L 0).1).length := by
      rw [hev]
      have := hidx 0
      simp only [Fin.val_zero] at this ⊢
      omega
    obtain ⟨cta, x, hx, l, hxl⟩ := hX.tmemPairBlocking.performed hget hlt
    have hxv := ((hX.tmemPair.1 cta).1 x hx).2.2
    have hxw : x.own = w' := hxv.ext hv' hxl
    obtain ⟨-, -, hxg, -⟩ := record_info hX ht (r := x) (cta := cta) hx
    exact ⟨[x.own], .inl ⟨cta, x, hx, hxg, rfl⟩, x.own, List.mem_singleton_self _, by
      rw [hxw]; exact hi⟩
  have hrun : runRequests {} (X.tmemHistory (g / L.block) ++
      [ownerRecord L X g pc dst (actOf act)]) ≠ .blocked := by
    apply Tmem.Pair.run_append_ne_blocked (hX.tmemPair.1 _).2.2
    intro st hst
    show Tmem.perform st (actOf act) ≠ .blocked
    by_cases hn0 : n = 0
    · subst hn0
      have hnil : X.tmemHistory (g / L.block) = [] := by
        apply List.eq_nil_iff_forall_not_mem.mpr
        intro x hx
        have := hbefore x hx
        omega
      rw [hnil] at hst
      simp only [runRequests, Tmem.Outcome.done.injEq] at hst
      subst hst
      simp only [TmemShape] at hsh
      rw [hsh]
      exact Tmem.Pair.perform_empty_alloc 512
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      apply Tmem.Pair.perform_ne_blocked
      intro a c h
      rcases m with _ | _ | m
      · simp only [TmemShape] at hsh
        rw [hsh] at h
        cases h
      · obtain ⟨b, hb'⟩ := hsh
        rw [hb'] at h
        cases h
      · exact hsh.elim
  obtain ⟨Y, hY, hle, hcov, hsize⟩ := warp_entry_counted hX hg hb hops hk hfree hready hrun
    (hasm · · _ _)
  refine ⟨Y, hY, hle, ?_, hsize⟩
  have : (X.tr g).length - 1 = j := by omega
  rw [this] at hcov
  exact hcov

end

end PTX.Kernels.InklingRelDecode.Proof.Tmem1
