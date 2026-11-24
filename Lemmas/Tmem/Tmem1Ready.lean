-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Tmem.Tmem1Protocol
public import Lemmas.Kernel.Progress.Blocked

@[expose] public section

/-! # A `cta_group::1` operation all lanes of its warp have made is ready

When every lane of the warp has made the collective of an operation that its CTA's allocator has
not performed, the lanes' events are one request (ERR-ALIGNED-MISMATCH), every operation of the
warp before it is performed (a lane's non-last operation is, `last_of_not_performed`), and the
allocator can perform it (`entry_ready`): an allocation finds it empty. -/

namespace PTX.Tmem.One
open PTX PTX.Proof Tmem.Pair

noncomputable section

variable {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0} {X : Execution} {w : Nat}

/-- A performed operation is covered (no operation of group two exists). -/
theorem covered_of_performed (hX : Consistent L K A mem0 X) (ht : Tmem1Ops L X w) {i : EvId}
    (h : Performed L X i) : Covered L X i := by
  obtain ⟨cta, r, hr, hp⟩ := h
  exact ⟨[r.own], .inl ⟨cta, r, hr, (record_info hX ht hr).2.2.1, rfl⟩, r.own,
    List.mem_singleton_self _, hp⟩

/-- **A ready operation.** -/
theorem entry_ready (hX : Consistent L K A mem0 X) (ht : Tmem1Ops L X w)
    (hlaunch : L.oneDimLaunch)
    (htc : ¬ AlignedMismatch L K X) {g k pc : Nat} {grp : CtaGroup} {dst : Option Loc}
    {act : Tmem.Request} (hg : g < L.threads)
    (he : X.get (g, (X.tr g).length - 1) = some ⟨pc, .tc (.resource grp dst act)⟩)
    (hn : ¬ Performed L X (g, (X.tr g).length - 1)) (hk : X.TcK (g, (X.tr g).length - 1) k)
    (hall : ∀ h, h < L.threads → SameWarp L g h → ∃ j, X.TcK (h, j) k) :
    ∃ c r, Step.EntryReady L X c r := by
  obtain ⟨hgw, rfl, hshape⟩ := ht.event hg he
  have hwb := ht.warp_lt
  have hB : 0 < L.block := by omega
  have hd := Nat.div_add_mod' g L.block
  have hm := Nat.mod_lt g hB
  -- the lanes of the warp
  have hlane : ∀ ℓ : Fin 32, g / L.block * L.block + w * 32 + ℓ.val < L.threads ∧
      SameWarp L g (g / L.block * L.block + w * 32 + ℓ.val) := by
    intro ℓ
    have hℓ := ℓ.isLt
    have hq : g / L.block < L.grid := (Nat.div_lt_iff_lt_mul hB).mpr hg
    have hd' : (g / L.block * L.block + w * 32 + ℓ.val) / L.block = g / L.block := by
      rw [Nat.add_assoc, Nat.add_comm, Nat.add_mul_div_right _ _ hB,
        Nat.div_eq_of_lt (by omega), Nat.zero_add]
    have hm' : (g / L.block * L.block + w * 32 + ℓ.val) % L.block = w * 32 + ℓ.val := by
      rw [Nat.add_assoc, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
    have hlt : g / L.block * L.block + w * 32 + ℓ.val < L.threads := by
      have := Nat.mul_le_mul_right L.block (show g / L.block + 1 ≤ L.grid by omega)
      rw [Nat.succ_mul] at this
      simp only [Launch.threads]
      omega
    refine ⟨hlt, ⟨⟨hg, hlt, hd'.symm⟩, ?_⟩⟩
    rw [hm', hgw]
    omega
  -- their events are the thread's
  have hev : ∀ ℓ : Fin 32, ∃ j, X.TcK (g / L.block * L.block + w * 32 + ℓ.val, j) k ∧
      X.get (g / L.block * L.block + w * 32 + ℓ.val, j) =
        some ⟨pc, .tc (.resource .one dst act)⟩ := by
    intro ℓ
    obtain ⟨hlt, hsw⟩ := hlane ℓ
    obtain ⟨j, hj⟩ := hall _ hlt hsw
    refine ⟨j, hj, ?_⟩
    obtain ⟨⟨ev, hget, hcoll⟩, -⟩ := id hj
    obtain ⟨pc', kd⟩ := ev
    cases kd <;> simp only [isTcColl, Bool.false_eq_true] at hcoll
    rename_i kf
    have hst : pc = pc' ∧ tcStatic (.resource .one dst act) = tcStatic kf := by
      by_contra hne
      apply htc
      refine ⟨.tc, .inl ((AlignedClass.divergent_tc_iff L).mpr
        ⟨(g, (X.tr g).length - 1), (_, j), _, _, _, _, _, hsw, hk, hj, he, hget, ?_⟩)⟩
      by_cases hp : pc = pc'
      · exact .inr fun h => hne ⟨hp, h⟩
      · exact .inl hp
    obtain ⟨rfl, hst⟩ := hst
    rw [hget]
    cases kf <;> simp_all [tcStatic]
  choose idx hidx using hev
  let q : WarpRequest := ⟨g / L.block, w, idx, pc, dst, act⟩
  have hqe : ∀ ℓ : Fin 32, q.event L ℓ =
      (g / L.block * L.block + w * 32 + ℓ.val, idx ℓ) := fun ℓ => rfl
  have hqv : q.Valid L X .one := by
    refine ⟨(Nat.div_lt_iff_lt_mul hB).mpr hg, hwb, fun ℓ => ?_, k, fun ℓ => ?_⟩
    · rw [hqe]; exact (hidx ℓ).2
    · rw [hqe]; exact (hidx ℓ).1
  -- the thread is one of the lanes
  have hgl : ∃ ℓ : Fin 32, q.event L ℓ = (g, (X.tr g).length - 1) := by
    refine ⟨⟨g % L.block % 32, Nat.mod_lt _ (by decide)⟩, ?_⟩
    have hgg : g / L.block * L.block + w * 32 + g % L.block % 32 = g := by
      rw [← hgw]
      omega
    have h1 := (hidx ⟨g % L.block % 32, Nat.mod_lt _ (by decide)⟩).1
    rw [hqe]
    simp only [hgg] at h1 ⊢
    exact Prod.ext rfl (h1.unique hk)
  have hnew : ∀ x ∈ X.tmemHistory (g / L.block), x.own ≠ q := by
    intro x hx hxq
    obtain ⟨ℓ, hℓ⟩ := hgl
    exact hn ⟨_, x, hx, ℓ, by rw [hxq]; exact hℓ⟩
  have hnp : ∀ ℓ, ¬ Performed L X (q.event L ℓ) := by
    rintro ℓ ⟨cta, x, hx, l', hl'⟩
    have hxq : x.own = q := ((hX.tmemPair.1 cta).1 x hx).2.2.ext hqv hl'
    have hc : cta = g / L.block := by rw [← (hX.tmemPair.1 cta).2.1 x hx, hxq]
    subst hc
    exact hnew x hx hxq
  have hlast : ∀ ℓ, (q.event L ℓ).2 + 1 = (X.tr (q.event L ℓ).1).length :=
    fun ℓ => Step.last_of_not_performed hX (hqv.2.2.1 ℓ) (hnp ℓ)
  refine ⟨g / L.block, ⟨q, .one, actOf q.request⟩,
    ⟨Launch.oneDimLaunch_clusterGridValid hlaunch, actOf_request _, hqv⟩,
      fun _ => ?_, hnew, rfl, ?_⟩
  · -- the operations before it are covered
    intro w1 hw1 w' group hv' hb i hi
    rw [List.mem_singleton.mp hw1] at hb
    obtain ⟨ℓ, rfl⟩ := hi
    refine covered_of_performed hX ht (hX.tmemPairBlocking.performed (hv'.2.2.1 ℓ) ?_)
    have hth : (w'.event L ℓ).1 = (q.event L ℓ).1 := by
      simp only [WarpRequest.event, hb.1, hb.2.1]
    have hix : (w'.event L ℓ).2 < (q.event L ℓ).2 := hb.2.2 ℓ
    have := hlast ℓ
    rw [hth]
    omega
  · apply Tmem.Pair.run_append_ne_blocked (hX.tmemPair.1 _).2.2
    intro st hst
    show Tmem.perform st (actOf act) ≠ .blocked
    by_cases ha : ∃ n, act = .alloc n
    · obtain ⟨n, rfl⟩ := ha
      obtain ⟨h0, rfl⟩ := shape_alloc hshape
      have hnil : X.tmemHistory (g / L.block) = [] := by
        apply List.eq_nil_iff_forall_not_mem.mpr
        intro x hx
        obtain ⟨hxc, hxw, -, -, hxe, hxs⟩ := record_info hX ht hx
        have hq0 := (hidx 0).2
        have hq0s := (ht.event (hlane 0).1 hq0).2.2
        obtain ⟨hq0n, -⟩ := shape_alloc hq0s
        simp only [Fin.val_zero, Nat.add_zero] at hq0 hq0n
        have hx0 : x.own.event L 0 = (g / L.block * L.block + w * 32, x.own.indices 0) := by
          simp [WarpRequest.event, hxc, hxw]
        have hl0 := hlast 0
        rw [hqe] at hl0
        simp only [Fin.val_zero, Nat.add_zero] at hl0
        have hxl : x.own.indices 0 < (X.tr (g / L.block * L.block + w * 32)).length :=
          len_of_get hxe
        rcases Nat.lt_or_ge (x.own.indices 0) (idx 0) with hlt | hge
        · have := tmemOps_lt hxe rfl hlt
          omega
        · have hi : x.own.indices 0 = idx 0 := by omega
          refine hnp 0 ⟨_, x, hx, 0, ?_⟩
          rw [hx0, hqe, hi]
          simp
      rw [hnil] at hst
      simp only [runRequests, Tmem.Outcome.done.injEq] at hst
      subst hst
      exact Tmem.Pair.perform_empty_alloc 512
    · apply Tmem.Pair.perform_ne_blocked
      intro a c h
      cases act <;> simp_all [actOf]

end
end PTX.Tmem.One
