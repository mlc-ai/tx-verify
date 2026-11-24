-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsCollShapePc

@[expose] public section

/-! # The steps into a warp collective from a blocking kind

The last event before a warp collective is fired from the state before it, and it has that state's
kind (`fires_unblocking`): it never blocks unless the kind is a cluster-barrier operation, a
register request, a named barrier, a warp-collective `tcgen05` event or a bulk async-group wait
(`Blocking`); no kind fires a `cp.async` group wait (`KindTmpl`). A machine steps from a state of
such a kind to a warp-collective state only in two places (`pred_blocking`): the loader from its
`setmaxnreg` to the broadcast of its first item, and a softmax thread from its second
`tcgen05.wait::st` of a tile to the tile's warp barrier, which is reached from nowhere else
(`soft_pred`). The prologue's cluster operations lead to the cluster wait and to the roles' requests
(`pro_succ`), the store warp makes no warp collective, the MMA warp's allocation, barriers and
deallocation to non-collective sites (`mma_pred`), the correction warps' barriers, loads and stores
neither (`corr_pred`). The loader reaches its first broadcast only from its request
(`loader_head_pred`), and no other loader warp collective has the broadcast's time `base`
(`loader_base`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Proof PTX.Flow Cross Progress.Time

noncomputable section
set_option maxRecDepth 100000

variable {L : Launch}

namespace Sched

/-- The kinds of events that may block a thread (`Step.Released`). -/
def Blocking (k : NextKind) : Prop :=
  k = .cluster ∨ k = .reg ∨ k = .bar ∨ k = .tmem ∨ k = .tcLoad ∨ k = .tcStore ∨ k = .bulkWait

/-- An event of a template of a kind that does not block never blocks. -/
theorem fires_unblocking {pc : Nat} {k : NextKind} {m : Tmpl} {e : Event} {o : Option TState}
    (hk : KindTmpl k m) (hf : Fires pc m e o) (hb : ¬ Blocking k) : Sched.Unblocking e.kind := by
  cases k <;> simp only [Blocking, reduceCtorEq, or_self, or_false, false_or, not_true_eq_false,
    not_false_eq_true] at hb
  all_goals simp only [KindTmpl] at hk
  all_goals (try casesm* _ ∨ _, ∃ _, _, _ ∧ _)
  all_goals subst_vars
  all_goals simp only [Fires] at hf
  all_goals (try casesm* _ ∨ _, ∃ _, _, _ ∧ _)
  all_goals subst_vars
  all_goals simp [Sched.Unblocking, isTcColl]

set_option maxHeartbeats 4000000 in
/-- A softmax thread steps to a warp collective from a state of a blocking kind, or to a warp
barrier, only from the tile's second `tcgen05.wait::st` to its warp barrier. -/
theorem soft_pred {g : Nat} {d d' : Softmax.D} {e : Event}
    (hn : Softmax.next L g d e = some (some d')) (hk : softmaxKind d'.site = .warp)
    (hb : Blocking (softmaxKind d.site) ∨ ∃ lp, d'.site = .warpBar lp) :
    ∃ lp, d.site = .pwait lp 1 ∧ d'.site = .warpBar lp := by
  obtain ⟨site, i, t, w, m, l⟩ := d
  rcases site with _ | _ | w' | lp | ⟨lp, c⟩ | ⟨lp, c⟩ | _ | j | ⟨lp, c⟩ | ⟨lp, h⟩ | lp |
    lp | lp | lp | _ | _ | _
  all_goals (try rcases Softmax.fin4_cases w' with rfl | rfl | rfl | rfl)
  all_goals (try rcases Softmax.fin3_cases j with rfl | rfl | rfl)
  all_goals (try rcases Softmax.fin4_cases c with rfl | rfl | rfl | rfl)
  all_goals (try rcases Softmax.fin2_cases h with rfl | rfl)
  all_goals simp only [Softmax.next, Softmax.nextItem, Softmax.afterStats,
    Softmax.afterLoad] at hn
  all_goals repeat' (first | split_ifs at hn | split at hn)
  all_goals (try simp only [Option.some.injEq, reduceCtorEq] at hn)
  all_goals (try subst hn)
  all_goals simp_all [softmaxKind, Blocking]

set_option maxHeartbeats 4000000 in
/-- The correction machine steps to a warp collective from no state of a blocking kind. -/
theorem corr_pred {g : Nat} {d d' : Correction.D} {e : Event}
    (hn : Correction.next L g d e = some (some d')) (hk : corrKind d'.site = .warp)
    (hb : Blocking (corrKind d.site)) : False := by
  obtain ⟨site, i, t, aw, a, o⟩ := d
  rcases site with _ | _ | st0 | ⟨st0, gen⟩ | a0 | st0 | st0 | ⟨st0, j0⟩ | ⟨st0, j0⟩ |
    ⟨st0, j0⟩ | st0 | ⟨st0, fin⟩ | st0 | st0 | st0 | ⟨st0, j0⟩ | ⟨st0, j0⟩ |
    ⟨st0, j0, h0, el0⟩ | st0 | st0 | _ | _ | _
  all_goals (try (exfalso; simp [corrKind, Blocking] at hb; done))
  all_goals (try fin_cases st0)
  all_goals (try cases gen)
  all_goals simp only [Correction.next] at hn
  all_goals repeat' (first | split_ifs at hn | split at hn)
  all_goals (try simp only [Option.some.injEq, reduceCtorEq] at hn)
  all_goals (try subst hn)
  all_goals simp_all [corrKind]

/-- The MMA machine steps to a warp collective from no state of a blocking kind. -/
theorem mma_pred {g : Nat} {d d' : Mma.D} {e : Event}
    (hn : Mma.next L g d e = some (some d')) (hk : mmaKind d'.site = .warp)
    (hb : Blocking (mmaKind d.site)) : False := by
  obtain ⟨site, i, t, b, pro⟩ := d
  cases site <;> (try (exfalso; simp [mmaKind, Blocking] at hb; done))
  all_goals simp only [Mma.next] at hn
  all_goals (try split_ifs at hn)
  all_goals simp only [Option.some.injEq] at hn
  all_goals subst hn
  all_goals simp [mmaKind] at hk

/-- The loader steps to a warp collective from a state of a blocking kind only from its
`setmaxnreg`, to the broadcast of its first item. -/
theorem loader_pred {g : Nat} {d d' : Loader.D} {e : Event}
    (hn : Loader.next L g d e = some (some d')) (hk : loaderKind d'.site = .warp)
    (hb : Blocking (loaderKind d.site)) : d'.site = .head ∧ d'.i = 0 := by
  obtain ⟨site, i, t, s, ph, qp⟩ := d
  cases site <;> (try (exfalso; simp [loaderKind, Blocking] at hb; done))
  simp only [Loader.next] at hn
  split_ifs at hn <;> simp only [Option.some.injEq] at hn <;> subst hn
  · exact ⟨rfl, rfl⟩
  · simp [loaderKind] at hk

/-- A role's first state is at its register request. -/
theorem start_reg {g : Nat} {k : RoleKind} {r : Role} (h : Role.start L g k = some r) :
    nextKind (.inr r) = .reg := by
  cases k <;> simp only [Role.start, Option.some.injEq] at h <;> subst h <;> rfl

/-- A prologue step to a warp collective stays in the prologue. -/
theorem pro_succ {g : Nat} {p : Prologue.D} {e : Event} {d : ThreadD}
    (hn : (code L g).next (.inl p) e = some (some d)) (hk : nextKind d = .warp) :
    ∃ p', d = .inl p' := by
  simp only [code, Option.map_eq_some_iff] at hn
  obtain ⟨o, -, ho⟩ := hn
  rcases o with _ | (p' | k)
  · cases ho
  · simp only [Option.bind_some, handoff, Option.some.injEq] at ho
    exact ⟨p', ho.symm⟩
  · simp only [Option.bind_some, handoff, Option.map_eq_some_iff] at ho
    obtain ⟨r, hr, rfl⟩ := ho
    rw [start_reg hr] at hk
    cases hk

/-- **No machine steps from a blocking kind to a warp collective**, but the loader to its first
item's broadcast and a softmax thread to a warp barrier. -/
theorem pred_blocking {g : Nat} {d0 d : ThreadD} {e : Event}
    (hn : (code L g).next d0 e = some (some d)) (hk : nextKind d = .warp)
    (hb : Blocking (nextKind d0)) : (∃ l, d = .inr (.loader l) ∧ l.site = .head ∧ l.i = 0) ∨
      ∃ s lp, d = .inr (.softmax s) ∧ s.site = .warpBar lp := by
  rcases d0 with p | r
  · obtain ⟨p', rfl⟩ := pro_succ hn hk
    obtain ⟨s⟩ := p
    cases s <;> simp only [nextKind, prologueKind, Blocking, reduceCtorEq, or_self,
      or_false] at hb
    all_goals simp only [code, Prologue.next, Option.map_some, Option.bind_some, handoff,
      Option.some.injEq, Option.map_eq_some_iff, reduceCtorEq] at hn
    · obtain rfl := Sum.inl.inj hn
      simp [nextKind, prologueKind] at hk
    · obtain ⟨r, -, h⟩ := hn
      cases h
  · obtain ⟨r', rfl, hkr⟩ := code_next_inr hn
    cases r <;> cases r' <;> simp only [Role.kind, reduceCtorEq] at hkr
    all_goals rename_i x y
    · obtain ⟨site⟩ := y
      cases site <;> simp [nextKind, idleKind] at hk
    · exact .inl ⟨y, rfl, loader_pred (next_role (fun _ _ h => by cases h; rfl) hn) hk hb⟩
    · exact (mma_pred (next_role (fun _ _ h => by cases h; rfl) hn) hk hb).elim
    · cases hs : y.site <;> simp [nextKind, storeKind, hs] at hk
    · obtain ⟨lp, -, hs'⟩ := soft_pred (next_role (fun _ _ h => by cases h; rfl) hn) hk (.inl hb)
      exact .inr ⟨y, lp, rfl, hs'⟩
    · exact (corr_pred (next_role (fun _ _ h => by cases h; rfl) hn) hk hb).elim

/-- The loader steps to the broadcast of its first item only from its `setmaxnreg`. -/
theorem loader_head_pred {g : Nat} {d d' : Loader.D} {e : Event}
    (hn : Loader.next L g d e = some (some d')) (hs : d'.site = .head) (hi : d'.i = 0) :
    d.site = .setMaxReg := by
  obtain ⟨site, i, t, s, ph, qp⟩ := d
  cases site
  · rfl
  all_goals exfalso
  all_goals simp only [Loader.next, Loader.afterCopy, Loader.afterUse,
    Loader.afterUse.itemEndOf] at hn
  all_goals repeat' (first | split_ifs at hn | split at hn)
  all_goals (try simp only [Option.some.injEq, reduceCtorEq] at hn)
  all_goals (try subst hn)
  all_goals simp_all

/-- The only loader warp collective at time `base` is the first item's broadcast. -/
theorem loader_base {n T : Nat} {d : Loader.D} (hk : loaderKind d.site = .warp)
    (h : Progress.Time.loader n T d = base) : d.site = .head ∧ d.i = 0 := by
  obtain ⟨site, i, t, s, ph, qp⟩ := d
  cases site <;> simp only [loaderKind, reduceCtorEq] at hk
  · simp only [Progress.Time.loader, loaderUse, slotTime, gslot, bandL] at h
    refine ⟨rfl, show i = 0 from ?_⟩
    have h0 : span * (i * (n + 1) + 0) = 0 := by omega
    simp only [Nat.add_zero, Nat.mul_eq_zero, span] at h0
    omega
  all_goals simp only [Progress.Time.loader, loaderUse, slotTime, tailTime, bandL] at h
  all_goals omega

end Sched

end
end PTX.Kernels.FlashAttn4Fwd.Proof
