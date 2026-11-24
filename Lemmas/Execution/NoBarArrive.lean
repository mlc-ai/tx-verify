-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Execution.EventFrameBase
public import Core.Assembly.Execution
public import Lemmas.Flow.Hooks

@[expose] public section

/-!
# Kernels without `bar.arrive`

If no instruction of a kernel is a `bar.arrive` (`Kernel.NoBarArrive`, checked by `rfl`), no
possible execution has a `bar.arrive` event (`Consistent.noBarArrive`): every CTA barrier event
is a `bar.sync` arrival, and the rules for `bar.arrive` (`BarArriveMismatch`, the arrive half of
`CtaBarBlocking`) are vacuous.
-/

namespace PTX

def Op.isBarArrive : Op → Bool
  | .barArrive .. => true
  | _ => false

/-- No instruction of `K` is a `bar.arrive`; checked by `rfl`. -/
def Kernel.NoBarArrive (K : Kernel) : Prop := K.code.all (fun ins => !ins.op.isBarArrive) = true

/-- A template that fires no `bar.arrive` event. -/
def Tmpl.NotBarArrive : Tmpl → Prop
  | .bar _ _ _ .arrive => False
  | _ => True

section
variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat}

theorem widen_notBarArrive {pc : Nat} {m : Tmpl} (h : m.NotBarArrive) :
    (widenMbarScope A pc m).NotBarArrive := by
  unfold widenMbarScope
  split
  · cases m <;> first
      | exact h
      | (split <;> trivial)
  · exact h

/-- An `if` of two templates that fire no `bar.arrive` fires none. -/
theorem ite_notBarArrive {c : Prop} [Decidable c] {a b : Tmpl} (ha : a.NotBarArrive)
    (hb : b.NotBarArrive) : (if c then a else b).NotBarArrive := by
  by_cases hc : c
  · rwa [ite_eq_left hc]
  · rwa [ite_eq_right hc]

theorem thenWaitLd_notBarArrive {pc : Nat} {m : Tmpl} (h : m.NotBarArrive) :
    (m.thenWaitLd pc).NotBarArrive :=
  Flow.thenWaitLd_of (P := Tmpl.NotBarArrive) (fun _ _ _ _ _ h => h) m pc h

theorem ofExec_notBarArrive {r : Exec Tmpl} (h : PTX.EventFrame.AllOk Tmpl.NotBarArrive r) :
    (ofExec r).NotBarArrive := by
  cases r with
  | error => trivial
  | ok m => exact h

/-- An instruction other than `bar.arrive` fires no `bar.arrive` event. -/
theorem eventTmpl_notBarArrive {t : TState} {op : Op} (hop : op.isBarArrive = false) :
    (eventTmpl A L g t op).NotBarArrive := by
  cases op <;> simp only [Op.isBarArrive, Bool.true_eq_false] at hop
  all_goals simp only [eventTmpl]
  all_goals try (refine Flow.tcStTmpl_pres (fun _ => trivial) trivial ?_; intro)
  all_goals first
    | (apply widen_notBarArrive
       simp only [tmaTmpl]
       repeat' first
         | trivial
         | (apply ofExec_notBarArrive)
         | (apply PTX.EventFrame.allOk_bind; intro _)
         | (apply PTX.EventFrame.allOk_ite)
         | split
         | dsimp only)
    | (simp only [memTmpl, accessTmpl, atomTmpl, bulkInitTmpl, cpAsyncTmpl,
        asyncStoreTmpl, warpTmpl, acquireLoadTmpl, releaseStoreTmpl, loadTmpl, storeTmpl,
        barTmpl, SetMaxNReg.tmpl, fenceTmpl,
        warpBarTmpl, electTmpl, shflTmpl, voteTmpl, voteModeTmpl, reduxTmpl, matchTmpl,
        activemaskTmpl, tensorStoreTmpl,
        tensorPrefetchTmpl, clcTmpl, tcCommitTmpl, tcLdTmpl,
        tcTmpl, mmaTmpl, matrixTmpl, matrixMoveTmpl, tensorTmpl, tensorMulticast,
        localSregTmpl, sregTmpl]
       repeat' first
         | trivial
         | (apply thenWaitLd_notBarArrive)
         | (apply ofExec_notBarArrive)
         | (apply PTX.EventFrame.allOk_bind; intro _)
         | (apply PTX.EventFrame.allOk_ite)
         | (apply ite_notBarArrive)
         | split)
    | trivial

theorem out_notBarArrive (hK : K.NoBarArrive) {t : TState} {m : Tmpl}
    (h : out K A L g t = .ev m) : m.NotBarArrive := by
  unfold out at h
  split at h
  · cases h; trivial
  · split at h
    · cases h; trivial
    · rename_i ins hins
      split at h
      · cases h; trivial
      · cases h
      · split at h
        · split at h
          · cases h
          · cases h; trivial
        · cases h
          have := List.all_eq_true.mp hK ins (List.mem_of_getElem? hins)
          simp only [Bool.not_eq_true'] at this
          exact eventTmpl_notBarArrive this

theorem fires_notBarArrive {pc : Nat} {m : Tmpl} {e : Event} {o : Option TState}
    (hm : m.NotBarArrive) (h : Fires pc m e o) :
    ∀ id c, e.kind ≠ .bar id c .arrive := by
  intro id c hk
  obtain ⟨epc, ek⟩ := e
  simp only at hk
  subst hk
  cases m <;> simp only [Fires] at h <;> aesop

theorem run_notBarArrive (hK : K.NoBarArrive) {t : TState} {l : List Event} {o : Option TState}
    (h : Run K A L g t l o) : ∀ e ∈ l, ∀ id c, e.kind ≠ .bar id c .arrive := by
  induction h with
  | nil => simp
  | step _ he _ ih =>
    obtain ⟨m, hm, hf⟩ := he
    intro e' h'
    rcases List.mem_cons.mp h' with rfl | h'
    · exact fires_notBarArrive (out_notBarArrive hK hm) hf
    · exact ih e' h'
  | last _ he =>
    obtain ⟨m, hm, hf⟩ := he
    intro e' h'
    rcases List.mem_singleton.mp h' with rfl
    exact fires_notBarArrive (out_notBarArrive hK hm) hf

/-- A kernel without `bar.arrive` has no `bar.arrive` event in a possible execution. -/
theorem Consistent.noBarArrive {mem0 : Mem0} {X : Execution} (hK : K.NoBarArrive)
    (hX : Consistent L K A mem0 X) (v : EvId) (pc id : Nat) (c : Option Nat) :
    X.get v ≠ some ⟨pc, .bar id c .arrive⟩ := by
  intro hv
  have hlt : v.2 < (X.tr v.1).length := by
    unfold Execution.get at hv; exact (List.getElem?_eq_some_iff.mp hv).1
  have hg : v.1 < L.threads := by
    by_contra hn; rw [hX.outside v.1 (by omega)] at hlt; simp at hlt
  obtain ⟨o, hr⟩ := hX.thr v.1 hg
  have hmem : (⟨pc, .bar id c .arrive⟩ : Event) ∈ X.tr v.1 := by
    unfold Execution.get at hv; exact List.mem_of_getElem? hv
  exact run_notBarArrive hK hr _ hmem id c rfl

section
variable {mem0 : Mem0} {X : Execution} (hK : K.NoBarArrive) (hX : Consistent L K A mem0 X)
include hK hX

/-- Without `bar.arrive`, every barrier arrival is a `bar.sync` arrival. -/
theorem Consistent.isBarrier_of_arrival {e : EvId} {id pc : Nat} {c : Option Nat}
    (h : X.IsBarArrival e id c pc) : X.IsBarrier e id c pc := by
  obtain ⟨mode, h⟩ := h
  cases mode
  · exact h
  · exact (hX.noBarArrive hK e pc id c h).elim

theorem Consistent.ctaBarK_of_arrival {e : EvId} {key : Nat} (h : CtaBarArrivalK L X e key) :
    CtaBarK L X e key := by
  obtain ⟨h1, ⟨c, pc, h2⟩, h3⟩ := h
  exact ⟨h1, ⟨c, pc, hX.isBarrier_of_arrival hK h2⟩, h3⟩

theorem Consistent.noBarArrive_tr :
    ∀ g ev, ev ∈ X.tr g → ∀ id c, ev.kind ≠ .bar id c .arrive := by
  intro g ev hm id c hk
  obtain ⟨j, hj⟩ := List.getElem?_of_mem hm
  obtain ⟨pc, kd⟩ := ev
  simp only at hk
  subst hk
  exact hX.noBarArrive hK (g, j) _ _ _ hj

theorem Consistent.not_barArriveMismatch : ¬ BarArriveMismatch L X := by
  rintro ⟨g, h, i, j, id, id', count, count', mode', pc, pc', -, hg, -⟩
  exact hX.noBarArrive hK _ _ _ _ hg

end

end

end PTX
