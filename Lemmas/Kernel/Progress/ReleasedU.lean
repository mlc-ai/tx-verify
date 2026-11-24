-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Kernel.Progress.Released
public import Lemmas.Kernel.FrameU

@[expose] public section
namespace PTX.Descent
open PTX PTX.Flow MBarrier AsyncCopy
noncomputable section
variable {K : Kernel} {A : List Assumption} {L : Launch} {mem0 : Mem0} {X : Execution}
variable {ι : Sort _} {Obl : Execution → ι → Prop} {rank : Execution → ι → Nat} {o : ι}
variable {C : (g : Nat) → Flow.Code K A L g}

theorem next_classU (hc : NextEnv L K A mem0 X) (hC : ∀ g < L.threads, (C g).SoundU) {g : Nat}
    (hp : Frame.Pending L X g) {d : (C g).D}
    (hσ : Frame.stateAt C X g (X.tr g).length = some (some d)) (hne : X.tr g ≠ [])
    (hrel : Step.Released L X g) {k : NextKind}
    (hk : ∀ ins, K.code[(C g).pc d]? = some ins → opKind ins.op = k)
    (h : ∀ t t1 m, Run K A L g {} (X.tr g) (some t) →
      Relation.ReflTransGen (Tau K A L g) t t1 → out K A L g t1 = .ev m → KindTmpl k m →
      Steps L K A mem0 Obl rank X o) :
    Steps L K A mem0 Obl rank X o := by
  obtain ⟨t, hrun⟩ := Frame.run_some hc.max.1 hc.noUb hp
  rcases Frame.end_atU hC hp.1 hrun hσ with hsite | ⟨u, f, hl, hout⟩
  case inr => exact ub_steps_inOrder hc.wf hc.max.1 hp.1 hne hrel hrun hl hout
  obtain ⟨t1, ins, hl, -, -, hins, hout⟩ := hsite
  rcases tmpl_kind (A := A) (L := L) (g := g) (t := t1) ins.op with ⟨f, hf⟩ | hm
  · rw [hf] at hout
    exact ub_steps_inOrder hc.wf hc.max.1 hp.1 hne hrel hrun hl hout
  · rw [hk ins hins] at hm
    exact h t t1 _ hrun hl hout hm

variable (hc : NextEnv L K A mem0 X) {g : Nat} (hp : Frame.Pending L X g) (hne : X.tr g ≠ [])
    (hrel : Step.Released L X g)

include hc hp hne hrel

theorem released_stepsU (hC : ∀ g < L.threads, (C g).SoundU) {d : (C g).D}
    (hσ : Frame.stateAt C X g (X.tr g).length = some (some d))
    (hk : ∀ ins, K.code[(C g).pc d]? = some ins → (opKind ins.op).Rest = false)
    (hlast : ∀ ins, K.code[(C g).pc d]? = some ins → opKind ins.op = .store →
      ∀ pc grp dst n, X.get (g, (X.tr g).length - 1) =
        some ⟨pc, .tc (.resource grp dst (.alloc n))⟩ → laneOf L g ≠ 0) :
    Steps L K A mem0 Obl rank X o := by
  obtain ⟨t, hrun⟩ := Frame.run_some hc.max.1 hc.noUb hp
  rcases Frame.end_atU hC hp.1 hrun hσ with hsite | ⟨u, f, hl, hout⟩
  case inr => exact ub_steps_inOrder hc.wf hc.max.1 hp.1 hne hrel hrun hl hout
  obtain ⟨t1, ins, -, -, -, hins, -⟩ := hsite
  have hr := hk ins hins
  have hk' : ∀ ins', K.code[(C g).pc d]? = some ins' → opKind ins'.op = opKind ins.op := by
    intro ins' h'
    rw [hins] at h'
    cases h'
    rfl
  generalize hkd : opKind ins.op = k at hr hk'
  refine next_classU hc hC hp hσ hne hrel hk' fun t t1 m hrun hl hout hm => ?_
  cases k
  case wait | warp | reg | alloc | other => simp [NextKind.Rest] at hr
  case cluster => exact cluster_steps hc hp hne hrel hrun hl hout hm
  case bar => exact bar_steps' hc hp hne hrel hrun hl hout hm
  case tmem => exact tmem_steps hc hp hne hrel hrun hl hout hm
  case init => exact init_steps hc hp hne hrel hrun hl hout hm
  case arrive => exact arrive_steps hc hp hne hrel hrun hl hout hm
  case tensorLoad => exact tensorLoad_steps hc hp hne hrel hrun hl hout hm
  case tensorStore => exact tensorStore_steps hc hp hne hrel hrun hl hout hm
  case mma => exact mma_steps hc hp hne hrel hrun hl hout hm
  case commit => exact commit_steps hc hp hne hrel hrun hl hout hm
  case bulkWait => exact bulkWait_steps hc hp hne hrel hrun hl hout hm
  case tcLoad => exact tcLoad_steps hc hp hne hrel hrun hl hout hm
  case read => exact read_steps hc hp hne hrel hrun hl hout hm
  case quiet => exact quiet_steps' hc hp hne hrel hrun hl hout hm
  case store => exact store_steps hc hp hne hrel hrun hl hout hm (hlast ins hins hkd)
  case exit => exact exit_steps hc hp hne hrel hrun hl hout hm

end
end PTX.Descent
