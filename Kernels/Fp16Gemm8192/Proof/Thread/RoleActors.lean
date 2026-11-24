-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Thread.RoleRun
public import Kernels.Fp16Gemm8192.Proof.Thread.Elect
public import Lemmas.Flow.TcTmpl

@[expose] public section

/-! # The elected actor of a role

The loader, MMA and scheduler warps each elect one lane in a full-mask election
(`Prologue.Role.electPc`), and only that lane goes on to the role's task loop; the other lanes
go to the exit. Along a thread's run, a role state past its election and before its exit
(`Prologue.Role.engaged`) follows an election of its own lane; so every mbarrier event of
such a role follows that election. -/

namespace PTX.Kernels.Fp16Gemm8192.Proof

open PTX PTX.Proof PTX.Flow

noncomputable section

set_option maxRecDepth 100000

/-- Among the events `es`, a full-mask election at `pc` elected thread `g`'s lane. -/
def ElectedIn (L : Launch) (g pc : Nat) (es : List Event) : Prop :=
  ∃ (j inst leader : Nat), es[j]? = some (⟨pc, .elect 4294967295 inst leader⟩ : Event) ∧
    laneOf L g = leader

theorem ElectedIn.snoc {L : Launch} {g pc : Nat} {es : List Event} (e : Event)
    (h : ElectedIn L g pc es) : ElectedIn L g pc (es ++ [e]) := by
  obtain ⟨j, inst, leader, hj, hl⟩ := h
  exact ⟨j, inst, leader, by rw [List.getElem?_append_left
      (List.getElem?_eq_some_iff.mp hj).1]; exact hj, hl⟩

theorem ElectedIn.last {L : Launch} {g pc : Nat} {es : List Event} {inst leader : Nat}
    (hl : laneOf L g = leader) :
    ElectedIn L g pc (es ++ [(⟨pc, .elect 4294967295 inst leader⟩ : Event)]) :=
  ⟨es.length, inst, leader, by simp, hl⟩

/-- The scheduler's exit sites. -/
def Scheduler.Site.done : Scheduler.Site → Bool
  | .exitArrive | .exitWait | .exit => true
  | _ => false

/-- A role state past its election and before its exit. -/
def Prologue.Role.engaged : Prologue.Role → Bool
  | .loader l => !l.site.done
  | .mma m => decide (m.site ≠ .elect) && !m.site.done
  | .sched s => decide (s.site ≠ .elect) && !s.site.done
  | .cons _ => false

/-- The prologue enters the loader's loop only at the role election, on the elected lane. -/
theorem Prologue.next_loaderLoop {L : Launch} {g : Nat} {p : Prologue.D} {e : Event} {l : Loader.D}
    (hn : Prologue.next L g p e = some (some (.inr (.loader l)))) (hd : l.site.done = false) :
    p.site = .roleElect ∧ ∃ mk inst leader, e.kind = .elect mk inst leader ∧ laneOf L g = leader :=
      by
  obtain ⟨s, w⟩ := p
  obtain ⟨pc, k⟩ := e
  unfold Prologue.next at hn
  repeat' (first | split_ifs at hn | split at hn)
  all_goals (try simp only [Option.some.injEq, reduceCtorEq, Sum.inr.injEq,
    Prologue.Role.loader.injEq] at hn)
  all_goals (try subst hn)
  all_goals first
    | (simp [Prologue.loaderIdle, Loader.Site.done] at hd; done)
    | simp_all

/-- An engaged role state follows the election of its lane. -/
def ActorInv (L : Launch) (g : Nat) : ThreadD → List Event → Prop
  | .inr r, es => r.engaged = true → ∀ pc, r.electPc = some pc → ElectedIn L g pc es
  | _, _ => True

theorem Loader.done_next {L : Launch} {g : Nat} {l l' : Loader.D} {e : Event}
    (hd : l.site.done = true) (hn : Loader.next L g l e = some (some l')) : l'.site.done = true :=
      by
  obtain ⟨s, m, n, q, cp, r, x⟩ := l
  cases s <;> simp [Loader.Site.done] at hd <;> simp only [Loader.next] at hn <;>
    simp_all [Loader.Site.done] <;> (obtain rfl := hn; rfl)

/-- Off the election, a role step keeps an engaged state's election. -/
private theorem actor_keep {L : Launch} {g : Nat} {pre : List Event} {e : Event}
    {r r' : Prologue.Role} (hq : ActorInv L g (.inr r) pre) (hpc : r'.electPc = r.electPc)
    (hk : r'.engaged = true → r.engaged = true) : ActorInv L g (.inr r') (pre ++ [e]) :=
  fun he pc' hp => (hq (hk he) pc' (hpc ▸ hp)).snoc e

theorem actorInv {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} (hpre : Pre P L mem0)
    (hg : g < L.threads) {es : List Event}
    (htr : (code L g).toMachine.Trace (some (code L g).init) es) :
    ∀ j d, (code L g).toMachine.after (some (code L g).init) (es.take j) = some (some d) →
      ActorInv L g d (es.take j) := by
  refine Code.run_inv (sound hpre hg) htr (ActorInv L g) trivial ?_
  intro d d' pre e t ins o hq hat hinv hc hf hn
  rcases d with p | (l | m | sd | cs)
  · -- the prologue enters a role
    change Prologue.next L g p e = some (some d') at hn
    rcases d' with p' | (l' | m' | sd' | cs')
    · trivial
    · intro hd pc hpc
      simp only [Prologue.Role.engaged, Bool.not_eq_true'] at hd
      simp only [Prologue.Role.electPc, Option.some.injEq] at hpc
      subst hpc
      obtain ⟨hrole, -, -, -, -, -⟩ := Prologue.next_loaderLoop hn hd
      obtain ⟨s, w⟩ := p
      simp only at hrole
      subst hrole
      obtain rfl := Option.some.inj (hc.symm.trans Flow.code_elect_1)
      have hmask : readBits L g t 32 (.reg 649) = .ok (BitVec.ofNat 64 4294967295) :=
        readBits_b32 (Prologue.reg_val (at_of_atD (by simp) hat)
          (show 649 ∈ Flow.live Prologue.Site.roleElect.pc by table_decide) (by pro_values))
          (by decide)
      obtain ⟨-, mk, inst', leader', hk, hl⟩ := Prologue.next_loaderLoop hn hd
      rcases fires_elect_mask hmask hf with ⟨inst, leader, rfl⟩ | ⟨f, rfl⟩
      · simp only [Kind.elect.injEq] at hk
        obtain ⟨-, -, rfl⟩ := hk
        exact ElectedIn.last hl
      · cases hk
    · intro hd
      rcases Prologue.next_mma hn with h | h <;>
        simp [Prologue.Role.engaged, h, Mma.Site.done] at hd
    · intro hd
      rw [Prologue.next_sched hn] at hd
      simp [Prologue.Role.engaged, Prologue.schedStart] at hd
    · intro hd
      simp [Prologue.Role.engaged] at hd
  · -- the loader
    obtain ⟨l', hl, rfl⟩ := next_of_loader hn
    refine actor_keep hq rfl fun hd => ?_
    simp only [Prologue.Role.engaged, Bool.not_eq_true'] at hd ⊢
    cases hdl : l.site.done
    · rfl
    · rw [Loader.done_next hdl hl] at hd
      cases hd
  · -- the MMA warps
    obtain ⟨m', hm, rfl⟩ := next_of_mma hn
    by_cases he : m.site = .elect
    · intro hd pc hpc
      simp only [Prologue.Role.electPc, Option.some.injEq] at hpc
      subst hpc
      obtain ⟨s, w, q, fp, ap, cp, r, x⟩ := m
      simp only at he
      subst he
      obtain rfl := Option.some.inj (hc.symm.trans Flow.code_elect_3)
      have hmask : readBits L g t 32 (.reg 836) = .ok (BitVec.ofNat 64 4294967295) :=
        readBits_b32 (holds_mem hat.2.2.2.2 (Flow.mem_factsFrom
          (show 836 ∈ Flow.live Mma.Site.elect.pc by table_decide))) (by decide)
      rcases fires_elect_mask hmask hf with ⟨inst, leader, rfl⟩ | ⟨f, rfl⟩
      · simp only [Mma.next] at hm
        split_ifs at hm with hl
        · exact ElectedIn.last hl
        · obtain rfl := Option.some.inj (Option.some.inj hm)
          simp [Prologue.Role.engaged, Mma.Site.done] at hd
      · simp [Mma.next] at hm
    · refine actor_keep hq rfl fun hd => ?_
      simp only [Prologue.Role.engaged, Bool.and_eq_true, decide_eq_true_eq,
        Bool.not_eq_true'] at hd ⊢
      refine ⟨he, ?_⟩
      cases hdm : m.site.done
      · rfl
      · obtain ⟨s, w, q, fp, ap, cp, r, x⟩ := m
        cases s <;> simp [Mma.Site.done] at hdm <;> simp only [Mma.next] at hm <;>
          first | (obtain rfl := Option.some.inj (Option.some.inj hm); simp [Mma.Site.done] at hd) |
            cases hm
  · -- the scheduler
    obtain ⟨s', hs, rfl⟩ := next_of_sched hn
    by_cases he : sd.site = .elect
    · intro hd pc hpc
      simp only [Prologue.Role.electPc, Option.some.injEq] at hpc
      subst hpc
      obtain ⟨s, ap, cp, r, x⟩ := sd
      simp only at he
      subst he
      obtain rfl := Option.some.inj (hc.symm.trans Flow.code_elect_2)
      have hmask : readBits L g t 32 (.reg 630) = .ok (BitVec.ofNat 64 4294967295) :=
        readBits_b32 (holds_mem hat.2.2.2.2 (Flow.mem_factsFrom
          (show 630 ∈ Flow.live Scheduler.Site.elect.pc by table_decide))) (by decide)
      rcases fires_elect_mask hmask hf with ⟨inst, leader, rfl⟩ | ⟨f, rfl⟩
      · simp only [Scheduler.next] at hs
        split_ifs at hs with hl
        · exact ElectedIn.last hl
        · obtain rfl := Option.some.inj (Option.some.inj hs)
          simp [Prologue.Role.engaged, Scheduler.Site.done] at hd
      · simp [Scheduler.next] at hs
    · refine actor_keep hq rfl fun hd => ?_
      simp only [Prologue.Role.engaged, Bool.and_eq_true, decide_eq_true_eq,
        Bool.not_eq_true'] at hd ⊢
      refine ⟨he, ?_⟩
      cases hdm : sd.site.done
      · rfl
      · obtain ⟨s, ap, cp, r, x⟩ := sd
        cases s <;> simp [Scheduler.Site.done] at hdm <;> simp only [Scheduler.next] at hs <;>
          first | (obtain rfl := Option.some.inj (Option.some.inj hs);
                    simp [Scheduler.Site.done] at hd) | cases hs
  · obtain ⟨c', -, rfl⟩ := next_of_cons hn
    intro hd
    simp [Prologue.Role.engaged] at hd

/-- An mbarrier event of an elected role follows the election of its lane. -/
theorem role_elected {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X) {g : Nat} (hg : g < L.threads)
    {k : Nat} {e : Event} (he : X.get (g, k) = some e) {r : Prologue.Role}
    (hσ : (code L g).toMachine.after (some (code L g).init) ((X.tr g).take k) =
      some (some (.inr r)))
    {pc : Nat} (hpc : r.electPc = some pc) (hk : ObjectKind e.kind) :
    ∃ j inst leader, j < k ∧ X.get (g, j) = some ⟨pc, .elect 4294967295 inst leader⟩ ∧
      laneOf L g = leader := by
  have htr := Frame.trace (fun _ => sound hpre) hX hg
  obtain ⟨t, ins, o, -, -, hc, hfire⟩ := Frame.fired_site (fun _ => sound hpre) hX he hσ
  have hop : objectOp ins.op = true := by
    cases h : objectOp ins.op
    · exact absurd hk (notObject_of_op h hfire)
    · rfl
  have hen : r.engaged = true := by
    rcases r with ⟨s, _, _, _, _, _, _⟩ | ⟨s, _, _, _, _, _, _, _⟩ | ⟨s, _, _, _, _⟩ | c
    all_goals try simp [Prologue.Role.electPc] at hpc
    all_goals (cases s <;> first
      | rfl
      | (code_at hc; subst hc; simp [objectOp] at hop))
  obtain ⟨j, inst, leader, hj, hl⟩ := actorInv hpre hg htr k _ hσ hen pc hpc
  have hjk : j < k := by
    have := (List.getElem?_eq_some_iff.mp hj).1
    simp only [List.length_take] at this
    omega
  refine ⟨j, inst, leader, hjk, ?_, hl⟩
  change (X.tr g)[j]? = _
  rw [← List.getElem?_take_of_lt hjk]
  exact hj

end
end PTX.Kernels.Fp16Gemm8192.Proof
