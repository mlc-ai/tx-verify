-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof2.Common.Sound
public import Kernels.InklingRelDecode.Proof2.Ref.Tail
public import Kernels.InklingRelDecode.Proof2.Ref.Worker
public import Kernels.InklingRelDecode.Proof2.Startup.Shape
public import Lemmas.Flow.NotVote
public import Lemmas.Kernel.Followed
public import Lemmas.Kernel.Counted
public import Lemmas.Kernel.Source.WarpColl
public import Lemmas.Flow.AllocTmpl
public import Lemmas.Flow.NotBulk

@[expose] public section

/-! # The reference invariant of the default partition, and its following

**Reference invariant** (`Ref`). At a startup state the shuffle count (0) and, from the second
barrier on, the base word 0 (`StartRef`); at a prologue state the base word, a positive shuffle
count and the prologue's reference (`ProRef`, `ProA.PRef`: the inherited registers, the request
words, the gate of the preloaded blocks, the base word register); at a state of the
softmax–epilogue fragment the base word, a positive shuffle count and, at a softmax state, the
entry numbers' meaning (`TailRef`, `SmRef`); at a worker state the base word, a positive shuffle
count and the worker reference (`WRef`: a reached site, the carried base word 0). The stubs behind a
failed gate are not followed (`False`): no followed thread enters them.

**Sources.** The base word: the read of the shared base returns the allocated column 0 written by
the allocation (`BaseRead`, a premise: lane-L request L-h, the old tree's `BaseWordRead`). The
received warp index: the warp collective source (`Frame.shfl_src`): the source lane is lane 0 of
the warp at its startup shuffle, which sends its warp index (`start_recv`); no lane of the kernel
votes (`novote`). The prologue's loads and the softmax region's bias loads: the read-only input
source (`pro_expect`, `Ref/Input.lean`; `sm_expect`, `Ref/Tail.lean`).

**Following** (`good`): `Frame.followedOn` over the lanes of the launch with the order by the warp
collectives; the startup's steps (`start_step`), the prologue's (`pro_step`, from
`ProA.ref_next`), the softmax–epilogue fragment's (`tail_step`) and the worker fragment's
(`worker_step`). The thread machine has no stub
on a followed thread's path, so it is followed itself, to the thread's return. -/

namespace PTX.Kernels.InklingRelDecode.Proof2
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.InklingRelDecode

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- **The counts of a state are the thread's events of each class before it.** -/
theorem fcount {k : Nat} {σ : (thread Q L g).D}
    (h : Frame.stateAt (thread Q L) X g k = some (some σ)) (c : Cls) :
    σ.2 c = ((X.tr g).take k).countP (cls c) :=
  Frame.count_eq (C := fun g => Code.glue (Startup.code Q L g)
      (Code.withStubs (frag Q L g) Startup.Entry.pc) (Code.gatedExit Startup.enterOf (sel L g)))
    (cls := fun _ => cls) h c

/-! ### The reference invariant -/

/-- The lanes the reference follows: every launched thread (its warp is below 8). -/
def DpLane (L : Launch) (g : Nat) : Prop := g < L.threads ∧ g % L.block / 32 < 8

/-- **The base word's source** (proved in `Ref/BaseRead.lean` from the first stage of the
following): the startup's load of the shared base returns the allocated column 0. -/
def BaseRead (Q : Params) (L : Launch) (X : Execution) : Prop :=
  ∀ {g k pc : Nat} {s : Startup.D} {n : Cls → Nat} {a : Acc} {bs : List (Option Byte)},
    Frame.stateAt (thread Q L) X g k = some (some (.inl s, n)) → s.site = .ld0 →
    X.get (g, k) = some ⟨pc, .rd a bs⟩ → a.loc = ⟨.shared, g / L.block, L.sharedBase⟩ →
      a.size = 4 → bs = (b32 0).toBytes.map some

/-- The startup's reference: no shuffle yet, and the base word 0 once it is read. -/
def StartRef (s : Startup.D) (n : Cls → Nat) : Prop :=
  match s.site with
  | .enter _ => False
  | .alloc | .allocWr | .bar0 | .ld0 => n .shfl = 0
  | .bar1 | .relinq | .shfl => n .shfl = 0 ∧ s.tm = 0 ∧ s.w = b32 0

/-- The prologue's reference: the base word 0, the startup's shuffle counted, and the
prologue's own reference (`ProA.PRef`: the inherited registers of the launch, the request words,
the gate of the preloaded blocks). -/
def ProRef (Q : Params) (L : Launch) (g tm : Nat) (bw : Value) (d : ProA.D) (n : Cls → Nat) :
    Prop :=
  tm = 0 ∧ 1 ≤ n .shfl ∧ ProA.PRef Q L g tm bw d ∧ bw = b32 0

/-- The softmax–epilogue fragment's reference: the base word 0, the startup's shuffle counted,
and at a softmax state the entry numbers' meaning (`SmRef`). -/
def TailRef (Q : Params) (L : Launch) (g tm : Nat) : Tail.St → (Cls → Nat) → Prop
  | .sm d, n => tm = 0 ∧ 1 ≤ n .shfl ∧ SmRef Q L g d
  | .epi _, n => tm = 0 ∧ 1 ≤ n .shfl

/-- **The reference invariant of a thread of warps 0 to 3.** -/
def Ref (Q : Params) (L : Launch) (g : Nat) : (thread Q L g).D → Prop
  | (.inl s, n) => StartRef s n
  | (.inr ⟨.inl (.dp tm bw), .inl d⟩, n) => ProRef Q L g tm bw d n
  | (.inr ⟨.inl (.dp tm _), .inr ⟨.inl _, σ⟩⟩, n) => TailRef Q L g tm σ n
  | (.inr ⟨.inl (.dp _ _), .inr ⟨.inr _, _⟩⟩, _) => False
  | (.inr ⟨.inl (.worker tm), σ⟩, n) => tm = b32 0 ∧ 1 ≤ n .shfl ∧ WRef (b32 0) σ
  | (.inr ⟨.inr _, _⟩, _) => False

theorem enterOf_init : Startup.enterOf (Startup.init L g) = none := by
  unfold Startup.init; split <;> rfl

theorem ref_init : Ref Q L g (thread Q L g).init := by
  show Ref Q L g (Code.enter (Startup.code Q L g) (Code.withStubs (frag Q L g) Startup.Entry.pc)
    (Code.gatedExit Startup.enterOf (sel L g)) (Startup.init L g), fun _ => 0)
  rw [Code.enter_none (by simp [Code.gatedExit, enterOf_init])]
  unfold Startup.init
  split <;> rfl

/-! ### Events at startup states -/

/-- **An event at a startup state of the thread machine has the startup's shape**, unless it is
undefined behaviour. -/
theorem start_ev (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X) {k : Nat}
    {e : Event} {s : Startup.D} {n : Cls → Nat} (he : X.get (g, k) = some e)
    (hσ : Frame.stateAt (thread Q L) X g k = some (some (.inl s, n)))
    (hu : ∀ f, e.kind ≠ .ub f) : Startup.Ev L g s e := by
  have hg := Frame.lt_of_get hX he
  obtain ⟨o, hf0⟩ := (Frame.trace (fun g hg => thread_sound hp hg) hX hg).fired_at he hσ
  obtain ⟨t, ⟨hat, hi, hx⟩, hf⟩ := hf0
  obtain ⟨ins, hc, -, -⟩ := (startup_steps hp s (Code.gatedExit_none.mp hx)).site hi
  change Fires t.pc (match kernel.code[(Startup.code Q L g).pc s]? with
    | some ins => eventTmpl Assumptions.all L g t ins.op | none => .ub .pcOutOfRange) e o at hf
  rw [hc, hat.1] at hf
  exact Startup.shape hp hat hi hc hf hu

/-- The startup's events are no exit, and the only shuffle is the shuffle site's. -/
theorem start_kind {s : Startup.D} {n : Cls → Nat} {e : Event} (hS : StartRef s n)
    (hE : Startup.Ev L g s e) :
    e.kind ≠ .exit ∧ (Execution.isShfl e = true →
      ∃ recv ok, e = ⟨17, .shfl .idx (b32 (g % L.block / 32)) 0 31 recv ok⟩) := by
  obtain ⟨site, tm, x, bw⟩ := s
  cases site <;> simp only [StartRef] at hS <;> simp only [Startup.Ev] at hE
  · subst hE; exact ⟨by simp, by simp [Execution.isShfl]⟩
  · obtain ⟨col, -, rfl⟩ := hE; exact ⟨by simp, by simp [Execution.isShfl]⟩
  · subst hE; exact ⟨by simp, by simp [Execution.isShfl]⟩
  · obtain ⟨ac, bs, rfl, -⟩ := hE; exact ⟨by simp, by simp [Execution.isShfl]⟩
  · subst hE; exact ⟨by simp, by simp [Execution.isShfl]⟩
  · subst hE; exact ⟨by simp, by simp [Execution.isShfl]⟩
  · obtain ⟨recv, ok, rfl⟩ := hE; exact ⟨by simp, fun _ => ⟨recv, ok, rfl⟩⟩

/-- **A followed position whose thread has made no shuffle is a startup state** of the thread
machine, with its reference and its event's shape (for an event that is no undefined
behaviour). -/
theorem start_at (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X) {h j : Nat}
    {e : Event} (he : X.get (h, j) = some e) (hu : ∀ f, e.kind ≠ .ub f)
    (hG : Frame.FollowedAt (thread Q L) (fun g => Ref Q L g) X h j)
    (hc : ((X.tr h).take j).countP Execution.isShfl = 0) :
    ∃ s n, Frame.stateAt (thread Q L) X h j = some (some (.inl s, n)) ∧ StartRef s n ∧
      Startup.Ev L h s e := by
  have hh := Frame.lt_of_get hX he
  cases hσ : Frame.stateAt (thread Q L) X h j with
  | none =>
    rcases Frame.fired (fun g hg => thread_sound hp hg) hX he with ⟨σ, o, hσ', -⟩ | ⟨-, pc, f, hf⟩
    · rw [hσ] at hσ'; cases hσ'
    · exact absurd (by rw [hf]) (hu f)
  | some o =>
    cases o with
    | none => exact absurd hσ hG.1
    | some σ =>
      have hR := hG.2 σ hσ
      have hn := fcount hσ .shfl
      simp only [cls] at hn
      rw [hc] at hn
      obtain ⟨x, n⟩ := σ
      rcases x with s | ⟨_ | r, d⟩
      · exact ⟨s, n, rfl, hR, start_ev hp hX he hσ hu⟩
      · rename_i i
        cases i with
        | dp tm bw =>
          rcases d with d | ⟨_ | _, τ⟩
          · exact absurd hR.2.1 (by simp only at hn; omega)
          · cases τ with
            | sm d => exact absurd hR.2.1 (by simp only at hn; omega)
            | epi d => exact absurd hR.2 (by simp only at hn; omega)
          · exact hR.elim
        | worker tm => exact absurd hR.2.1 (by simp only at hn; omega)
      · exact hR.elim

/-- No event of the kernel is a vote (it has no `vote.sync`). -/
theorem novote (hX : Consistent L kernel Assumptions.all m X) {i : EvId} {e : Event}
    (he : X.get i = some e) {mk : Nat} : voteWith mk e = false := by
  have h := no_kind_of_code hX Op.isVote (fun k => voteWith mk ⟨0, k⟩ = true)
    (fun f => by simp [voteWith, voteClass])
    (fun hf hb => fires_vote_op hf (by obtain ⟨pc, k⟩ := ‹Event›; simpa [voteWith] using hb))
    (by decide +kernel) he
  obtain ⟨pc, k⟩ := e
  simpa [voteWith] using h

/-! ### The startup's shuffle returns the warp index -/

/-- **What the startup's shuffle receives**: lane 0's warp index, which is the thread's. -/
theorem start_recv (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hg : DpLane L g) {k : Nat} {recv : Value} {ok : Bool}
    (he : X.get (g, k) = some ⟨17, .shfl .idx (b32 (g % L.block / 32)) 0 31 recv ok⟩)
    (hc : ((X.tr g).take k).countP Execution.isShfl = 0)
    (hprev : ∀ j, Frame.lexOrder (Frame.collUpTo X) j (g, k) → DpLane L j.1 →
      ¬ Frame.Bad (thread Q L) (fun g => Ref Q L g) X j) :
    recv = b32 (g % L.block / 32) := by
  have hb : L.block % 32 = 0 := by rw [hp.block]
  have hcv : ((X.tr g).take k).countP (voteWith (2 ^ 32 - 1)) = 0 :=
    List.countP_eq_zero.mpr fun e he' => by
      obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp (List.mem_of_mem_take he')
      simp [novote hX (i := (g, i)) hi]
  have IH : Frame.GoodUpTo (thread Q L) (fun g => Ref Q L g) X (g % L.block / 32) (0 + 0) := by
    have := Frame.upTo_of_prev (C := thread Q L) (J := fun g => Ref Q L g)
      (w := g % L.block / 32) (fun g => ref_init) he (by simp [Frame.isColl, Execution.isShfl])
      (fun j hj hw' => hprev j hj ⟨hw'.1, by rw [hw'.2]; exact hg.2⟩)
    rwa [Frame.countColl, hc, hcv] at this
  obtain ⟨j, pc', b', c', r', o', hget, hG, hcs, -⟩ := Frame.shfl_src (C := thread Q L)
    (J := fun g => Ref Q L g) hb hX hg.1 rfl he hc IH
    (fun _ _ _ _ _ he' hv _ _ _ => by rw [novote hX he'] at hv; cases hv)
    (fun _ _ _ _ _ he' hG' hs _ => by
      obtain ⟨s, n, -, hS, hE⟩ :=
        start_at hp hX he' (by simp) hG' (by unfold Frame.cnt at hs; omega)
      exact (start_kind hS hE).1 rfl)
  have hsl := Step.shflSource_lt ShflMode.idx
    (show laneOf L g < 32 from Nat.mod_lt _ (by decide)) 0 31
  obtain ⟨-, hsW, -, -, -⟩ := Frame.lane_facts hb hg.1 rfl hsl
  obtain ⟨s, n, -, hS, hE⟩ := start_at hp hX hget (by simp) hG hcs
  obtain ⟨recv', ok', heq⟩ := (start_kind hS hE).2 (by simp [Execution.isShfl])
  simp only [Event.mk.injEq, Kind.shfl.injEq] at heq
  rw [heq.2.2.1, hsW]

/-! ### The startup's steps -/

theorem bump_shfl {n : Cls → Nat} {e : Event} (h : Execution.isShfl e = false) :
    Code.bump cls n e .shfl = n .shfl := by
  simp [Code.bump, cls, h]

/-- A startup step into a state that is no exit, with its reference. -/
theorem step_to {s s' : Startup.D} {n : Cls → Nat} {e : Event}
    (h : Startup.succ L g s e = some (some s')) (hx : Startup.enterOf s' = none)
    (hR : StartRef s' (Code.bump cls n e)) :
    Frame.StepGood (thread Q L) (fun g => Ref Q L g) g (.inl s, n) e := by
  have hn : (thread Q L g).next (.inl s, n) e = some (some (.inl s', Code.bump cls n e)) := by
    simp only [thread,
      Code.roleThread, Code.counted, Code.glue, Startup.code, h, Option.map_some]
    simp [Code.enter, Code.gatedExit, hx]
  refine ⟨by rw [hn]; simp, fun σ' h' => ?_⟩
  rw [hn] at h'
  cases h'
  exact hR

/-- **The startup steps a lane of warps 0 to 3 well**: into the prologue's first state after the
shuffle, whose received word is the warp index (`start_recv`). -/
theorem start_step (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hB : BaseRead Q L X) (hg : DpLane L g) {k : Nat} {s : Startup.D} {n : Cls → Nat} {e : Event}
    (he : X.get (g, k) = some e)
    (hσ : Frame.stateAt (thread Q L) X g k = some (some (.inl s, n))) (hR : StartRef s n)
    (hprev : ∀ j, Frame.lexOrder (Frame.collUpTo X) j (g, k) → DpLane L j.1 →
      ¬ Frame.Bad (thread Q L) (fun g => Ref Q L g) X j) :
    Frame.StepGood (thread Q L) (fun g => Ref Q L g) g (.inl s, n) e := by
  have hreal := hσ
  have hev : (∀ f, e.kind ≠ .ub f) → Startup.Ev L g s e := start_ev hp hX he hreal
  have hns : s.site ≠ .shfl → Execution.isShfl e = false := by
    intro hs
    by_cases hu : ∀ f, e.kind ≠ .ub f
    · cases hsh : Execution.isShfl e with
      | false => rfl
      | true =>
        obtain ⟨recv, ok, rfl⟩ := (start_kind hR (hev hu)).2 hsh
        obtain ⟨site, tm, x, bw⟩ := s
        cases site <;> simp only [Startup.Ev] at hev <;> first
          | exact absurd rfl hs
          | exact hR.elim
          | (have := hev hu; simp_all)
    · simp only [not_forall, not_not] at hu
      obtain ⟨f, hf⟩ := hu
      obtain ⟨pc, kind⟩ := e
      simp only at hf
      subst hf
      rfl
  obtain ⟨site, tm, x, bw⟩ := s
  cases site with
  | enter r => exact hR.elim
  | alloc =>
    have h0 : n .shfl = 0 := hR
    by_cases hl : laneOf L g = 0
    · exact step_to (s' := ⟨.allocWr, tm, x, bw⟩) (by simp [Startup.succ, hl]) rfl
        (show _ = 0 by rw [bump_shfl (hns nofun), h0])
    · exact step_to (s' := ⟨.bar0, tm, x, bw⟩) (by simp [Startup.succ, hl]) rfl
        (show _ = 0 by rw [bump_shfl (hns nofun), h0])
  | allocWr =>
    exact step_to (s' := ⟨.bar0, tm, x, bw⟩) (by simp [Startup.succ]) rfl
      (show _ = 0 by rw [bump_shfl (hns nofun)]; exact hR)
  | bar0 =>
    exact step_to (s' := ⟨.ld0, tm, x, bw⟩) (by simp [Startup.succ]) rfl
      (show _ = 0 by rw [bump_shfl (hns nofun)]; exact hR)
  | bar1 =>
    obtain ⟨h0, ht⟩ := hR
    by_cases hl : g % L.block < 32
    · exact step_to (s' := ⟨.relinq, tm, x, bw⟩) (by simp [Startup.succ, hl]) rfl
        ⟨by rw [bump_shfl (hns nofun), h0], ht⟩
    · exact step_to (s' := ⟨.shfl, tm, x, bw⟩) (by simp [Startup.succ, hl]) rfl
        ⟨by rw [bump_shfl (hns nofun), h0], ht⟩
  | relinq =>
    obtain ⟨h0, ht⟩ := hR
    exact step_to (s' := ⟨.shfl, tm, x, bw⟩) (by simp [Startup.succ]) rfl
      ⟨by rw [bump_shfl (hns nofun), h0], ht⟩
  | ld0 =>
    have h0 : n .shfl = 0 := hR
    by_cases hu : ∀ f, e.kind ≠ .ub f
    · obtain ⟨ac, bs, rfl, hl, hsz, -⟩ := hev hu
      have hbs := hB hσ rfl he hl hsz
      subst hbs
      have hw : Proof.ProA.word32 (b32 0) = some 0 := by simp [Proof.ProA.word32, b32]
      exact step_to (s' := ⟨.bar1, 0, x, b32 0⟩) (by simp [Startup.succ, rebuild_b32, hw]) rfl
        ⟨by rw [bump_shfl (by simp [Execution.isShfl]), h0], rfl, rfl⟩
    · simp only [not_forall, not_not] at hu
      obtain ⟨f, hf⟩ := hu
      obtain ⟨pc, kind⟩ := e
      simp only at hf
      subst hf
      refine ⟨?_, fun σ' h' => ?_⟩ <;>
        simp [thread, Code.roleThread, Code.counted, Code.glue, Startup.code, Startup.succ] at *
  | shfl =>
    obtain ⟨h0, ht⟩ := hR
    by_cases hu : ∀ f, e.kind ≠ .ub f
    · obtain ⟨recv, ok, rfl⟩ := hev hu
      have hcnt : ((X.tr g).take k).countP Execution.isShfl = 0 := by
        have := fcount hσ .shfl
        simp only [cls] at this
        omega
      have hrv := start_recv hp hX hg he hcnt hprev
      subst hrv
      by_cases h4 : g % L.block / 32 < 4
      · have hw4 : Arith32.scmpi .lt .u (BitVec.ofNat 64 (g % L.block / 32)) 4 = true := by
          generalize g % L.block / 32 = w at h4 ⊢
          interval_cases w <;> decide
        have hgate : Gate L g ⟨.enter .dp, tm, BitVec.ofNat 64 (g % L.block / 32), bw⟩ = true := by
          simp only [Gate, beq_self_eq_true, Bool.true_and, decide_eq_true_eq]
          omega
        have hn : (thread Q L g).next (.inl ⟨.shfl, tm, x, bw⟩, n)
            ⟨17, .shfl .idx (b32 (g % L.block / 32)) 0 31 (b32 (g % L.block / 32)) ok⟩ =
            some (some (.inr ⟨.inl (.dp tm bw), (frag Q L g (.dp tm bw)).init⟩,
              Code.bump cls n ⟨17, .shfl .idx (b32 (g % L.block / 32)) 0 31
                (b32 (g % L.block / 32)) ok⟩)) := by
          simp only [thread,
            Code.roleThread, Code.counted, Code.glue, Startup.code]
          simp [Startup.succ, b32, Startup.entryOf, hw4, Code.enter, Code.gatedExit,
            Startup.enterOf, sel, hgate]
        refine ⟨by rw [hn]; simp, fun σ' h' => ?_⟩
        rw [hn] at h'
        cases h'
        simp only at ht
        obtain ⟨rfl, rfl⟩ := ht
        exact ⟨rfl, by simp [Code.bump, cls, Execution.isShfl], ProA.pref_init _ rfl, rfl⟩
      · have hw4 : Arith32.scmpi .lt .u (BitVec.ofNat 64 (g % L.block / 32)) 4 = false := by
          have h8 := hg.2
          generalize g % L.block / 32 = w at h4 h8 ⊢
          interval_cases w <;> first | omega | decide
        have hgate : WGate L g ⟨.enter .worker, tm, BitVec.ofNat 64 (g % L.block / 32), bw⟩ =
            true := by
          simp only [WGate, beq_self_eq_true, Bool.true_and, decide_eq_true_eq]
          omega
        have hn : (thread Q L g).next (.inl ⟨.shfl, tm, x, bw⟩, n)
            ⟨17, .shfl .idx (b32 (g % L.block / 32)) 0 31 (b32 (g % L.block / 32)) ok⟩ =
            some (some (.inr ⟨.inl (.worker bw), (frag Q L g (.worker bw)).init⟩,
              Code.bump cls n ⟨17, .shfl .idx (b32 (g % L.block / 32)) 0 31
                (b32 (g % L.block / 32)) ok⟩)) := by
          simp only [thread,
            Code.roleThread, Code.counted, Code.glue, Startup.code]
          simp [Startup.succ, b32, Startup.entryOf, hw4, Code.enter, Code.gatedExit,
            Startup.enterOf, sel, hgate]
        refine ⟨by rw [hn]; simp, fun σ' h' => ?_⟩
        rw [hn] at h'
        cases h'
        show bw = b32 0 ∧ 1 ≤ Code.bump cls n _ .shfl ∧
          WRef (b32 0) (.worker ⟨.loop, Worker.workerPro Q L g bw⟩)
        simp only at ht
        obtain ⟨-, rfl⟩ := ht
        exact ⟨rfl, by simp [Code.bump, cls, Execution.isShfl], ⟨Or.inl rfl,
          by simp [Worker.workerPro]⟩, rfl⟩
    · simp only [not_forall, not_not] at hu
      obtain ⟨f, hf⟩ := hu
      obtain ⟨pc, kind⟩ := e
      simp only at hf
      subst hf
      refine ⟨?_, fun σ' h' => ?_⟩ <;>
        simp [thread, Code.roleThread, Code.counted, Code.glue, Startup.code, Startup.succ] at *

/-! ### The prologue's steps -/

/-- The thread machine at a prologue state is the prologue's successor, entering the
softmax–epilogue fragment (or the stub) at the prologue's exit. -/
theorem next_pro (tm : Nat) (bw : Value) (d : ProA.D) (n : Cls → Nat) (e : Event) :
    (thread Q L g).next (.inr ⟨.inl (.dp tm bw), .inl d⟩, n) e =
      (ProA.next L g d e).map (Option.map fun d' =>
        (.inr ⟨.inl (.dp tm bw), Code.enter (ProA.code L g (Startup.inh L g Q tm) bw)
          (Code.withStubs (fun dt => Tail.code L g (tailInit Q L g dt)) (fun _ : Unit => 574))
          (Code.gatedExit ProA.exitOf (ProA.selTail Q L g)) d'⟩, Code.bump cls n e)) := by
  rcases h : ProA.next L g d e with _ | _ | d' <;>
    simp [thread, Code.roleThread, Code.counted, Code.glue, Code.withStubs, frag, dpCode, h]

/-- At the prologue's exit under its reference, the gate of the softmax region holds. -/
theorem tailGate_of (hR : ProA.PRef Q L g 0 (b32 0) d) (hx : d.site = .exit) :
    TailGate Q L g d.dt := by
  obtain ⟨hpro, ⟨w0, w1, w2⟩, -, hw⟩ := hR
  obtain ⟨site, dt⟩ := d
  simp only at hx
  subst hx
  have hk : (ProA.Site.exit).old.afterSk = true := by decide
  exact ⟨hpro, ⟨w0 (by simp [ProA.D.old, ProA.Site.old]) (by simp [ProA.D.old, ProA.Site.old]),
    w1 (.inl hk), w2 hk⟩, hw⟩

/-- **The prologue steps a lane of warps 0 to 3 well**: its loads read the launch
(`pro_expect`), so by `ProA.ref_next` the machine does not stop and its successor holds the
reference; at the prologue's exit the gate holds and the thread enters the softmax region's first
state, whose entry numbers mean what `EntMeans` says (`Sm.entOf_means`). -/
theorem pro_step (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    {k tm : Nat} {bw : Value} {d : ProA.D} {n : Cls → Nat} {e : Event}
    (he : X.get (g, k) = some e)
    (hσ : Frame.stateAt (thread Q L) X g k = some (some (.inr ⟨.inl (.dp tm bw), .inl d⟩, n)))
    (hR : ProRef Q L g tm bw d n) :
    Frame.StepGood (thread Q L) (fun g => Ref Q L g) g (.inr ⟨.inl (.dp tm bw), .inl d⟩, n) e := by
  obtain ⟨htm, hn1, hP, hbw⟩ := hR
  have hg := Frame.lt_of_get hX he
  obtain ⟨t, ins, o, -, ⟨hi, hx⟩, -, -⟩ :=
    Frame.fired_site (fun g hg => thread_sound hp hg) hX he hσ
  have hx' : d.site ≠ .exit := fun h => by simp [Code.gatedExit, ProA.exitOf, h] at hx
  obtain ⟨hns, hsucc⟩ := ProA.ref_next hp hg hP (pro_expect hp hX he hσ hP) hx'
  have hb : 1 ≤ Code.bump cls n e .shfl := by simp only [Code.bump]; omega
  unfold Frame.StepGood
  rw [next_pro]
  rcases h : ProA.next L g d e with _ | _ | d'
  · simp
  · exact absurd h hns
  · refine ⟨by simp, fun σ' h' => ?_⟩
    simp only [Option.map_some, Option.some.injEq] at h'
    subst h'
    have hP' := hsucc d' h
    cases hxo : ProA.exitOf d' with
    | none =>
      rw [Code.enter_none (by simp [Code.gatedExit, hxo])]
      exact ⟨htm, hb, hP', hbw⟩
    | some u =>
      have hxs : d'.site = .exit := by
        obtain ⟨site, dt⟩ := d'
        cases site <;> simp_all [ProA.exitOf]
      subst htm hbw
      have hG := tailGate_of hP' hxs
      have hsel : ProA.selTail Q L g u d' = some d'.dt := by simp [ProA.selTail, hG]
      rw [Code.enter_some (i := Sum.inl d'.dt) (by simp [Code.gatedExit, hxo, hsel])]
      show TailRef Q L g 0 (.sm (tailInit Q L g d'.dt)) (Code.bump cls n e)
      have hargs : Proof.ProA.ArgsOk L g d'.dt.pro := by
        rw [hG.1, ← hP.pro]
        exact hi.args
      exact ⟨rfl, hb, Proof.Sm.entOf_means hp hargs⟩

/-! ### The softmax–epilogue fragment's steps -/

/-- The thread machine at a fragment state is the fragment's successor. -/
theorem next_tail (tm : Nat) (bw : Value) (dt : Proof.ProA.Dat) (σ : Tail.St) (n : Cls → Nat)
    (e : Event) :
    (thread Q L g).next (.inr ⟨.inl (.dp tm bw), .inr ⟨.inl dt, σ⟩⟩, n) e =
      (Tail.next L g σ e).map (Option.map fun σ' =>
        (.inr ⟨.inl (.dp tm bw), .inr ⟨.inl dt, σ'⟩⟩, Code.bump cls n e)) := by
  rcases h : Tail.next L g σ e with _ | _ | σ' <;>
    simp [thread, Code.roleThread, Code.counted, Code.glue, Code.withStubs, frag, dpCode, h]

/-- **The softmax–epilogue fragment steps a lane of warps 0 to 3 well**: its bias loads read the
launch (`sm_expect`) and the epilogue's load returns 64 values (`epi_expect`), so it does not
stop; every successor keeps the entry numbers or enters the epilogue. -/
theorem tail_step (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X) {k tm : Nat}
    {bw : Value}
    {dt : Proof.ProA.Dat} {σ : Tail.St} {n : Cls → Nat} {e : Event} (he : X.get (g, k) = some e)
    (hσ : Frame.stateAt (thread Q L) X g k =
      some (some (.inr ⟨.inl (.dp tm bw), .inr ⟨.inl dt, σ⟩⟩, n)))
    (hR : TailRef Q L g tm σ n) :
    Frame.StepGood (thread Q L) (fun g => Ref Q L g) g
      (.inr ⟨.inl (.dp tm bw), .inr ⟨.inl dt, σ⟩⟩, n) e := by
  have hg := Frame.lt_of_get hX he
  obtain ⟨t, ins, o, hat, hi, hc, hf⟩ :=
    Frame.fired_site (fun g hg => thread_sound hp hg) hX he hσ
  unfold Frame.StepGood
  rw [next_tail]
  cases σ with
  | sm d =>
    obtain ⟨htm, hn1, hS⟩ := hR
    have hb : 1 ≤ Code.bump cls n e .shfl := by simp only [Code.bump]; omega
    have hE := sm_expect hp hX hg he hat hi hc hf hS
    have hne := sm_next_ne (L := L) (g := g) hE
    rcases h : Tail.next L g (.sm d) e with _ | _ | σ'
    · simp
    · exact absurd h hne
    · refine ⟨by simp, fun σ'' h' => ?_⟩
      simp only [Option.map_some, Option.some.injEq] at h'
      subst h'
      simp only [Tail.next] at h
      split at h
      · unfold Tail.exitNext at h
        split at h
        · simp only [Option.some.injEq] at h
          subst h
          exact ⟨htm, hb⟩
        · cases h
      · cases hs : Proof.Sm.next L g d e with
        | none => rw [hs] at h; cases h
        | some o =>
          cases o with
          | none => rw [hs] at h; cases h
          | some d' =>
            rw [hs] at h
            simp only [Option.map_some, Option.some.injEq] at h
            subst h
            refine ⟨htm, hb, ?_⟩
            show Proof.Sm.EntMeans _ _ _ _ d'.e
            rw [sm_next_e hs]
            exact hS
  | epi d =>
    obtain ⟨htm, hn1⟩ := hR
    have hb : 1 ≤ Code.bump cls n e .shfl := by simp only [Code.bump]; omega
    have hne := epi_next_ne (L := L) (g := g) (epi_expect hat hi.1 hc hf)
    rcases h : Tail.next L g (.epi d) e with _ | _ | σ'
    · simp
    · exact absurd h hne
    · refine ⟨by simp, fun σ'' h' => ?_⟩
      simp only [Option.map_some, Option.some.injEq] at h'
      subst h'
      simp only [Tail.next] at h
      cases hs : Proof.Epi.next d e with
      | none => rw [hs] at h; cases h
      | some o =>
        cases o with
        | none => rw [hs] at h; cases h
        | some d' =>
          rw [hs] at h
          simp only [Option.map_some, Option.some.injEq] at h
          subst h
          exact ⟨htm, hb⟩

/-! ### The worker fragment's steps -/

/-- The thread machine at a worker state is the worker machine's successor. -/
theorem next_worker (tm : Value) (σ : Proof.WComp.WSt) (n : Cls → Nat) (e : Event) :
    (thread Q L g).next (.inr ⟨.inl (.worker tm), σ⟩, n) e =
      (Proof.WComp.next L g σ e).map (Option.map fun σ' =>
        (.inr ⟨.inl (.worker tm), σ'⟩, Code.bump cls n e)) := by
  rcases h : Proof.WComp.next L g σ e with _ | _ | σ' <;>
    simp [thread, Code.roleThread, Code.counted, Code.glue, Code.withStubs, frag, Worker.code, h]

/-- **The worker fragment steps a worker lane well**: it does not stop and keeps its reference
(`wnext_ne`, `wnext_ref`); no source is used. -/
theorem worker_step {tm : Value} {σ : Proof.WComp.WSt} {n : Cls → Nat} {e : Event}
    (hR : tm = b32 0 ∧ 1 ≤ n .shfl ∧ WRef (b32 0) σ) :
    Frame.StepGood (thread Q L) (fun g => Ref Q L g) g (.inr ⟨.inl (.worker tm), σ⟩, n) e := by
  obtain ⟨htm, hn1, hW⟩ := hR
  have hb : 1 ≤ Code.bump cls n e .shfl := by simp only [Code.bump]; omega
  unfold Frame.StepGood
  rw [next_worker]
  have hne := wnext_ne (L := L) (g := g) (e := e) hW
  rcases h : Proof.WComp.next L g σ e with _ | _ | σ'
  · simp
  · exact absurd h hne
  · refine ⟨by simp, fun σ'' h' => ?_⟩
    simp only [Option.map_some, Option.some.injEq] at h'
    subst h'
    exact ⟨htm, hb, wnext_ref hW h⟩

/-! ### Following -/

/-- **Every lane of warps 0 to 3 is followed, at states that hold the reference invariant**, from
its first event to its return. -/
theorem good (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X) (hB : BaseRead Q L X)
    (hg : DpLane L g) (k : Nat) :
    Frame.FollowedAt (thread Q L) (fun g => Ref Q L g) X g k :=
  Frame.followedOn (Q := DpLane L) (Frame.inductive_lex (Frame.collUpTo X))
    (fun _ _ => ref_init)
    (fun g k σ e hg he hσ hR hprev => by
      obtain ⟨x, n⟩ := σ
      rcases x with s | ⟨_ | r, d⟩
      · exact start_step hp hX hB hg he hσ hR hprev
      · rename_i i
        cases i with
        | dp tm bw =>
          rcases d with d | ⟨_ | _, τ⟩
          · exact pro_step hp hX he hσ hR
          · exact tail_step hp hX he hσ hR
          · exact hR.elim
        | worker tm => exact worker_step hR
      · exact hR.elim) hg k

/-- **Every launched thread is followed**, at states that hold the reference invariant. -/
theorem good_all (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hB : BaseRead Q L X) (hg : g < L.threads) (k : Nat) :
    Frame.FollowedAt (thread Q L) (fun g => Ref Q L g) X g k := by
  have hb := hp.block
  refine good hp hX hB ⟨hg, ?_⟩ k
  rw [hb]
  have := Nat.mod_lt g (show 0 < 256 by decide)
  omega

end
end PTX.Kernels.InklingRelDecode.Proof2
