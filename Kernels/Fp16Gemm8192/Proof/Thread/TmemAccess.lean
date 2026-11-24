-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Thread.ExitTasks
public import Kernels.Fp16Gemm8192.Proof.Thread.InputIssues
public import Kernels.Fp16Gemm8192.Proof.Thread.ConsumerLoadWords
public import Kernels.Fp16Gemm8192.Proof.Thread.BaseAccess
public import Kernels.Fp16Gemm8192.Proof.Thread.TmemStep
public import Kernels.Fp16Gemm8192.Proof.Thread.TcColl

@[expose] public section

/-! # The thread facts of the Tensor Memory accesses

Four facts behind the accesses' allocation and completion. CTA thread 0 allocates at its event 20,
before its first cluster arrival, so the allocation happens before every role event of its cluster
(`alloc_before_fact`, as `base_write_fact`). A deallocation is made past the thread's exit wait
(`dealloc_waited_fact`: the cluster invariant `ClInv`). A Tensor Memory data event is a consumer's
in its task loop, and a load returns sixteen words (`data_loop_fact`). An MMA's accumulator commits
before it are fewer than the thread's successful response polls, and its reads after the earlier
polls claim a CTA (`mma_tile_fact`: `Mma.Counts`, with `mma_reads_claim`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof

open PTX PTX.Proof PTX.Flow

noncomputable section

set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **The allocation before the roles.** Thread 0 of a CTA of a role event's cluster allocates at
its event 20, has events past it, and the allocation happens before the role event. -/
theorem alloc_before_fact (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    {h j T : Nat} {ev : Event} {r : Prologue.Role} (he : X.get (h, j) = some ev)
    (hr : Frame.stateAt (code L) X h j = some (some (.inr r))) (hT : T < L.grid)
    (hcl : L.clusterOfCta T = L.clusterOfCta (h / L.block)) :
    (∃ pc grp dst n, X.get (T * L.block, 20) =
      some ⟨pc, .tc (.resource grp dst (.alloc n))⟩) ∧
    21 < (X.tr (T * L.block)).length ∧ baseCausality L X (T * L.block, 20) (h, j) := by
  have hblock : 0 < L.block := by rw [hpre.block]; norm_num
  have hg0 : T * L.block < L.threads := by
    change _ < L.grid * L.block
    exact Nat.mul_lt_mul_of_pos_right hT hblock
  have hh : h < L.threads := Frame.lt_of_get hX he
  have hf0 : Prologue.first L (T * L.block) = true :=
    (Prologue.first_iff L _).2 (Nat.mul_mod_left _ _)
  have hdiv : T * L.block / L.block = T := Nat.mul_div_cancel _ hblock
  have hscl : SameCluster L (T * L.block) h := ⟨hg0, hh, by rw [hdiv]; exact hcl⟩
  have hj := Prologue.post_cluster hpre hX (len_of_get he).le hr
  have hsync := clusterSync_of_post_event hX hblock hpre.oneDimLaunch.1
    (Prologue.cluster_before hpre hX)
    (Prologue.cluster_arrive hpre hX) (Prologue.cluster_wait hpre hX) hscl he hj
    (i := 20) (by rw [Prologue.clusterIndex_first hf0]; omega)
  have hlen : 21 < (X.tr (T * L.block)).length := by
    obtain ⟨-, i, -, -, hi, h20, -⟩ := hsync
    simp only at hi h20
    omega
  refine ⟨?_, hlen, .single (.inr (.inr (.inr (.inl hsync))))⟩
  -- the state at event 20 is the allocation, which continues to a prologue state
  obtain ⟨p, hp⟩ := Prologue.prologue_state hpre hX hg0 20 (by norm_num)
    (by rw [Prologue.clusterIndex_first hf0]; norm_num) (by omega)
  obtain ⟨p', hp'⟩ := Prologue.prologue_state hpre hX hg0 21 (by norm_num)
    (by rw [Prologue.clusterIndex_first hf0]; norm_num) (by omega)
  have hidx := (stateAt_prologue hpre hX hg0 (by omega) hp).1
  obtain ⟨e, he20⟩ : ∃ e, (X.tr (T * L.block))[20]? = some e :=
    ⟨_, List.getElem?_eq_getElem (by omega)⟩
  have hs := stateAt_succ_inl he20 hp
  rw [hp'] at hs
  obtain ⟨s, w⟩ := p
  have hsite : s = .alloc := by
    cases s with
    | alloc => rfl
    | init i => simp only [Prologue.index] at hidx; have := i.isLt; omega
    | _ => simp only [Prologue.index, hf0, Prologue.fenceIdx, ↓reduceIte] at hidx
           (try split_ifs at hidx) <;> omega
  subst hsite
  obtain ⟨epc, ek⟩ := e
  simp only [Prologue.next] at hs
  split at hs
  · exact ⟨epc, _, _, _, by simp only at *; exact he20⟩
  · simp at hs

/-- **A deallocation is made past the thread's exit wait.** -/
theorem dealloc_waited_fact (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    {g k pc : Nat} {grp : CtaGroup} {dst : Option Loc} {a n : Nat} (hg : g < L.threads)
    (he : X.get (g, k) = some ⟨pc, .tc (.resource grp dst (.dealloc a n))⟩) :
    ExitWaited ((X.tr g).take k) := by
  have htr := Frame.trace (fun _ => sound hpre) hX hg
  obtain ⟨d, hσ⟩ := state_at hpre hX hg he (by intro _ _ h; cases h)
  obtain ⟨t, ins, o, hat, -, hc, hfire⟩ := Frame.fired_site (fun _ => sound hpre) hX he hσ
  have hsite := tmem_site hat hc hfire rfl
  have hI := clusterInv hpre hg htr k _ hσ
  refine hI.2.1 ?_
  rcases d with ⟨site, w⟩ | (l | m | sd | c)
  · exfalso
    change site = .alloc at hsite
    subst hsite
    change kernel.code[Flow.tmemAlloc_0]? = some ins at hc
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tmemAlloc_0)
    obtain ⟨-, -, n', -, hact⟩ := fires_tcAlloc_resource hfire rfl
    cases hact
  · exact hsite.elim
  · exact hsite.elim
  · exact hsite.elim
  · change c.site = .relinquish ∨ c.site = .dealloc at hsite
    change c.site = .relinquish ∨ c.site = .ldBase ∨ c.site = .dealloc ∨ c.site = .exit
    rcases hsite with h | h
    · exact .inl h
    · exact .inr (.inr (.inl h))

set_option maxHeartbeats 8000000 in
/-- **A Tensor Memory data event is a consumer's in its task loop**, and a load returns sixteen
words. -/
theorem data_loop_fact (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    {g k : Nat} {e : Event} (hg : g < L.threads) (he : X.get (g, k) = some e)
    (hd : isTcData e = true) :
    ∃ c, Frame.stateAt (code L) X g k = some (some (.inr (.cons c))) ∧ Consumer.exitOff c = none ∧
      ∀ pc a vals, e = ⟨pc, .tc (.ld a vals .s32x32b)⟩ → vals.length = 16 := by
  have htr := Frame.trace (fun _ => sound hpre) hX hg
  obtain ⟨d, hσ⟩ := state_at hpre hX hg he (by intro _ _ h; subst h; simp [isTcData] at hd)
  obtain ⟨c, rfl, hs⟩ := data_role hpre hX hg he hσ hd
  refine ⟨c, hσ, ?_, fun pc a vals hev => ?_⟩
  · rcases hs with ⟨j, hj⟩ | ⟨j, hj⟩ <;> simp [Consumer.exitOff, hj]
  · subst hev
    obtain ⟨t, ins, o, -, -, hc, hfire⟩ := Frame.fired_site (fun _ => sound hpre) hX he hσ
    change kernel.code[c.site.pc]? = some ins at hc
    change Fires c.site.pc (eventTmpl Prod L g t ins.op) _ o at hfire
    have hb : L.block % 32 = 0 := by rw [hpre.block]
    rcases hs with ⟨j, hj⟩ | ⟨j, hj⟩
    · rw [hj] at hc hfire
      obtain rfl := Option.some.inj (hc.symm.trans (Consumer.code_load j))
      rcases o with _ | u
      · rw [eventTmpl_tcLd_noWait (by hooks_off)] at hfire
        simp only [tcTmpl, Fires] at hfire
        revert hfire
        cases readBits L g t 32 (.reg (Consumer.ldAddr j)) <;>
          simp [ofExec, bind, Except.bind, pure, Except.pure, throw, throwThe,
            MonadExceptOf.throw] <;> split_ifs <;> simp
      · obtain ⟨a', vals', hlen, hev, -⟩ := fires_tcLd (fun _ h => by cases h) hfire
        simp only [Event.mk.injEq, Kind.tc.injEq, TcKind.ld.injEq] at hev
        obtain ⟨-, -, rfl, -⟩ := hev
        rw [hlen, Consumer.ldRegs_len]
    · rw [hj] at hc hfire
      obtain rfl := Option.some.inj (hc.symm.trans (Consumer.code_wait j))
      have hev := fires_tcWaitLd hb hfire
      simp at hev

/-- **An MMA's batch is below the thread's response polls.** Its accumulator commits before it are
fewer than its successful response polls, and a successful response poll that is not its latest
is followed by a read of a response that claims a CTA. -/
theorem mma_tile_fact (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    {g k : Nat} {e : Event} {d : ThreadD} {dst : Nat} {sp : TcMma.OperandSpec} {acc : Bool}
    {mask : List Nat} (hg : g < L.threads) (he : X.get (g, k) = some e)
    (hσ : Frame.stateAt (code L) X g k = some (some d)) (hk : e.kind = .tc (.mma dst sp acc mask)) :
    ((X.tr g).take k).countP
        (commitsTo (Bar.loc L (g / L.block) ⟨.acc, g % L.block / 32 % 2, true⟩)) <
      okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) ((X.tr g).take k) ∧
    ∀ j pc p acq sc, X.get (g, j) =
        some ⟨pc, .wait (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) p true acq sc⟩ →
      okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) ((X.tr g).take j) + 1 <
        okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) ((X.tr g).take k) →
      ∃ pcr, ∃ a : Acc, ∃ bs rr, X.get (g, j + 1) = some ⟨pcr, .rd a bs⟩ ∧
        a.SameFootprint ⟨⟨.shared, g / L.block, L.sharedBase + 144⟩, 16, false, false, .cta, 0,
            false⟩ ∧
        Flow.responseOf bs = some rr ∧ Loader.claims rr := by
  have htr := Frame.trace (fun _ => sound hpre) hX hg
  obtain ⟨m, s, j, rfl, hs, -, -, -⟩ := mma_issue_fact hpre hX hg he hσ hk
  have hk' : k ≤ (X.tr g).length := (len_of_get he).le
  have hrw := role_warp hpre hX hg k hk' _ hσ
  simp only [roleWarp] at hrw
  have c : Mma.Counts L g m ((X.tr g).take k) := threadCounts_run hpre hg htr k _ hσ
  refine ⟨?_, mma_reads_claim hpre hX hg hσ⟩
  · have hacc := c.accRound
    have ht := c.task
    have hcd := c.cond
    simp only [Mma.taskPos, Mma.taskStarted, hs] at ht
    simp only [MmaCond, hs] at hcd
    simp only [hs, show Mma.Site.mma s j ≠ Mma.Site.accCommit from by simp, ↓reduceIte,
      add_zero] at hacc
    rw [hrw.1] at hacc
    change _ < okPolls (Mma.respBar L g) _
    change _ = mcount L g _ / 128 at hacc
    rw [show Bar.loc L (g / L.block) ⟨.acc, g % L.block / 32 % 2, true⟩ =
      Mma.accBar L g (g % L.block / 32 % 2) true from rfl, hacc]
    have h128 : (m.q + s.val) < 128 := by
      have := Nat.mod_lt (mcount L g ((X.tr g).take k)) (show 0 < 128 by decide)
      omega
    have hlt : mcount L g ((X.tr g).take k) < 128 * okPolls (Mma.respBar L g) ((X.tr g).take k) :=
      by
      omega
    exact (Nat.div_lt_iff_lt_mul (by decide)).mpr (by rw [Nat.mul_comm]; exact hlt)

end

end PTX.Kernels.Fp16Gemm8192.Proof
