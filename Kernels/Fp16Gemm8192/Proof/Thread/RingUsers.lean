-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Interface
public import Kernels.Fp16Gemm8192.Proof.Thread.PrologueCluster
public import Kernels.Fp16Gemm8192.Proof.Thread.LoaderIssues
public import Kernels.Fp16Gemm8192.Proof.Thread.MmaCommits
public import Lemmas.Flow.NotObject
public import Kernels.Fp16Gemm8192.Proof.Thread.RoleWarp
public import Lemmas.Flow.NotClc

@[expose] public section

/-! # Which events use the ring objects

Every event of a tracked thread uses the ring objects (the input ring's and the accumulator
ring's mbarriers) only as `RingEvent` says. An event of a site whose instruction is not an
mbarrier instruction uses no object; the object sites are the polls (which `RingEvent` does not
restrict), the loader's arrivals and copies, the consumer threads' accumulator arrivals, the
MMA thread's commits, CTA thread 0's initializations, and the acknowledgement and scheduler
barriers. -/

namespace PTX.Kernels.Fp16Gemm8192.Proof

open PTX PTX.Proof PTX.Flow

noncomputable section

set_option maxRecDepth 100000

section Generic

variable {L : Launch} {g k : Nat} {d : ThreadD} {e : Event}

theorem ringEvent_of_notObject (h : ¬ ObjectKind e.kind) : RingEvent L g k d e where
  wait _ _ _ _ _ _ hk _ := absurd (by rw [hk]; trivial) h
  arrive _ _ _ _ _ _ hk _ := absurd (by rw [hk]; trivial) h
  tensor _ _ _ _ hk _ _ := absurd (by rw [hk]; trivial) h
  commit _ _ _ _ hk _ _ := absurd (by rw [hk]; trivial) h
  init _ _ _ hk _ := absurd (by rw [hk]; trivial) h
  clc _ _ hk := absurd (by rw [hk]; trivial) h
  copy _ hk := h (by rw [hk]; trivial)
  inval _ hk := h (by rw [hk]; trivial)
  loc _ hm := by
    rcases hm with ⟨_, _, _, _, hk⟩ | ⟨_, _, _, _, hk⟩ | ⟨_, _, hk, -⟩ <;>
      exact absurd (by rw [hk]; trivial) h
  wait_leader _ _ _ _ _ _ hk _ _ := absurd (by rw [hk]; trivial) h
  init_site _ _ hk := absurd (by rw [hk]; trivial) h

/-- A poll at `m`, which is barrier `b0` of CTA `c0`, by a thread that polls `b0`. -/
theorem ringEvent_wait {b0 : Bar} {c0 pc q : Nat} {m : Loc} {ok acq : Bool} {sc : MbarScope}
    (he : e = ⟨pc, .wait m q ok acq sc⟩) (hm : m = b0.loc L c0) (hb0 : b0.Valid)
    (hp : b0.pollBy L g d) (hc : c0 = g / L.block)
    (hlead : b0.leaderOnly = true → c0 % 2 = 0 := by intro h; simp [Bar.leaderOnly] at h) :
    RingEvent L g k d e := by
  subst he; exact { wait := fun b cta _ _ _ _ hk hb => by
                      cases hk
                      obtain ⟨rfl, rfl⟩ := Bar.loc_inj hb hb0 hm
                      exact ⟨hp, hc⟩
                    arrive := fun _ _ _ _ _ _ hk _ => by cases hk
                    tensor := fun _ _ _ _ hk _ _ => by cases hk
                    commit := fun _ _ _ _ hk _ _ => by cases hk
                    init := fun _ _ _ hk _ => by cases hk
                    clc := fun _ _ hk => by cases hk
                    copy := fun _ hk => by cases hk
                    inval := fun _ hk => by cases hk
                    loc := fun m' hm' => by
                      rcases hm' with ⟨_, _, _, _, hk⟩ | ⟨_, _, _, _, hk⟩ | ⟨_, _, hk, -⟩
                      · cases hk
                      · cases hk
                        exact ⟨b0, c0, hb0, hm⟩
                      · cases hk
                    wait_leader := fun b cta _ _ _ _ hk hb hlo => by
                      cases hk
                      obtain ⟨rfl, rfl⟩ := Bar.loc_inj hb hb0 hm
                      exact hlead hlo
                    init_site := fun _ _ hk => by cases hk }

/-- A poll whose address evaluates to `m0`, which is barrier `b0` of CTA `c0`. -/
theorem ringEvent_wait_at {b0 : Bar} {c0 : Nat} {t : TState} {p base : Nat} {off : Int}
    {par : Opnd} {acq : Bool} {sc : MbarScope} {pc : Nat} {o : Option TState} {m0 : Loc}
    (hm : mbarLoc L g t base off = .ok m0)
    (hf : Fires pc (eventTmpl Prod L g t (.mbarWait p base off par acq sc)) e o)
    (hb0 : b0.Valid) (hm0 : m0 = b0.loc L c0) (hp : b0.pollBy L g d) (hc : c0 = g / L.block)
    (hlead : b0.leaderOnly = true → c0 % 2 = 0 := by intro h; simp [Bar.leaderOnly] at h) :
    RingEvent L g k d e := by
  rcases fires_mbarWait_kind hf with ⟨m, q, ok, acq', sc', hk⟩ | ⟨f, hk⟩
  · obtain rfl := fires_wait_loc hm hf m q ok acq' sc' hk
    exact ringEvent_wait (e := e) (by rw [← hk]) hm0 hb0 hp hc hlead
  · exact ringEvent_of_notObject (by rw [hk]; exact id)

/-- An arrival at `m`, which is barrier `b0` of CTA `c0`, with an arrival count of one. -/
theorem ringEvent_arrive {b0 : Bar} {c0 pc tx c : Nat} {m : Loc} {rel : Bool} {sc : MbarScope}
    (he : e = ⟨pc, .arrive m tx c rel sc⟩) (hm : m = b0.loc L c0) (hb0 : b0.Valid)
    (hp : b0.arriveBy L g d) (hc : c0 = b0.arriveCta L g) (htx : tx = b0.arriveTx) (hc1 : c = 1) :
    RingEvent L g k d e := by
  subst he; exact { wait := fun _ _ _ _ _ _ hk _ => by cases hk
                    arrive := fun b cta _ _ _ _ hk hb => by
                      cases hk
                      obtain ⟨rfl, rfl⟩ := Bar.loc_inj hb hb0 hm
                      exact ⟨hp, hc, htx, hc1⟩
                    tensor := fun _ _ _ _ hk _ _ => by cases hk
                    commit := fun _ _ _ _ hk _ _ => by cases hk
                    init := fun _ _ _ hk _ => by cases hk
                    clc := fun _ _ hk => by cases hk
                    copy := fun _ hk => by cases hk
                    inval := fun _ hk => by cases hk
                    loc := fun m' hm' => by
                      rcases hm' with ⟨_, _, _, _, hk⟩ | ⟨_, _, _, _, hk⟩ | ⟨_, _, hk, -⟩
                      · cases hk
                        exact ⟨b0, c0, hb0, hm⟩
                      · cases hk
                      · cases hk
                    wait_leader := fun _ _ _ _ _ _ hk _ _ => by cases hk
                    init_site := fun _ _ hk => by cases hk }

/-- A copy completing at `sp.mbar`, which is barrier `b0` of CTA `c0`, with its bytes. -/
theorem ringEvent_tensor {b0 : Bar} {c0 pc a : Nat} {sp : TensorCopy.Spec}
    (he : e = ⟨pc, .tensorIssue a sp⟩) (hm : sp.mbar = b0.loc L c0) (hb0 : b0.Valid)
    (hp : b0.copyBy d) (hc : c0 = 2 * (g / L.block / 2))
    (hbytes : TensorTransfer.bytes sp.descriptor = b0.completeBytes) : RingEvent L g k d e := by
  subst he; exact { wait := fun _ _ _ _ _ _ hk _ => by cases hk
                    arrive := fun _ _ _ _ _ _ hk _ => by cases hk
                    tensor := fun _ _ b cta hk hm' hb => by
                      cases hk
                      obtain ⟨rfl, rfl⟩ := Bar.loc_inj hb hb0 (hm'.symm.trans hm)
                      exact ⟨hp, hc, hbytes⟩
                    commit := fun _ _ _ _ hk _ _ => by cases hk
                    init := fun _ _ _ hk _ => by cases hk
                    clc := fun _ _ hk => by cases hk
                    copy := fun _ hk => by cases hk
                    inval := fun _ hk => by cases hk
                    loc := fun _ hm' => by
                      rcases hm' with ⟨_, _, _, _, hk⟩ | ⟨_, _, _, _, hk⟩ | ⟨_, _, hk, -⟩ <;>
                        cases hk
                    wait_leader := fun _ _ _ _ _ _ hk _ _ => by cases hk
                    init_site := fun _ _ hk => by cases hk }

/-- A leader CTA's thread commits to the barrier at `a` of its CTA, mask 3, over its cluster. -/
theorem ringEvent_commit {b0 : Bar} {pc a : Nat} {grp : CtaGroup}
    (he : e = ⟨pc, .tc (.commit ⟨grp, ⟨.shared, g / L.block, a⟩, 3, g / L.block / 2 * 2, 2⟩)⟩)
    (hev : g / L.block % 2 = 0) (hb0 : b0.Valid) (ha : a = L.sharedBase + b0.off)
    (hp : b0.commitBy d) : RingEvent L g k d e := by
  subst he
  have hloc : ∀ m', NamesMbar (Kind.tc (.commit ⟨grp, ⟨.shared, g / L.block, a⟩, 3,
    g / L.block / 2 * 2, 2⟩))
      m' → ∃ (b : Bar) (cta : Nat), b.Valid ∧ m' = b.loc L cta := by
    intro m' hm'
    rcases hm' with ⟨_, _, _, _, hk⟩ | ⟨_, _, _, _, hk⟩ | ⟨sp', rank, hk, ht'⟩
    · cases hk
    · cases hk
    · cases hk
      simp only [TcCommit.target] at ht'
      by_cases hr : (rank : ℕ) < 2 ∧ BitVec.toNat (3 : BitVec 16) / 2 ^ (rank : ℕ) % 2 = 1
      · simp only [hr.1, hr.2, and_self, ↓reduceIte, Option.some.injEq] at ht'
        exact ⟨b0, g / L.block / 2 * 2 + rank, hb0, by rw [← ht', ha]; simp only [Bar.loc]⟩
      · simp only [hr, ↓reduceIte, reduceCtorEq] at ht'
  refine { wait := fun _ _ _ _ _ _ hk _ => by cases hk
           arrive := fun _ _ _ _ _ _ hk _ => by cases hk
           tensor := fun _ _ _ _ hk _ _ => by cases hk
           commit := fun sp rank b cta hk ht hb => ?_
           init := fun _ _ _ hk _ => by cases hk
           clc := fun _ _ hk => by cases hk
           copy := fun _ hk => by cases hk
           inval := fun _ hk => by cases hk
           loc := hloc
           wait_leader := fun _ _ _ _ _ _ hk _ _ => by cases hk
           init_site := fun _ _ hk => by cases hk }
  cases hk
  simp only [TcCommit.target] at ht
  by_cases hr : (rank : ℕ) < 2 ∧ BitVec.toNat (3 : BitVec 16) / 2 ^ (rank : ℕ) % 2 = 1
  · simp only [hr.1, hr.2, and_self, ↓reduceIte, Option.some.injEq, Bar.loc, Loc.mk.injEq,
      true_and] at ht
    obtain rfl := Bar.off_inj hb hb0 (by have := ht.2; omega)
    refine ⟨hp, hev, hr.1, by omega, ?_⟩
    simp only [Bar.loc, ← ht.2]
  · simp only [hr, ↓reduceIte, reduceCtorEq] at ht

/-- A register of a state's facts. -/
theorem reg_at {t : TState} {live : List Nat} {val : Nat → Value} {r : Nat}
    (h : Holds t.regs (Flow.factsFrom live val)) (hl : r ∈ live) : t.regs r = some (val r) :=
  holds_mem h (Flow.mem_factsFrom hl)

end Generic

section Bytes

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {t u : TState} {e : Event}

/-- A copy through a map held as the A or B parameter moves sixteen kilobytes. -/
theorem copy_bytes (hpre : Pre P L mem0) {grp : Bool} {dst mb r : Nat} {off moff : Int}
    {cs : List Opnd} {pc : Nat}
    (hf : Fires pc (eventTmpl Prod L g t (.cpTensor true grp dst off (.reg r) cs mb moff none
      .tile))
      e (some u))
    {name : String} (hr0 : t.regs r = some (.ptr 64 true (.param name) 0))
    (hn : name = "gemm_kernel_param_0" ∨ name = "gemm_kernel_param_1") :
    ∀ a sp, e.kind = .tensorIssue a sp → TensorTransfer.bytes sp.descriptor = 16384 := by
  intro a sp hk
  obtain ⟨hma, d, hd, hdesc⟩ := fires_cpTensor_desc hf a sp hk
  simp only [TensorMode.transfer] at hdesc
  obtain ⟨M, hpar, h1, h2, D, hD, hbD⟩ : ∃ M, L.paramObjects name = some (mapParam name, M) ∧
      M % 128 = 0 ∧ M + 128 ≤ 2 ^ 64 ∧ ∃ D : Σ n, TensorDescriptor.Descriptor n,
      L.tensorMaps M = some D ∧ TensorTransfer.bytes D.2 = 16384 := by
    rcases hn with rfl | rfl
    · exact ⟨_, hpre.paramA, hpre.mapAlignment.1, hpre.mapRange.1, _, hpre.mapA, by
        norm_num [TensorTransfer.bytes, Fp16Gemm8192.mapA, encodeTiled, TensorTile.count,
          TensorTile.step, TensorTile.rows, TensorTile.rowsOf, TensorDescriptor.Format.bytes]⟩
    · exact ⟨_, hpre.paramB, hpre.mapAlignment.2.1, hpre.mapRange.2.1, _, hpre.mapB, by
        norm_num [TensorTransfer.bytes, Fp16Gemm8192.mapB, encodeTiled, TensorTile.count,
          TensorTile.step, TensorTile.rows, TensorTile.rowsOf, TensorDescriptor.Format.bytes]⟩
  obtain rfl : a = M := by
    simp only [tensorMapAddress, readValue, readReg, hr0, hpar, mapParam, ParamObjectDecl.bytes,
      bind, Except.bind, pure, Except.pure, le_refl, Nat.ofNat_pos, h1,
      show M + 128 ≤ 2 ^ 64 from h2, and_self, ↓reduceIte, Except.ok.injEq] at hma
    exact hma.symm
  rw [hD] at hd
  obtain rfl := Option.some.inj hd
  rw [hdesc]
  exact hbD

/-- An acknowledgement through a cluster pointer to the leader CTA's acknowledgement barrier. -/
theorem ringEvent_ack (hpre : Pre P L mem0) (hg : g < L.threads) {k : Nat} {d : ThreadD}
    {base : Nat} {rel : Bool} {sc : MbarScope} {pc : Nat} {o : Option TState}
    (hr : t.regs base = some (.ptr 32 false (.shared (g / L.block) (2 * ((g / L.block) / 2)))
          (BitVec.ofNat 64 (L.sharedBase + 128))))
    (hf : Fires pc (eventTmpl Prod L g t (.mbarArrive base 0 (.imm 0) (.imm 1) true rel sc)) e o)
    (hd : Bar.arriveBy L g d ⟨.clc, 0, false⟩) : RingEvent L g k d e := by
  have hbase : L.sharedBase + 230400 ≤ 2 ^ 18 := hpre.sharedRange
  have hal := hpre.sharedAlignment
  have hcta := cta_lt hpre hg
  have hm := mbarClusterLoc_ptr hr hg (by rw [hpre.grid] at hcta ⊢; omega)
    (by simp only [clusterOfCta_eq hpre]; omega) (by omega) (by omega)
  obtain ⟨rel', sc', he, -⟩ := fires_arrive_at (cluster := true) (by simpa using hm)
    (show readBits L g t 32 (.imm 0) = .ok 0 by rfl)
    (show readBits L g t 32 (.imm 1) = .ok 1 by rfl) hf
  exact ringEvent_arrive (b0 := ⟨.clc, 0, false⟩) (c0 := 2 * (g / L.block / 2)) he
    (by simp only [Bar.loc, Bar.off]) (show (0 : Nat) < 1 by decide) hd rfl rfl rfl

end Bytes

namespace Loader

variable {P : Params} {L : Launch} {mem0 : Mem0} {g k : Nat} {t u : TState} {e : Event}
  {ins : Instr}

theorem ringEvent (hpre : Pre P L mem0) (hg : g < L.threads) {l : D} (hal : ArriveLead L g l)
    (h : At t l.site.pc (facts L g l)) (hc : kernel.code[l.site.pc]? = some ins)
    (hf : Fires l.site.pc (eventTmpl Prod L g t ins.op) e (some u))
    (hop : ¬ objectOp ins.op = false) :
    RingEvent L g k (.inr (.loader l)) e := by
  obtain ⟨s, m, n, q, cp, r, x⟩ := l
  cases s with
  | wait b =>
    obtain ⟨ok, acq, sc, he⟩ := wait_event hpre b rfl h hc hf
    exact ringEvent_wait (b0 := ⟨.input, (InputRing.slotOf b).val, false⟩) (c0 := g / L.block)
      he (InputRing.emptyLoc_bar L _ _) (InputRing.slotOf b).isLt ⟨_, rfl⟩ rfl
  | drain i =>
    obtain ⟨ok, acq, sc, he⟩ := drain_event hpre i rfl h hc hf
    exact ringEvent_wait (b0 := ⟨.input, i.val, false⟩) (c0 := g / L.block) he
      (InputRing.emptyLoc_bar L _ _) i.isLt ⟨_, rfl⟩ rfl
  | clcWait =>
    obtain ⟨p, ok, acq, sc, -, he⟩ := clcWait_event hpre rfl h hc hf
    exact ringEvent_wait (b0 := ⟨.clc, 0, true⟩) (c0 := g / L.block) he
      (by simp only [Bar.loc, Bar.off]) (show (0 : Nat) < 1 by decide) ⟨_, rfl⟩ rfl
  | ack =>
    code_at hc; subst hc
    exact ringEvent_ack hpre hg ((reg_at h.2.2.2.2 (by lit_mem)).trans
      (congrArg some (by loader_values))) hf (.inl ⟨_, rfl⟩)
  | arrive b =>
    obtain ⟨rel, sc, he⟩ := arrive_event hpre hg b rfl h hc hf
    have hlead : g / L.block % 2 = 0 := by simpa [leader] using hal b rfl
    exact ringEvent_arrive (b0 := ⟨.input, (InputRing.slotOf b).val, true⟩)
      (c0 := 2 * (g / L.block / 2)) he (InputRing.fullLoc_bar L _ _) (InputRing.slotOf b).isLt
      ⟨⟨_, rfl⟩, hlead⟩ rfl rfl rfl
  | load b j =>
    have hb : ∀ a sp, e.kind = .tensorIssue a sp → TensorTransfer.bytes sp.descriptor = 16384 := by
      simp only at h hc hf
      fin_cases b <;> fin_cases j <;>
      · code_at hc
        subst hc
        exact copy_bytes hpre hf ((reg_at h.2.2.2.2 (by lit_mem)).trans
          (congrArg some (by loader_values; rfl))) (by simp)
    obtain ⟨a, sp, he, hm⟩ := load_event hpre hg b j rfl h hc hf
    exact ringEvent_tensor (b0 := ⟨.input, (InputRing.slotOf b).val, true⟩)
      (c0 := 2 * (g / L.block / 2)) he (hm.trans (InputRing.fullLoc_bar L _ _))
      (InputRing.slotOf b).isLt ⟨_, rfl⟩ rfl (hb a sp (by rw [he]))
  | _ => code_at hc; subst hc; simp [objectOp] at hop

end Loader

namespace Mma

variable {P : Params} {L : Launch} {mem0 : Mem0} {g k : Nat} {t u : TState} {e : Event}
  {ins : Instr}

theorem ringEvent (hpre : Pre P L mem0) (hg : g < L.threads) {d : D} (hi : Inv d)
    (hl : Lead L g d) (h : At t d.site.pc (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e (some u))
    (hop : ¬ objectOp ins.op = false) :
    RingEvent L g k (.inr (.mma d)) e := by
  obtain ⟨s, w, q, fp, ap, cp, r, x⟩ := d
  cases s with
  | full s =>
    obtain ⟨ok, acq, sc, he⟩ := full_event hpre s rfl hi h hc hf
    have hev : g / L.block % 2 = 0 := by
      rcases hl with h' | h' | h' | h' <;> first | (simp only at h'; cases h') | exact h'
    exact ringEvent_wait (b0 := ⟨.input, s.val, true⟩) (c0 := g / L.block) he
      (by simp only [Bar.loc, Bar.off, Nat.add_assoc]) s.isLt ⟨_, rfl⟩ rfl (fun _ => hev)
  | accWait =>
    obtain ⟨ok, acq, sc, he⟩ := accWait_event hpre rfl hi h hc hf
    have hev : g / L.block % 2 = 0 := by
      rcases hl with h' | h' | h' | h' <;> first | (simp only at h'; cases h') | exact h'
    exact ringEvent_wait (b0 := ⟨.acc, w % 2, false⟩) (c0 := g / L.block) he
      (by simp only [Bar.loc, Bar.off, Loc.mk.injEq, true_and]; omega)
      (Nat.mod_lt _ (by decide)) ⟨_, rfl, rfl⟩ rfl (fun _ => hev)
  | clcWait =>
    obtain ⟨p, ok, acq, sc, -, he⟩ := clcWait_event hpre rfl h hc hf
    exact ringEvent_wait (b0 := ⟨.clc, 0, true⟩) (c0 := g / L.block) he
      (by simp only [Bar.loc, Bar.off]) (show (0 : Nat) < 1 by decide) ⟨_, rfl⟩ rfl
  | mma s j =>
    obtain ⟨ad, bd, en, hc'⟩ := code_mma s j; rw [hc'] at hc; cases hc; simp [objectOp] at hop
  | ack =>
    code_at hc; subst hc
    exact ringEvent_ack hpre hg ((reg_at h.2.2.2.2 (by lit_mem)).trans
      (congrArg some (by mma_values))) hf (.inr (.inl ⟨⟨_, rfl⟩, by
        rcases hl with h | h | h | h <;> first | cases h | exact h⟩))
  | commit s =>
    have hev : g / L.block % 2 = 0 := by rcases hl with h' | h' | h' | h' <;>
      first | cases h' | exact h'
    exact ringEvent_commit (b0 := ⟨.input, s.val, false⟩) (commit_event hpre hg s rfl h hc hf) hev
      s.isLt (by simp only [Bar.off]; omega) ⟨_, rfl⟩
  | accCommit =>
    have hev : g / L.block % 2 = 0 := by rcases hl with h' | h' | h' | h' <;>
      first | cases h' | exact h'
    exact ringEvent_commit (b0 := ⟨.acc, w % 2, true⟩) (accCommit_spec hpre hg rfl h hc hf) hev
      (Nat.mod_lt _ (by decide)) (by simp only [Bar.off]; omega) ⟨_, rfl, rfl⟩
  | _ => code_at hc; subst hc; simp [objectOp] at hop

end Mma

namespace Scheduler

variable {P : Params} {L : Launch} {mem0 : Mem0} {g k : Nat} {t u : TState} {e : Event}
  {ins : Instr}

theorem ringEvent (hpre : Pre P L mem0) (hg : g < L.threads) {d : D}
    (hl : Lead L g d) (h : At t d.site.pc (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e (some u))
    (hop : ¬ objectOp ins.op = false) :
    RingEvent L g k (.inr (.sched d)) e := by
  have hbase : L.sharedBase + 230400 ≤ 2 ^ 18 := hpre.sharedRange
  have hal := hpre.sharedAlignment
  obtain ⟨s, ap, cp, r, x⟩ := d
  cases s with
  | ackWait =>
    code_at hc; subst hc
    exact ringEvent_wait_at (b0 := ⟨.clc, 0, false⟩) (c0 := g / L.block)
      (mbarLoc_b32 (L := L) (g := g) ((reg_at h.2.2.2.2 (by lit_mem)).trans
        (congrArg some (by sched_values))) (a := L.sharedBase + 128) (by omega) (by omega))
      hf (show (0 : Nat) < 1 by decide) (by simp only [Bar.loc, Bar.off]) ⟨_, rfl⟩ rfl
      (fun _ => by have := hl (.inl rfl); simpa [Loader.leader] using this)
  | clcWait =>
    code_at hc; subst hc
    exact ringEvent_wait_at (b0 := ⟨.clc, 0, true⟩) (c0 := g / L.block)
      (mbarLoc_b32 (a := L.sharedBase + 104)
        ((reg_at h.2.2.2.2 (by lit_mem)).trans (congrArg some (by sched_values))) (by omega)
        (by omega)) hf (show (0 : Nat) < 1 by decide)
      (by simp only [Bar.loc, Bar.off]) ⟨_, rfl⟩ rfl
  | ack =>
    code_at hc; subst hc
    exact ringEvent_ack hpre hg ((reg_at h.2.2.2.2 (by lit_mem)).trans
      (congrArg some (by sched_values))) hf (.inr (.inr (.inl ⟨_, rfl⟩)))
  | arriveTx =>
    code_at hc; subst hc
    have hm := mbarLoc_b32 (L := L) (g := g) (base := 637)
      ((reg_at h.2.2.2.2 (by lit_mem)).trans (congrArg some (by sched_values)))
      (a := L.sharedBase + 104) (by omega) (by omega)
    have hn : t.regs 638 = some (b32 16) :=
      (reg_at h.2.2.2.2 (by lit_mem)).trans (congrArg some (by sched_values))
    obtain ⟨rel, sc, he, -⟩ := fires_arrive_at (cluster := false) (by simpa using hm)
      (show readBits L g t 32 (.reg 638) = .ok (truncBits 32 (BitVec.ofNat 64 16)) by
        simp [readBits, readReg, hn, b32, bind, Except.bind, pure, Except.pure])
      (show readBits L g t 32 (.imm 1) = .ok 1 by rfl) hf
    exact ringEvent_arrive (b0 := ⟨.clc, 0, true⟩) (c0 := g / L.block) he
      (by simp only [Bar.loc, Bar.off]) (show (0 : Nat) < 1 by decide) ⟨_, rfl⟩ rfl rfl rfl
  | tryCancel =>
    code_at hc; subst hc
    have hl := hl (.inr rfl)
    simp only [Loader.leader, decide_eq_true_eq] at hl
    have hr : t.regs 635 = some (b32 (L.sharedBase + 104)) :=
      (reg_at h.2.2.2.2 (by lit_mem)).trans (congrArg some (by sched_values))
    have hm := mbarLoc_b32 (L := L) (g := g) hr (by omega) (by omega)
    rcases fires_clcTryCancel_kind hf with ⟨sp, tg, hk⟩ | ⟨f, hk⟩
    · have hrr : t.regs 634 = some (b32 (L.sharedBase + 144)) :=
        (reg_at h.2.2.2.2 (by lit_mem)).trans (congrArg some (by sched_values))
      obtain ⟨hresp, hsp⟩ := fires_clcIssue_spec (effAddr_b32 hrr (by omega)) hm hf sp tg hk
      have htg := fires_clcIssue_targets hf sp tg hk
      exact { wait := fun _ _ _ _ _ _ h' _ => by rw [hk] at h'; cases h'
              arrive := fun _ _ _ _ _ _ h' _ => by rw [hk] at h'; cases h'
              tensor := fun _ _ _ _ h' _ _ => by rw [hk] at h'; cases h'
              commit := fun _ _ _ _ h' _ _ => by rw [hk] at h'; cases h'
              init := fun _ _ _ h' _ => by rw [hk] at h'; cases h'
              clc := fun sp' tg' h' => by
                rw [hk] at h'; cases h'
                refine ⟨⟨.clc, 0, true⟩, Nat.one_pos, ⟨⟨_, rfl⟩, hl⟩,
                  by rw [hsp]; simp only [Bar.loc, Bar.off], by rw [hresp]; rfl, fun c hc' => ?_⟩
                simpa [clusterOfCta_eq hpre] using (htg _ hc').2
              copy := fun _ h' => by rw [hk] at h'; cases h'
              inval := fun _ h' => by rw [hk] at h'; cases h'
              loc := fun _ hm' => by
                rcases hm' with ⟨_, _, _, _, h'⟩ | ⟨_, _, _, _, h'⟩ | ⟨_, _, h', -⟩ <;>
                  (rw [hk] at h'; cases h')
              wait_leader := fun _ _ _ _ _ _ h' _ _ => by rw [hk] at h'; cases h'
              init_site := fun _ _ h' => by rw [hk] at h'; cases h' }
    · exact ringEvent_of_notObject (by rw [hk]; exact id)
  | _ => code_at hc; subst hc; simp [objectOp] at hop

end Scheduler

namespace Consumer

variable {P : Params} {L : Launch} {mem0 : Mem0} {g k : Nat} {t u : TState} {e : Event}
  {ins : Instr}

theorem ringEvent (hpre : Pre P L mem0) (hg : g < L.threads) {d : D}
    (hw : tidOf L g / 32 < 8) (hfirst : d.site = .ack → first L g = true)
    (h : Holds t.regs (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e (some u))
    (hop : ¬ objectOp ins.op = false) :
    RingEvent L g k (.inr (.cons d)) e := by
  have hbase : L.sharedBase + 230400 ≤ 2 ^ 18 := hpre.sharedRange
  have hal := hpre.sharedAlignment
  have hj : tidOf L g / 32 / 4 < 2 := by omega
  obtain ⟨s, m, n, m', n', cp, ap, resp, x, acc, base⟩ := d
  cases s with
  | clcWait =>
    code_at hc; subst hc
    exact ringEvent_wait_at (b0 := ⟨.clc, 0, true⟩) (c0 := g / L.block)
      (mbarLoc_b32 (a := L.sharedBase + 104)
        ((reg_at h (by lit_mem)).trans (congrArg some (by cons_values))) (by omega)
        (by omega)) hf (show (0 : Nat) < 1 by decide)
      (by simp only [Bar.loc, Bar.off]) ⟨_, rfl⟩ rfl
  | accWait =>
    code_at hc; subst hc
    exact ringEvent_wait_at (b0 := ⟨.acc, tidOf L g / 32 / 4, true⟩) (c0 := g / L.block)
      (mbarLoc_b32 (L := L) (g := g) ((reg_at h (by lit_mem)).trans
        (congrArg some (by cons_values)))
        (a := L.sharedBase + 8 * (tidOf L g / 32 / 4) + 72) (by omega) (by omega))
      hf hj (by simp only [Bar.loc, Bar.off, Loc.mk.injEq, true_and]; omega) ⟨⟨_, rfl⟩, rfl⟩ rfl
  | ack =>
    code_at hc; subst hc
    exact ringEvent_ack hpre hg ((reg_at h (by lit_mem)).trans
      (congrArg some (by cons_values))) hf (.inr (.inr (.inr ⟨⟨_, rfl⟩, hfirst rfl⟩)))
  | accArrive =>
    code_at hc; subst hc
    have hcta := cta_lt hpre hg
    have hm := mbarClusterLoc_ptr (base := 433) (cta := 2 * (g / L.block / 2))
      (a := L.sharedBase + 8 * (tidOf L g / 32 / 4) + 88)
      ((reg_at h (by lit_mem)).trans (congrArg some (by cons_values))) hg
      (by rw [hpre.grid] at hcta ⊢; omega)
      (by simp only [clusterOfCta_eq hpre]; omega) (by omega) (by omega)
    obtain ⟨rel, sc, he, -⟩ := fires_arrive_at (cluster := true) (by simpa using hm)
      (show readBits L g t 32 (.imm 0) = .ok 0 by rfl)
      (show readBits L g t 32 (.imm 1) = .ok 1 by rfl) hf
    exact ringEvent_arrive (b0 := ⟨.acc, tidOf L g / 32 / 4, false⟩)
      (c0 := 2 * (g / L.block / 2) ) he
      (by simp only [Bar.loc, Bar.off, Loc.mk.injEq, true_and]; omega) hj
      ⟨⟨_, rfl⟩, rfl⟩ rfl rfl rfl
  | load j => fin_cases j <;> (code_at hc; subst hc; simp [objectOp] at hop)
  | loadWait j => fin_cases j <;> (code_at hc; subst hc; simp [objectOp] at hop)
  | drain j => fin_cases j <;> (code_at hc; subst hc; simp [objectOp] at hop)
  | barA j => fin_cases j <;> (code_at hc; subst hc; simp [objectOp] at hop)
  | barB j => fin_cases j <;> (code_at hc; subst hc; simp [objectOp] at hop)
  | fence j => fin_cases j <;> (code_at hc; subst hc; simp [objectOp] at hop)
  | tma j => fin_cases j <;> (code_at hc; subst hc; simp [objectOp] at hop)
  | commit j => fin_cases j <;> (code_at hc; subst hc; simp [objectOp] at hop)
  | store j i el => fin_cases j <;> fin_cases i <;> (code_at hc; subst hc; simp [objectOp] at hop)
  | _ => code_at hc; subst hc; simp [objectOp] at hop

end Consumer

section Execution

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- Prologue initialization `i` is of ring barrier `b` exactly when the offsets agree, and then
it is the barrier's initialization, with its index and count. -/
theorem init_bar (i : Fin 18) {b : Bar} (hb : b.Valid) (h : Prologue.initOff i = b.off) :
    2 + i.val = b.initIndex ∧ Prologue.initCount i = b.count := by
  obtain ⟨r, s, f⟩ := b
  simp only [Bar.Valid] at hb; simp only [Bar.initIndex]
  cases r <;> cases f <;> simp only [Ring.slots] at hb <;>
    fin_cases i <;> simp only [Prologue.initOff, Bar.off, Prologue.initCount, Bar.count] at h ⊢ <;>
    constructor <;> first | trivial | omega

/-- The prologue initialization of ring barrier `b`. -/
def Bar.initSlot (b : Bar) : Fin 18 := ⟨(b.off / 8 - 1) % 18, Nat.mod_lt _ (by decide)⟩

theorem Bar.initSlot_off {b : Bar} (hb : b.Valid) : Prologue.initOff b.initSlot = b.off := by
  obtain ⟨r, s, f⟩ := b
  simp only [Bar.Valid] at hb
  cases r <;> cases f <;> simp only [Ring.slots] at hb <;>
    · interval_cases s <;> rfl

/-- The prologue initializes an input object only on its CTA's thread 0, as its initialization. -/
theorem prologue_ringEvent (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    {g k : Nat} {e : Event} {p : Prologue.D} (hg : g < L.threads) (he : X.get (g, k) = some e)
    (hσ : Frame.stateAt (code L) X g k =
      some (some (.inl p))) {t : TState} {ins : Instr} {o : Option TState}
    (hc : kernel.code[p.site.pc]? = some ins)
    (hf : Fires p.site.pc (eventTmpl Prod L g t ins.op) e o)
    (hop : ¬ objectOp ins.op = false) : RingEvent L g k (.inl p) e := by
  have hlen : k ≤ (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1.le
  obtain ⟨hidx, -, hcanon⟩ := (onPath_all hpre hX hg k hlen).1 p hσ
  obtain ⟨s, w⟩ := p
  cases s with
  | init i =>
    have hf0 : g % L.block = 0 := (Prologue.first_iff L g).1 (hcanon.2.1 i rfl)
    have hk : k = 2 + i.val := by simpa [Prologue.index] using hidx
    subst hk
    have hkind := init_event hpre hX hg hf0 i he
    exact
      { wait := fun _ _ _ _ _ _ hk _ => by rw [hkind] at hk; cases hk
        arrive := fun _ _ _ _ _ _ hk _ => by rw [hkind] at hk; cases hk
        tensor := fun _ _ _ _ hk _ _ => by rw [hkind] at hk; cases hk
        commit := fun _ _ _ _ hk _ _ => by rw [hkind] at hk; cases hk
        init := fun b cta c hk hb => by
          simp only [hkind, Kind.mbInit.injEq] at hk
          obtain ⟨hl, rfl⟩ := hk
          simp only [Prologue.initLoc, Bar.loc, Loc.mk.injEq, true_and] at hl
          exact ⟨hf0, hl.1.symm, init_bar i hb (by omega)⟩
        clc := fun _ _ hk => by rw [hkind] at hk; cases hk
        copy := fun _ hk => by rw [hkind] at hk; cases hk
        inval := fun _ hk => by rw [hkind] at hk; cases hk
        loc := fun _ hm' => by
          rcases hm' with ⟨_, _, _, _, hk⟩ | ⟨_, _, _, _, hk⟩ | ⟨_, _, hk, -⟩ <;>
            (rw [hkind] at hk; cases hk)
        wait_leader := fun _ _ _ _ _ _ hk _ _ => by rw [hkind] at hk; cases hk
        init_site := fun m c hk => by
          simp only [hkind, Kind.mbInit.injEq] at hk
          obtain ⟨rfl, rfl⟩ := hk
          refine ⟨hf0, rfl, ?_, ?_, ?_, rfl, ?_, ?_⟩
          · simp only [Prologue.initLoc, Nat.add_sub_cancel_left]
            fin_cases i <;> rfl
          · fin_cases i <;> decide
          · fin_cases i <;> decide
          · simp only [Prologue.initLoc]
            fin_cases i <;> simp only [Prologue.initOff] <;> omega
          · simp only [Prologue.initLoc]
            fin_cases i <;> simp only [Prologue.initOff] <;> omega }
  | _ => code_at hc; subst hc; simp [objectOp] at hop

/-- Every event of a tracked thread uses the input ring's objects as `RingEvent` says. -/
theorem ring_event (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X) {g k : Nat}
    {e : Event} {d : ThreadD} (hg : g < L.threads) (he : X.get (g, k) = some e)
    (hσ : Frame.stateAt (code L) X g k = some (some d)) : RingEvent L g k d e := by
  obtain ⟨t, ins, o, hat, hinv, hc, hfire⟩ := Frame.fired_site (fun _ => sound hpre) hX he hσ
  cases o with
  | none => exact ringEvent_of_notObject (fires_none_notObject hfire)
  | some u =>
    by_cases hop : objectOp ins.op = false
    · exact ringEvent_of_notObject (notObject_of_op hop hfire)
    rcases d with p | (l | m | s | c)
    · exact prologue_ringEvent hpre hX hg he hσ hc hfire hop
    · exact Loader.ringEvent hpre hg hinv.2 hat hc hfire hop
    · exact Mma.ringEvent hpre hg hinv.1 hinv.2.2 hat hc hfire hop
    · exact Scheduler.ringEvent hpre hg hinv.2 hat hc hfire hop
    · have hw := role_warp hpre hX hg k (List.getElem?_eq_some_iff.mp he).1.le _ hσ
      simp only [roleWarp, Prologue.warpOf] at hw
      exact Consumer.ringEvent hpre hg hw hinv.2.2 hat.2.2.2.2 hc hfire hop

/-- A poll is on an mbarrier of the polling thread's own CTA. -/
theorem wait_local (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X) {g k : Nat}
    {e : Event} {d : ThreadD} (hg : g < L.threads) (he : X.get (g, k) = some e)
    (hσ : Frame.stateAt (code L) X g k =
      some (some d)) {m : Loc} {p : Nat} {ok acq : Bool} {sc : MbarScope}
    (hk : e.kind = .wait m p ok acq sc) : m.space = .shared ∧ m.cta = g / L.block := by
  obtain ⟨_, hfo⟩ := (Frame.trace (fun _ => sound hpre) hX hg).fired_at he hσ
  obtain ⟨t, ins, -, -, -, hfire⟩ := Code.fired_site (sound hpre hg) hfo
  exact fires_wait_local hfire hk

/-- Before a role's event, CTA thread 0 of each cluster CTA has initialized each ring barrier,
published to the event. -/
theorem ring_initialized (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    {g j : Nat} {ev : Event} {r : Prologue.Role} {b : Bar} {cta : Nat} (hg : g < L.threads)
    (he : X.get (g, j) = some ev) (hσ : Frame.stateAt (code L) X g j =
      some (some (.inr r))) (hbv : b.Valid)
    (hcta : cta < L.grid) (hcl : L.clusterOfCta cta = L.clusterOfCta (g / L.block)) :
    ∃ pc, X.get (cta * L.block, b.initIndex) = some ⟨pc, .mbInit (b.loc L cta) b.count⟩ ∧
      baseCausality L X (cta * L.block, b.initIndex) (g, j) := by
  have hblock : 0 < L.block := by rw [hpre.block]; norm_num
  set g0 := cta * L.block with hg0
  have hg0t : g0 < L.threads := Nat.mul_lt_mul_of_pos_right hcta hblock
  have hf0 : g0 % L.block = 0 := Nat.mul_mod_left _ _
  have hc0 : g0 / L.block = cta := Nat.mul_div_cancel _ hblock
  have hcl' : SameCluster L g0 g := ⟨hg0t, hg, by rw [hc0, hcl]⟩
  have hj := Prologue.post_cluster hpre hX (List.getElem?_eq_some_iff.mp he).1.le hσ
  set i := b.initSlot
  have hloc : Prologue.initLoc L g0 i = b.loc L cta := by
    simp only [Prologue.initLoc, Bar.loc, hc0, i, Bar.initSlot_off hbv]
  have hsync := clusterSync_of_post_event hX hblock hpre.oneDimLaunch.1
    (Prologue.cluster_before hpre hX)
    (Prologue.cluster_arrive hpre hX) (Prologue.cluster_wait hpre hX) hcl' he hj
    (i := 2 + i.val) (by rw [Prologue.clusterIndex_first ((Prologue.first_iff L g0).2 hf0)]; omega)
  have hhb : baseCausality L X (g0, 2 + i.val) (g, j) :=
    Relation.TransGen.single (Or.inr (Or.inr (Or.inr (Or.inl hsync))))
  obtain ⟨-, a, -, -, ha, hai, -, -⟩ := hsync
  obtain ⟨e0, he0⟩ : ∃ e0, X.get (g0, 2 + i.val) = some e0 :=
    ⟨_, List.getElem?_eq_getElem (by omega)⟩
  have hkind := init_event hpre hX hg0t hf0 i he0
  rw [hloc] at hkind
  obtain ⟨hidx, hcnt⟩ := init_bar i hbv (Bar.initSlot_off hbv)
  rw [← hidx]
  refine ⟨e0.pc, ?_, ?_⟩
  · rw [he0, ← hcnt, ← hkind]
  · exact hhb

end Execution

end
end PTX.Kernels.Fp16Gemm8192.Proof
