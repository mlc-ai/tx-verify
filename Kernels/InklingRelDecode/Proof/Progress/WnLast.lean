-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Progress.WnShape
public import Kernels.InklingRelDecode.Proof.Progress.Collective
public import Kernels.InklingRelDecode.Proof.Interface.LkBar
public import Kernels.InklingRelDecode.Proof.Interface.LedgerEvents
public import Kernels.InklingRelDecode.Proof.Interface.Lk4Class
public import Kernels.InklingRelDecode.Proof.Interface.IpTmOps
public import Lemmas.Execution.NoBarArrive
public import Lemmas.Flow.Resource
public import Lemmas.Flow.NotTcData

@[expose] public section

/-!
# `WarpCollFacts.last` from the lockstep of the lanes

The last event of a lane before its warp collective either never blocks or is a blocking event:
a register request, a named-barrier `bar.sync` or a warp-collective `tcgen05` event (the kernel has
no cluster barrier, no `bar.arrive` and no group wait). A blocking event is fired from a
synchronizing state (`sy_of_blocking`), so a lane whose last event blocks is at its warp
collective right after a synchronizing state, the one before the warp collective's.

Two lanes of a warp at their `n`-th warp collective are at one synchronizing ordinal `N`
(`cnt_gt_of_ord`), so their synchronizing states of ordinal `N - 1` are at one position (the
lockstep, `lock_kernel`), and the events fired there are of one instruction: the same register
request, the same barrier id, both allocator operations or neither (`isRes_pc`). The lanes have
made as many register requests, warp-collective `tcgen05` events and events on that barrier before
them (`lock_count`, with the classes `reqClass`, `isTcColl_state`, `barIdClass`). So the event of
a lane whose last event blocks (`syncOf`) is made by every lane at the same warp collective, and
it is the last event of every lane whose last event blocks (`sync_lane`). `warpColl_last` is
`WarpCollFacts.last`, with the event chosen from such a lane, if there is one (`lastR`).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Progress.Wn
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof
open PTX.Kernels.InklingRelDecode.Proof.Interface PTX.Kernels.InklingRelDecode.Proof.Progress
open PTX.Kernels.InklingRelDecode.Proof.Interface.Lk
open PTX.Kernels.InklingRelDecode.Proof.Progress.Lk4
open PTX.Kernels.InklingRelDecode.Proof.Lk (syOp syPcs syPc syAt kernel_syPcs)

noncomputable section
set_option maxRecDepth 100000

/-! ### Register-request states are synchronizing -/

/-- The instruction at a position is a register request. -/
def reqPc (pc : Nat) : Bool := (Ledger.reqAt pc).isSome

theorem syPc_of_req {pc : Nat} (h : reqPc pc = true) : syPc pc = true := by
  unfold reqPc Ledger.reqAt at h
  cases hc : kernel.code[pc]? with
  | none => rw [hc] at h; simp at h
  | some ins =>
    rw [hc] at h
    simp only at h
    have hs : syOp ins.op = true := by
      generalize ins.op = op at h ⊢
      cases op <;> simp_all [syOp]
    exact List.contains_iff_mem.mpr (OpPcsFast.mem kernel_syPcs hc hs)

theorem req_dstart_sub (s : DStart.Site) : reqPc s.pc = true → s.sub = 0 := by
  cases s <;> decide +kernel

theorem req_pro_nat : ∀ n < 182, reqPc (ProA.Site.ofNat n).pc = true →
    (ProA.Site.ofNat n).sub = 0 := by
  decide +kernel

theorem req_loader_sub (s : Loader.Site) : reqPc s.pc = true → (match s with
    | .ld1 => 1 | _ => 0) = 0 := by
  cases s <;> decide +kernel

/-- The state is not the common start's hand-off site, which is never a state of a trace (the
step into it is the prologue's first state, `DComp.Inv`). -/
def notHand : TSt → Bool
  | .d (.dstart d) => decide (d.site ≠ DStart.Site.toProA)
  | _ => true

/-- The state's instruction is a register request, and it is not the hand-off site. -/
def reqSt (s : TSt) : Bool := reqPc (TSt.pc s) && notHand s

/-- **A register-request state is synchronizing.** -/
theorem reqSt_sy {s : TSt} (h : reqSt s = true) : tSy s := by
  simp only [reqSt, Bool.and_eq_true] at h
  obtain ⟨hp, hn⟩ := h
  have hsy := syPc_of_req hp
  cases s with
  | d s =>
    cases s with
    | dstart d =>
      have h1 := req_dstart_sub d.site hp
      have h2 : d.site ≠ DStart.Site.toProA := by simpa [notHand] using hn
      simp only [tSy, PTX.Kernels.InklingRelDecode.Proof.Lk.dSy, Bool.and_eq_true,
        decide_eq_true_eq, PTX.Kernels.InklingRelDecode.Proof.Lk.dsSy, syAt]
      exact ⟨⟨hsy, by omega⟩, h2⟩
    | pro d =>
      have := req_pro_nat d.site.ctorIdx (PTX.Kernels.InklingRelDecode.Proof.Lk.ctorIdx_lt _)
        (by rw [PTX.Kernels.InklingRelDecode.Proof.Lk.ofNat_ctorIdx]; exact hp)
      rw [PTX.Kernels.InklingRelDecode.Proof.Lk.ofNat_ctorIdx] at this
      simp only [tSy, PTX.Kernels.InklingRelDecode.Proof.Lk.dSy,
        PTX.Kernels.InklingRelDecode.Proof.Lk.proSy, syAt, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨hsy, this⟩
    | sm d =>
      simp only [tSy, PTX.Kernels.InklingRelDecode.Proof.Lk.dSy,
        PTX.Kernels.InklingRelDecode.Proof.Lk.smSy, syAt, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨hsy, trivial⟩
    | epi d =>
      simp only [tSy, PTX.Kernels.InklingRelDecode.Proof.Lk.dSy,
        PTX.Kernels.InklingRelDecode.Proof.Lk.epSy, syAt, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨hsy, trivial⟩
  | w s =>
    simp only [tSy, PTX.Kernels.InklingRelDecode.Proof.Lk.wSy, syAt, Bool.or_eq_true,
      Bool.and_eq_true, decide_eq_true_eq]
    left
    refine ⟨hsy, ?_⟩
    cases s with
    | loader d P =>
      have := req_loader_sub d.site hp
      simp only [WComp.sub, Loader.sub]
      cases hs : d.site <;> simp_all
    | _ => rfl

theorem tReq_isSome (s : TSt) : (tReq s).isSome = reqPc (TSt.pc s) := by
  rw [reqPc, (t_static s).1]

/-! ### The classes of the events on one barrier and of the allocator operations -/

/-- The barrier id of the instruction at a position. -/
def barIdOf (pc : Nat) : Nat :=
  match kernel.code[pc]? with
  | some ins => (barIdCnt ins).1
  | none => 0

/-- The state's instruction is a named barrier with id `id`. -/
def barIdSt (id : Nat) (s : TSt) : Bool := barSt s && (barIdOf (TSt.pc s) == id)

/-- The instruction at a position is an allocator operation. -/
def resPc (pc : Nat) : Bool :=
  match kernel.code[pc]? with
  | some ins => tmemOp ins.op
  | none => false

/-- A `tcgen05` kind is an allocator operation. -/
def isRes : TcKind → Bool
  | .resource .. => true
  | _ => false

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- A state at which an event is fired is not the hand-off site. -/
theorem notHand_of_event (hS : ∀ g < L.threads, (threadCode L g Q).Sound)
    (hX : Consistent L kernel asms mem0 X) {g k : Nat} {e : Event} {s : TSt}
    (he : X.get (g, k) = some e) (hσ : St Q L X g k = some (some s)) : notHand s = true := by
  obtain ⟨t, ins, o, -, hinv, -⟩ := Frame.fired_site hS hX he hσ
  cases s with
  | d s =>
    cases s with
    | dstart d => simpa [notHand] using hinv.2.2
    | _ => rfl
  | w s => rfl

/-- A blocking `tcgen05` event is a warp collective. -/
theorem tcColl_of_blocking {pc : Nat} {t : TcKind} (h : ¬ Sched.Unblocking (.tc t)) :
    isTcColl ⟨pc, .tc t⟩ = true := by
  cases t <;> simp_all [Sched.Unblocking, isTcColl]

/-- **A warp-collective `tcgen05` event is an allocator operation exactly when its instruction
is one.** -/
theorem isRes_pc (hX : Consistent L kernel asms mem0 X) {i : EvId} {pc : Nat} {t : TcKind}
    (he : X.get i = some ⟨pc, .tc t⟩) (hc : isTcColl ⟨pc, .tc t⟩ = true) :
    isRes t = resPc pc := by
  rcases Flow.get_source hX he with ⟨f, hf⟩ | ⟨t0, ins, o, -, hcode, hf⟩
  · cases hf
  · simp only at hcode hf
    unfold resPc
    rw [hcode]
    cases t with
    | resource grp dst act =>
      exact (fires_resource_op hf (show (⟨pc, .tc (.resource grp dst act)⟩ : Event).kind = _
        from rfl)).symm
    | _ =>
      first
        | simp [isTcColl] at hc; done
        | have hd := fires_tcData_op hf (by simp [isTcData])
          simp only [isRes]
          revert hd
          cases ins.op <;> simp [tcDataOp, tmemOp]

section
variable (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
  (hf : ThreadFacts Q L mem0 X)
include hX hf

/-- **The register requests are the class of the register-request states.** -/
theorem reqClass : ClassEv SetMaxNReg.isRequest reqSt Q L X := by
  intro g k e s _ he hσ
  rw [reqSt, notHand_of_event hf.sound hX he hσ, Bool.and_true, ← tReq_isSome]
  exact Bool.eq_iff_iff.mpr (event_req hX hf.sound he hσ).1

include hpre in
/-- **The events on barrier `id` are the class of the states at a barrier with that id.** -/
theorem barIdClass (id : Nat) : ClassEv (Execution.isBarId id) (barIdSt id) Q L X := by
  intro g k e s _ he hσ
  have hb : L.block ≠ 128 := by have := hpre.block; omega
  have h1 := isBar_state hX hf.sound hb he hσ
  obtain ⟨pc, kd⟩ := e
  have hpc := Frame.event_pc hf.sound hX he hσ
  simp only at hpc
  cases kd with
  | bar i c m =>
    have hbs : barSt s = true := by rw [← h1]; rfl
    obtain ⟨ins, hc, hic⟩ := bar_event_idcnt hX hb he
    have hid : barIdOf (TSt.pc s) = i := by
      unfold barIdOf
      rw [← hpc, hc]
      simp only
      rw [← hic]
    simp [barIdSt, hbs, hid, Execution.isBarId]
  | _ =>
    have hbs : barSt s = false := by rw [← h1]; rfl
    simp [barIdSt, hbs, Execution.isBarId]

omit hX hf in
theorem barIdSt_sy {id : Nat} {s : TSt} (h : barIdSt id s = true) : tSy s := by
  simp only [barIdSt, Bool.and_eq_true] at h
  exact barSt_sy h.1

omit hX hf in
/-- Two synchronizing states of one key are at one position. -/
theorem key_pc {g h : Nat} {s s' : TSt} (hs : (kernelSkel Q L).sy s)
    (hs' : (kernelSkel Q L).sy s') (hk : (kernelSkel Q L).key g s = (kernelSkel Q L).key h s') :
    TSt.pc s = TSt.pc s' := by
  rw [← (kernelSkel Q L).pc_key (g := g) hs, ← (kernelSkel Q L).pc_key (g := h) hs', hk]

omit hX hf in
/-- A synchronizing state is not the hand-off site. -/
theorem notHand_sy {s : TSt} (hs : (kernelSkel Q L).sy s) : notHand s = true := by
  cases s with
  | d s =>
    cases s with
    | dstart d =>
      change PTX.Kernels.InklingRelDecode.Proof.Lk.dSy (.dstart d) = true at hs
      simp only [PTX.Kernels.InklingRelDecode.Proof.Lk.dSy, Bool.and_eq_true] at hs
      simpa [notHand] using hs.2
    | _ => rfl
  | w s => rfl

include hpre in
/-- **A blocking event is fired from a synchronizing state.** -/
theorem sy_of_blocking {g k : Nat} {e : Event} {s : TSt} (hg : g < L.threads)
    (he : X.get (g, k) = some e) (hσ : St Q L X g k = some (some s))
    (hu : ¬ Sched.Unblocking e.kind) : tSy s := by
  have hb : L.block ≠ 128 := by have := hpre.block; omega
  obtain ⟨pc, kd⟩ := e
  cases kd with
  | setMaxReg inc n inst =>
    apply reqSt_sy
    rw [reqSt, notHand_of_event hf.sound hX he hσ, Bool.and_true, ← tReq_isSome]
    exact (event_req hX hf.sound he hσ).1.mp (by simp [SetMaxNReg.isRequest])
  | bar id c m =>
    apply barSt_sy
    rw [← isBar_state hX hf.sound hb he hσ]
    rfl
  | tc t =>
    apply tcSt_sy
    rw [← isTcColl_state hpre hX hf hg he hσ]
    exact tcColl_of_blocking hu
  | cluster op => exact absurd he (Safety.no_cluster hX)
  | bulkWait md n => exact absurd he (no_bulkWait hX)
  | asyncWait n => exact absurd he (no_asyncWait hX)
  | _ => exact absurd trivial hu

end

/-! ### The synchronizing event of a blocking event -/

/-- The synchronizing event that event `j` of thread `g` is, if it blocks. -/
def syncOf (X : Execution) (g j : Nat) : Option SyncEv :=
  match X.get (g, j) with
  | some ⟨pc, .setMaxReg inc n _⟩ => some (.reg pc inc n (SetMaxNReg.ordinal X (g, j)))
  | some ⟨_, .tc t⟩ => some (.tc (isRes t) (cnt isTcColl X g j))
  | some ⟨_, .bar id _ _⟩ => some (.bar id (cnt (Execution.isBarId id) X g j))
  | _ => none

section
variable (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
  (hf : ThreadFacts Q L mem0 X)
include hpre hX hf

/-- **A blocking event is its synchronizing event.** -/
theorem sync_self {g j : Nat} {e : Event} (hg : g < L.threads) (he : X.get (g, j) = some e)
    (hu : ¬ Sched.Unblocking e.kind) : ∃ x, syncOf X g j = some x ∧ SyncAt X g j x := by
  obtain ⟨pc, kd⟩ := e
  cases kd with
  | setMaxReg inc n inst =>
    exact ⟨.reg pc inc n (SetMaxNReg.ordinal X (g, j)), by simp [syncOf, he], inst, he, rfl⟩
  | bar id c m =>
    cases m with
    | sync =>
      exact ⟨.bar id (cnt (Execution.isBarId id) X g j), by simp [syncOf, he], c, pc, he, rfl⟩
    | arrive =>
      exact (Consistent.noBarArrive Safety.kernel_noBarArrive hX (g, j) pc id c he).elim
  | tc t =>
    have hc : isTcColl ⟨pc, .tc t⟩ = true := tcColl_of_blocking hu
    refine ⟨.tc (isRes t) (cnt isTcColl X g j), by simp [syncOf, he], ⟨⟨_, he, hc⟩, rfl⟩, ?_, ?_⟩
    · intro pc' dst act h
      rw [he] at h
      simp only [Option.some.injEq, Event.mk.injEq, Kind.tc.injEq] at h
      obtain ⟨-, rfl⟩ := h
      have := (res_event hpre hX hf hg he).2.1
      cases this
    · constructor
      · rintro ⟨pc', grp, dst, act, h⟩
        rw [he] at h
        simp only [Option.some.injEq, Event.mk.injEq, Kind.tc.injEq] at h
        obtain ⟨-, rfl⟩ := h
        rfl
      · intro h
        cases t <;> simp_all [isRes]
  | cluster op => exact absurd he (Safety.no_cluster hX)
  | bulkWait md n => exact absurd he (no_bulkWait hX)
  | asyncWait n => exact absurd he (no_asyncWait hX)
  | _ => exact absurd trivial hu

/-- **A lane at a synchronizing state of the ordinal of another lane's blocking synchronizing
event `x` makes `x` there**: the states are at one position (`lock_kernel`, `key_pc`), so of one
instruction, and the lanes have made as many register requests, `tcgen05` collectives and events
on the barrier before them (`lock_count`). -/
theorem made_of_ord (hA : LaneAgree Q L X) {g g' a b : Nat} {sa s' : TSt} (hw : SameWarp L g g')
    (ha : a < (X.tr g).length) (hbl : b < (X.tr g').length)
    (hsa : St Q L X g a = some (some sa)) (hs'' : St Q L X g' b = some (some s'))
    (hsya : (kernelSkel Q L).sy sa) (hsy' : tSy s')
    (hna : syN (kernelSkel Q L) X g a = syN (kernelSkel Q L) X g' b)
    {e' : Event} (he' : X.get (g', b) = some e') (hu' : ¬ Sched.Unblocking e'.kind) {x : SyncEv}
    (hx : syncOf X g' b = some x) : SyncAt X g a x := by
  have hg : g < L.threads := hw.1.1
  have hg' : g' < L.threads := hw.1.2.1
  have hb : L.block ≠ 128 := by have := hpre.block; omega
  have ht := hf.tracked
  have hS := hf.sound
  have hL := lock_kernel ht hA
  have hkey := hL _ (sameWarp_symm (sameWarp_symm hw)) ha.le hbl.le hsa hs'' hsya
    hsy' hna rfl
  have hpc := key_pc hsya hsy' hkey
  obtain ⟨ea, hea⟩ : ∃ ea, X.get (g, a) = some ea := ⟨_, List.getElem?_eq_getElem ha⟩
  have hpca := Frame.event_pc hS hX hea hsa
  have hpc' := Frame.event_pc hS hX he' hs''
  simp only at hpca hpc'
  have hcount : ∀ {c : Event → Bool} {Cs : TSt → Bool}, ClassEv c Cs Q L X →
      (∀ {s}, Cs s = true → tSy s) →
      (∀ {g h : Nat} {s s' : TSt}, SameWarp L g h → (kernelSkel Q L).sy s →
        (kernelSkel Q L).sy s' → (kernelSkel Q L).key g s = (kernelSkel Q L).key h s' →
        Cs s = Cs s') → cnt c X g a = cnt c X g' (b) :=
    fun hev hcs hcls => lock_count (kernelSkel Q L) ht hL hev hcs hcls _ hw ha.le
      hbl.le hsa hs'' hsya hsy' hna rfl
  obtain ⟨pc', kd'⟩ := e'
  cases kd' with
  | setMaxReg inc n inst =>
    simp only [syncOf, he', Option.some.injEq] at hx
    subst hx
    have hr' := (event_req hX hS he' hs'').2 _ _ _ _ rfl
    have hra : tReq sa = some (inc, n) := by
      rw [← hr', ← (t_static sa).1, ← (t_static s').1, hpc]
    have hreq : SetMaxNReg.isRequest ea = true :=
      (event_req hX hS hea hsa).1.mpr (by rw [hra]; rfl)
    obtain ⟨pca, kda⟩ := ea
    cases kda <;> simp only [SetMaxNReg.isRequest, Bool.false_eq_true] at hreq
    rename_i ia na insta
    have := (event_req hX hS hea hsa).2 _ _ _ _ rfl
    rw [hra] at this
    simp only [Option.some.injEq, Prod.mk.injEq] at this
    obtain ⟨rfl, rfl⟩ := this
    have hpe : pca = pc' := by simp only at hpca hpc'; rw [hpca, hpc, ← hpc']
    subst hpe
    refine ⟨insta, hea, ?_⟩
    exact hcount (reqClass hX hf) (fun h => reqSt_sy h)
      (fun {g h s s'} _ hs hs' hk => by
        rw [reqSt, reqSt, key_pc hs hs' hk, notHand_sy hs, notHand_sy hs'])
  | tc t =>
    simp only [syncOf, he', Option.some.injEq] at hx
    subst hx
    have hc1 : isTcColl ⟨pc', .tc t⟩ = true := tcColl_of_blocking hu'
    have htc' : tcSt s' = true := by
      rw [← isTcColl_state hpre hX hf hg' he' hs'']; exact hc1
    have htca : tcSt sa = true := by
      rw [tcKey_class (sameWarp_symm (sameWarp_symm hw)) hsya hsy' hkey]; exact htc'
    have hca : isTcColl ea = true := by rw [isTcColl_state hpre hX hf hg hea hsa]; exact htca
    obtain ⟨pca, kda⟩ := ea
    obtain ⟨ta, rfl⟩ : ∃ ta, kda = .tc ta := by
      cases kda <;> simp [isTcColl] at hca ⊢
    have hpe : pca = pc' := by simp only at hpca hpc'; rw [hpca, hpc, ← hpc']
    subst hpe
    obtain ⟨y, hy, hsy⟩ := sync_self hpre hX hf hg hea (fun h => by
      cases ta <;> simp_all [Sched.Unblocking, isTcColl])
    simp only [syncOf, hea, Option.some.injEq] at hy
    subst hy
    obtain ⟨-, htwo, hres⟩ := hsy
    have hrr : isRes ta = isRes t := (isRes_pc hX hea hca).trans (isRes_pc hX he' hc1).symm
    refine ⟨⟨⟨_, hea, hca⟩, ?_⟩, htwo, ?_⟩
    · exact hcount (fun hg he hσ => isTcColl_state hpre hX hf hg he hσ) (fun h => tcSt_sy h)
        tcKey_class
    · rw [← hrr]
      exact hres
  | bar id c m =>
    simp only [syncOf, he', Option.some.injEq] at hx
    subst hx
    have hbs' : barSt s' = true := by rw [← isBar_state hX hS hb he' hs'']; rfl
    have hbsa : barSt sa = true := by
      rw [barKey_class (sameWarp_symm (sameWarp_symm hw)) hsya hsy' hkey]; exact hbs'
    have hba : Execution.isBar ea = true := by rw [isBar_state hX hS hb hea hsa]; exact hbsa
    obtain ⟨pca, kda⟩ := ea
    cases kda <;> simp only [Execution.isBar, Bool.false_eq_true] at hba
    rename_i ida ca ma
    have hpe : pca = pc' := by simp only at hpca hpc'; rw [hpca, hpc, ← hpc']
    subst hpe
    obtain ⟨ins, hcode, hic⟩ := bar_event_idcnt hX hb hea
    obtain ⟨ins', hcode', hic'⟩ := bar_event_idcnt hX hb he'
    rw [hcode] at hcode'
    obtain rfl := Option.some.inj hcode'
    have hid : ida = id := by
      have := hic.trans hic'.symm
      simp only [Prod.mk.injEq] at this
      exact this.1
    subst hid
    cases ma with
    | arrive =>
      exact (Consistent.noBarArrive Safety.kernel_noBarArrive hX (g, a) _ _ _ hea).elim
    | sync =>
      refine ⟨ca, pca, hea, ?_⟩
      exact hcount (barIdClass hpre hX hf ida) (fun h => barIdSt_sy h)
        (fun {g h s s'} _ hs hs' hk => by simp only [barIdSt, barSt, key_pc hs hs' hk])
  | cluster op => exact absurd he' (Safety.no_cluster hX)
  | bulkWait md n => exact absurd he' (no_bulkWait hX)
  | asyncWait n => exact absurd he' (no_asyncWait hX)
  | _ => exact absurd trivial hu'

/-- **A lane at the warp collective of a lane whose last event blocks has made that event, and its
own last event is that event or does not block.** -/
theorem sync_lane (hA : LaneAgree Q L X) {g g' : Nat} {d d' : TSt} (hw : SameWarp L g g')
    (hσ : St Q L X g (X.tr g).length = some (some d)) (hk : nextKind d = .warp)
    (hσ' : St Q L X g' (X.tr g').length = some (some d')) (hk' : nextKind d' = .warp)
    (hn : (X.tr g).countP Sched.isWarpColl = (X.tr g').countP Sched.isWarpColl)
    {e' : Event} (he' : X.get (g', (X.tr g').length - 1) = some e')
    (hu' : ¬ Sched.Unblocking e'.kind) {x : SyncEv}
    (hx : syncOf X g' ((X.tr g').length - 1) = some x) :
    (∃ j, j < (X.tr g).length ∧ SyncAt X g j x) ∧
      (LastFree X g ∨ SyncAt X g ((X.tr g).length - 1) x) := by
  have hg : g < L.threads := hw.1.1
  have hg' : g' < L.threads := hw.1.2.1
  have hb : L.block ≠ 128 := by have := hpre.block; omega
  have hc : wcSt d = true := (nextKind_warp d).mp hk
  have hc' : wcSt d' = true := (nextKind_warp d').mp hk'
  have ht := hf.tracked
  have hS := hf.sound
  have hL := lock_kernel ht hA
  -- one synchronizing ordinal
  have e1 : cnt Sched.isWarpColl X g (X.tr g).length = (X.tr g).countP Sched.isWarpColl := by
    simp [cnt]
  have e2 : cnt Sched.isWarpColl X g' (X.tr g').length = (X.tr g').countP Sched.isWarpColl := by
    simp [cnt]
  have hN : syN (kernelSkel Q L) X g (X.tr g).length =
      syN (kernelSkel Q L) X g' (X.tr g').length := by
    rcases Nat.lt_trichotomy (syN (kernelSkel Q L) X g (X.tr g).length)
      (syN (kernelSkel Q L) X g' (X.tr g').length) with hlt | heq | hgt
    · have := cnt_gt_of_ord hX hf hA hw le_rfl le_rfl hσ hc hlt
      omega
    · exact heq
    · have := cnt_gt_of_ord hX hf hA (sameWarp_symm hw) le_rfl le_rfl hσ' hc' hgt
      omega
  -- the last state of `g'` is synchronizing
  have hlen' : 0 < (X.tr g').length := by
    have := len_of_get he'
    simp only at this
    omega
  obtain ⟨s', hs'⟩ := Frame.stateAt_live (C := code L Q) ht hg' hσ'
    (Nat.sub_le (X.tr g').length 1)
  have hs'' : St Q L X g' ((X.tr g').length - 1) = some (some s') := hs'
  have hsy' : tSy s' := sy_of_blocking hpre hX hf hg' he' hs'' hu'
  have hN' : syN (kernelSkel Q L) X g' (X.tr g').length =
      syN (kernelSkel Q L) X g' ((X.tr g').length - 1) + 1 := by
    have := syN_succ (kernelSkel Q L) (X := X) g' ((X.tr g').length - 1)
    rw [Nat.sub_add_cancel hlen'] at this
    have hi : IsSy (kernelSkel Q L) X g' ((X.tr g').length - 1) := ⟨s', hs'', hsy'⟩
    simp only [this, hi, ↓reduceIte]
  -- `g`'s synchronizing state of that ordinal
  obtain ⟨a, ha, hsa, hna, hno⟩ := exists_prev (kernelSkel Q L) (X := X) g
    ⟨d, hσ, wcSt_sy hc⟩ (n := syN (kernelSkel Q L) X g' ((X.tr g').length - 1)) (by omega)
  obtain ⟨sa, hsa, hsya⟩ := hsa
  have hat : SyncAt X g a x :=
    made_of_ord hpre hX hf hA hw ha (by omega) hsa hs'' hsya hsy' hna he' hu' hx
  refine ⟨⟨a, ha, hat⟩, ?_⟩
  by_cases hfree : LastFree X g
  · exact .inl hfree
  · right
    unfold LastFree at hfree
    push Not at hfree
    obtain ⟨q, hq, hqu⟩ := hfree
    have hlen : 0 < (X.tr g).length := by
      have := len_of_get hq
      simp only at this
      omega
    obtain ⟨sl, hsl⟩ := Frame.stateAt_live (C := code L Q) ht hg hσ
      (Nat.sub_le (X.tr g).length 1)
    have hsl' : St Q L X g ((X.tr g).length - 1) = some (some sl) := hsl
    have hsyl := sy_of_blocking hpre hX hf hg hq hsl' hqu
    have hal : a = (X.tr g).length - 1 := by
      by_contra hne
      exact hno _ (by omega) (by omega) ⟨sl, hsl', hsyl⟩
    rw [← hal]
    exact hat

end

/-! ### `WarpCollFacts.last` -/

open Classical in
/-- The synchronizing event of the warp `key` at its `n`-th warp collective: that of the last
event of a lane at it whose last event blocks, if there is one. -/
def lastR (Q : Params) (L : Launch) (X : Execution) (key : Nat × Nat) (n : Nat) :
    Option SyncEv :=
  if h : ∃ g d, g < L.threads ∧ warpKey L g = key ∧
      St Q L X g (X.tr g).length = some (some d) ∧ nextKind d = .warp ∧
      (X.tr g).countP Sched.isWarpColl = n ∧ ¬ LastFree X g
  then syncOf X h.choose ((X.tr h.choose).length - 1) else none

/-- **`WarpCollFacts.last`**, with `R = lastR`. -/
theorem warpColl_last (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hA : LaneAgree Q L X) :
    ∃ R : Nat × Nat → Nat → Option SyncEv,
    ∀ {g : Nat} {d : TSt}, g < L.threads → St Q L X g (X.tr g).length = some (some d) →
      nextKind d = .warp →
      match R (warpKey L g) ((X.tr g).countP Sched.isWarpColl) with
      | none => LastFree X g
      | some x => (∃ j, j < (X.tr g).length ∧ SyncAt X g j x) ∧
        (LastFree X g ∨ SyncAt X g ((X.tr g).length - 1) x) := by
  refine ⟨lastR Q L X, ?_⟩
  intro g d hg hσ hk
  by_cases hex : ∃ g' d', g' < L.threads ∧ warpKey L g' = warpKey L g ∧
      St Q L X g' (X.tr g').length = some (some d') ∧ nextKind d' = .warp ∧
      (X.tr g').countP Sched.isWarpColl = (X.tr g).countP Sched.isWarpColl ∧ ¬ LastFree X g'
  · have hR : lastR Q L X (warpKey L g) ((X.tr g).countP Sched.isWarpColl) =
        syncOf X hex.choose ((X.tr hex.choose).length - 1) := by
      unfold lastR
      rw [dite_eq_left_of_eq_true (eq_true hex)]
    obtain ⟨d', hg', hkey, hσ', hk', hn', hnf⟩ := hex.choose_spec
    obtain ⟨e', he', hu'⟩ : ∃ e', X.get (hex.choose, (X.tr hex.choose).length - 1) = some e' ∧
        ¬ Sched.Unblocking e'.kind := by
      by_contra hc
      exact hnf fun q hq => by
        by_contra hu
        exact hc ⟨q, hq, hu⟩
    obtain ⟨x, hx, -⟩ := sync_self hpre hX hf hg' he' hu'
    rw [hR, hx]
    exact sync_lane hpre hX hf hA (sameWarp_of_key hg hg' hkey.symm) hσ hk hσ' hk' hn'.symm
      he' hu' hx
  · have hR : lastR Q L X (warpKey L g) ((X.tr g).countP Sched.isWarpColl) = none := by
      unfold lastR
      rw [dite_eq_right_of_eq_false (eq_false hex)]
    rw [hR]
    by_contra hnf
    exact hex ⟨g, d, hg, rfl, hσ, hk, rfl, hnf⟩

end
end PTX.Kernels.InklingRelDecode.Proof.Progress.Wn
