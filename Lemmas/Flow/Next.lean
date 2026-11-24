-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Execution.EventFrameSource
public import Lemmas.Execution.EventFrame
public import Lemmas.Isa.Tmpl

@[expose] public section

/-! # The thread state after an event

A proof tool. For most event instructions the thread continues in `next t` whatever the
event's operands evaluate to; an mbarrier poll continues in `next t` with its predicate
set to the observed outcome. These are the facts a site machine needs to evaluate the
local code after an event (`Flow.Code.StepAt.step`). -/

namespace PTX.Flow
open PTX PTX.EventFrame

noncomputable section

/-- Instructions whose only continuation is the next instruction. A `cp.async.bulk` copy with
`.multicast::cluster` copies to one destination CTA per sub-step (`bulkMulticast`) and is no such
instruction. -/
def AdvancesOp : Op → Prop
  | .mbarInit .. | .fence .. | .fenceMbarInit | .cluster .. | .setMaxReg .. => True
  | .cpBulk c => c.multicast = none
  | .cpTensor _ _ _ _ _ _ _ _ none _ _ => True
  | .warp ⟨.barWarp, _, _, _, _⟩ => True
  | .mbarArrive _ _ _ _ _ _ _ none => True
  | _ => False

private theorem ofExec_next {t : TState} {r : Exec Tmpl}
    (h : AllOk (CallbackFrame (· = next t)) r) : CallbackFrame (· = next t) (ofExec r) :=
  ofExec_frame h

theorem tmaTmpl_next {L : Launch} {g : Nat} {t : TState} {op : Op} (h : AdvancesOp op) :
    CallbackFrame (· = next t) (tmaTmpl L g t op) := by
  cases op
  case warp w => exact True.intro
  case cpBulk c =>
    simp only [AdvancesOp] at h
    simp only [tmaTmpl, bulkCopyTmpl, h]
    apply ofExec_next
    repeat' first
      | rfl
      | exact True.intro
      | (apply allOk_bind; intro v)
      | (split; try simp_all)
  all_goals (try (revert h; cases ‹Option Nat› <;> intro h))
  all_goals simp only [AdvancesOp] at h
  all_goals simp only [tmaTmpl]
  all_goals first | rfl | exact True.intro | apply ofExec_next
  all_goals repeat' first
    | rfl
    | exact True.intro
    | (apply allOk_bind; intro v)
    | split

/-- A fence event continues in `next t`, or faults. -/
theorem fenceTmpl_next {L : Launch} {g : Nat} {t : TState} {f : FenceInstr} :
    CallbackFrame (· = next t) (fenceTmpl L g t (.fence f)) := by
  cases f with
  | thread sem scope => rfl
  | proxy k order addr =>
    cases addr with
    | none => rfl
    | some a =>
      simp only [fenceTmpl]
      repeat' split
      all_goals first | rfl | exact True.intro

theorem tensorTmpl_next {L : Launch} {g : Nat} {t : TState} {ca grp : Bool} {dst mb : Nat}
    {off moff : Int} {map : Opnd} {cs : List Opnd} {lm : TensorMode} {policy : Option Opnd} :
    CallbackFrame (· = next t)
      (tensorTmpl L g t (.cpTensor ca grp dst off map cs mb moff none lm policy)) := by
  simp only [tensorTmpl]
  apply ofExec_next
  repeat' first
    | rfl
    | exact True.intro
    | (apply allOk_bind; intro v)
    | split

theorem widen_next {A : List Assumption} {P : TState → Prop} {site : Nat} {m : Tmpl}
    (h : CallbackFrame P m) : CallbackFrame P (widenMbarScope A site m) := by
  unfold widenMbarScope
  split
  · cases m
    all_goals try exact h
    case arrive m tx t count release scope => cases release <;> cases scope <;> exact h
    case wait m parity k acquire scope => cases acquire <;> cases scope <;> exact h
  · exact h

/-- After an advancing instruction the thread is in `next t`. -/
theorem fires_next {A : List Assumption} {L : Launch} {g : Nat} {t u : TState} {op : Op}
    {pc : Nat} {e : Event} (h : AdvancesOp op) (hf : Fires pc (eventTmpl A L g t op) e (some u)) :
    u = next t := by
  have hm : CallbackFrame (· = next t) (eventTmpl A L g t op) := by
    cases op
    case warp w =>
      rcases w with ⟨⟨⟩, _, _, _, _⟩ <;> simp only [AdvancesOp] at h
      simp only [eventTmpl, warpTmpl]
      split <;> (try unfold warpBarTmpl) <;> (repeat' split) <;> first | rfl | trivial
    all_goals (try (revert h; cases ‹Option Nat› <;> intro h))
    all_goals simp only [AdvancesOp] at h
    all_goals simp only [eventTmpl]
    case cpTensor mc _ _ =>
      cases mc with
      | none => exact tensorTmpl_next
      | some _ => exact h.elim
    case cluster => rfl
    case setMaxReg => unfold SetMaxNReg.tmpl; split <;> first | rfl | trivial
    case fence f => exact fenceTmpl_next
    case cpBulk c => exact widen_next (tmaTmpl_next (by simp only [AdvancesOp]; exact h))
    all_goals exact widen_next (tmaTmpl_next (by simp [AdvancesOp]))
  exact callbackFrame_fires (P := (· = next t)) hm hf

/-- After a poll the thread is in `next t` with its predicate holding the outcome, and the
event records that outcome. -/
theorem fires_wait {A : List Assumption} {L : Launch} {g : Nat} {t u : TState}
    {p base : Nat} {off : Int} {par : Opnd} {acq : Bool} {sc : MbarScope} {e : Event}
    (hf : Fires t.pc (eventTmpl A L g t (.mbarWait p base off par acq sc)) e (some u)) :
    ∃ m parity ok scope, e = ⟨t.pc, .wait m parity ok acq scope⟩ ∧
      u = next (setReg t p (.pred ok)) := by
  have hm : CallbackFrame (fun u => ∃ ok, u = next (setReg t p (.pred ok)))
      (eventTmpl A L g t (.mbarWait p base off par acq sc)) := by
    simp only [eventTmpl]
    apply widen_next
    simp only [tmaTmpl]
    apply ofExec_frame
    repeat' first
      | (intro ok; exact ⟨ok, rfl⟩)
      | (apply allOk_bind; intro v)
  obtain ⟨m, parity, ok, scope, he, -, hreg⟩ := mbarWait_fires hf
  obtain ⟨ok', rfl⟩ := callbackFrame_fires hm hf
  have hok : ok' = ok := by simpa [next, setReg] using hreg
  subst hok
  exact ⟨m, parity, ok', scope, he, rfl⟩

theorem loadTmpl_cases {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {sp : Space}
    {w : Nat} {ds : List Nat} {base : Nat} {off : Int} :
    (∃ f, loadTmpl A L g t sp false w ds base off = .ub f) ∨
      ∃ a, loadTmpl A L g t sp false w ds base off = .read a (afterLoad t ds) := by
  unfold loadTmpl
  split
  · exact .inl ⟨_, rfl⟩
  · exact .inr ⟨_, rfl⟩

/-- After a load without `.nc` and without extension the thread is in `afterLoad t a.regs bs` for
the bytes read. -/
theorem fires_load {A : List Assumption} {L : Launch} {g : Nat} {t u : TState} {a : MemAccess}
    {pc : Nat} {e : Event} (hk : a.kind = .load) (hnc : a.nc = false)
    (hf : Fires pc (eventTmpl A L g t (.mem a)) e (some u)) (he : a.ext = .same := by rfl) :
    ∃ r bs, e = ⟨pc, .rd r bs⟩ ∧ u = afterLoad t a.regs bs := by
  have hl : ∀ {sp base ds} {m : Tmpl}, (∀ r k, loadTmpl A L g t sp false a.elem.width ds base
      a.addr.off = .read r k → m = .read r k ∨ ∃ r', m = .read r' k) →
      (∀ f, loadTmpl A L g t sp false a.elem.width ds base a.addr.off = .ub f → m = .ub f) →
      Fires pc m e (some u) → ∃ r bs, e = ⟨pc, .rd r bs⟩ ∧ u = afterLoad t ds bs := by
    intro sp base ds m hr hu hf
    rcases loadTmpl_cases (A := A) (L := L) (g := g) (t := t) (sp := sp) (w := a.elem.width)
      (ds := ds) (base := base) (off := a.addr.off) with ⟨f, h⟩ | ⟨r, h⟩
    · rw [hu f h] at hf
      exact absurd hf.2 (by simp)
    · rcases hr r _ h with rfl | ⟨r', rfl⟩ <;>
        obtain ⟨bs, -, rfl, hu⟩ := hf <;> exact ⟨_, bs, rfl, Option.some.inj hu⟩
  have hacc : Fires pc (accessTmpl A L g t a) e (some u) → ∃ r bs, e = ⟨pc, .rd r bs⟩ ∧
      u = afterLoad t a.regs bs := by
    intro hf
    rcases accessTmpl_load (A := A) (L := L) (g := g) (t := t) hk with ⟨f, h⟩ | ⟨r, -, -, h⟩ |
      ⟨r, k, hn, -⟩
    · rw [h] at hf
      exact absurd hf.2 (by simp)
    · rw [h, he, afterAccessLoad_same] at hf
      obtain ⟨bs, -, rfl, hu⟩ := hf
      exact ⟨_, bs, rfl, Option.some.inj hu⟩
    · simp [hnc] at hn
  have hnotAtomic : a.rule ≠ some .threadAtomic := by
    rw [MemAccess.rule, hk]
    repeat' split
    all_goals simp_all
  simp only [eventTmpl, memTmpl] at hf
  split at hf
  · -- THREAD-ACCESS at a location the access names directly
    rename_i r sp? ab sp base w hr hloc hbase
    split at hf
    · -- an acquire load into one register: `loadTmpl` with the acquire flag
      rename_i k s ds srcs d hk' hsem hregs
      rw [hregs]
      refine hl (sp := sp) (base := base) (fun r k h => ?_) (fun f h => ?_) hf <;>
        simp only [acquireLoadTmpl, h]
      exact .inr ⟨_, rfl⟩
    · -- a weak load
      rename_i k s ds srcs hk' hsem
      rw [hnc] at hf
      exact hl (sp := sp) (base := base) (fun r k h => .inl h) (fun f h => h) hf
    · -- a release store: no load
      rename_i k s ds srcs v hk' hsem hsrcs
      exact absurd (hk.symm.trans hk') (by simp)
    · -- a weak store: no load
      rename_i k s ds srcs hk' hsem
      exact absurd (hk.symm.trans hk') (by simp)
    · -- no direct location rule for this access: `accessTmpl`
      rename_i k s ds srcs i1 i2 i3 i4
      exact hacc hf
  · -- THREAD-ATOMIC is the rule of an `.rmw` or `.reduce` access only
    rename_i r sp? ab hrule
    exact absurd hrule hnotAtomic
  · -- THREAD-ACCESS without a located space: `accessTmpl`, or no rule at all
    rename_i r sp? ab hnotAtomic hnotDirect
    split at hf
    · exact hacc hf
    · exact absurd hf.2 (by simp)

theorem clcQuery_cases {L : Launch} {g : Nat} {t : TState} {q : ClcQuery} {dst : Nat}
    {src : Opnd} :
    (∃ f, clcTmpl L g t (.clcQuery q dst src) = .ub f) ∨
      ∃ r v, readValue L g t 128 src = .ok (.clc r) ∧ clcQueryValue q r = .ok v ∧
        clcTmpl L g t (.clcQuery q dst src) = .clcQuery q r (next (setReg t dst v)) := by
  simp only [clcTmpl]
  cases hr : readValue L g t 128 src with
  | error f => exact .inl ⟨f, by simp [ofExec, bind, Except.bind]⟩
  | ok val =>
    cases val
    case clc r =>
      cases hq : clcQueryValue q r with
      | error f => exact .inl ⟨f, by simp [ofExec, bind, Except.bind, hq]⟩
      | ok v => exact .inr ⟨r, v, rfl, hq, by
        simp [ofExec, bind, Except.bind, hq, pure, Except.pure]⟩
    all_goals exact .inl ⟨.typeMismatch, by
      simp [ofExec, bind, Except.bind, throw, throwThe, MonadExceptOf.throw]⟩

/-- After a CLC query of a response register the thread holds the query's value. -/
theorem fires_clcQuery {A : List Assumption} {L : Launch} {g : Nat} {t u : TState}
    {q : ClcQuery} {dst : Nat} {src : Opnd} {pc : Nat} {e : Event}
    (hf : Fires pc (eventTmpl A L g t (.clcQuery q dst src)) e (some u)) :
    ∃ r v, readValue L g t 128 src = .ok (.clc r) ∧ clcQueryValue q r = .ok v ∧
      e = ⟨pc, .clcQuery q r⟩ ∧ u = next (setReg t dst v) := by
  simp only [eventTmpl] at hf
  rcases clcQuery_cases (L := L) (g := g) (t := t) (q := q) (dst := dst) (src := src) with
    ⟨f, hc⟩ | ⟨r, v, hr, hq, hc⟩
  · rw [hc] at hf
    exact absurd hf.2 (by simp)
  · rw [hc] at hf
    obtain ⟨rfl, hu⟩ := hf
    exact ⟨r, v, hr, hq, rfl, Option.some.inj hu⟩

/-- After a shuffle the thread holds the received value and, if requested, the validity
predicate. -/
theorem fires_shfl {A : List Assumption} {L : Launch} {g : Nat} {t u : TState} {mode : ShflMode}
    {d : Nat} {p : Option Nat} {a b c mask : Opnd} {pc : Nat} {e : Event}
    {ty : Option DType}
    (hf : Fires pc (eventTmpl A L g t
      (.warp ⟨.shfl mode, ty, some d :: (p.map some).toList, [a, b, c], some mask⟩)) e
      (some u)) :
    ∃ av bv cv recv ok, e = ⟨pc, .shfl mode av bv cv recv ok⟩ ∧
      u = next (p.elim (setReg t d recv) fun p => setReg (setReg t d recv) p (.pred ok)) := by
  simp only [eventTmpl] at hf
  rcases warpTmpl_shfl (L := L) (g := g) (t := t) (mode := mode) (ty := ty) (d := d)
    (ps := (p.map some).toList) (a := a) (b := b) (c := c) (mask := mask) with h | h <;>
    rw [h] at hf
  swap
  · exact absurd hf.2 (by simp)
  have hp : (p.map some).toList.head?.join = p := by cases p <;> rfl
  rw [hp] at hf
  simp only [shflTmpl] at hf
  split at hf
  · split_ifs at hf
    · obtain ⟨recv, ok, rfl, hu⟩ := hf
      refine ⟨_, _, _, recv, ok, rfl, ?_⟩
      obtain rfl := Option.some.inj hu
      cases p <;> rfl
    all_goals simp [Fires] at hf
  all_goals simp [Fires] at hf

/-- After an election the thread's predicate says whether it is the leader. -/
theorem fires_elect {A : List Assumption} {L : Launch} {g : Nat} {t u : TState}
    {dst : Option Nat} {p : Nat} {mask : Opnd} {pc : Nat} {e : Event} {ty : Option DType}
    (hf : Fires pc (eventTmpl A L g t (.warp ⟨.elect, ty, [dst, some p], [], some mask⟩)) e
      (some u)) :
    ∃ mk inst leader, e = ⟨pc, .elect mk inst leader⟩ ∧
      u = next (setReg (dst.elim t fun d => setReg t d (.bits 32 (BitVec.ofNat 64 leader))) p
        (.pred (laneOf L g == leader))) := by
  simp only [eventTmpl, warpTmpl_elect, electTmpl] at hf
  split at hf
  · simp [Fires] at hf
  · split_ifs at hf
    · obtain ⟨inst, leader, rfl, hu⟩ := hf
      refine ⟨_, inst, leader, rfl, ?_⟩
      obtain rfl := Option.some.inj hu
      cases dst <;> rfl
    · simp [Fires] at hf

/-- An election's mask is the value its mask operand reads; an election that does not
continue is undefined behaviour. -/
theorem fires_elect_mask {A : List Assumption} {L : Launch} {g : Nat} {t : TState}
    {dst : Option Nat} {p : Nat} {mask : Opnd} {pc : Nat} {e : Event} {o : Option TState}
    {bits : BitVec 64} {ty : Option DType} (hm : readBits L g t 32 mask = .ok bits)
    (hf : Fires pc (eventTmpl A L g t (.warp ⟨.elect, ty, [dst, some p], [], some mask⟩)) e o) :
    (∃ inst leader, e = ⟨pc, .elect bits.toNat inst leader⟩) ∨ ∃ f, e = ⟨pc, .ub f⟩ := by
  simp only [eventTmpl, warpTmpl_elect, electTmpl, hm] at hf
  split_ifs at hf
  · obtain ⟨inst, leader, rfl, -⟩ := hf
    exact .inl ⟨inst, leader, rfl⟩
  · exact .inr ⟨_, hf.1⟩

end
end PTX.Flow
