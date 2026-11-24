-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.Polls
public import Lemmas.Flow.Regs
public import Lemmas.Flow.Events
public import Lemmas.Isa.Tmpl
public import Lemmas.Flow.Hooks

@[expose] public section

/-! # Undefined behaviour only after a stopped machine

A proof tool. An undefined-behaviour event fires only from a template that is undefined
behaviour (`fires_ub`). So in a sound code machine whose sites' templates never are
(`Code.TmplOk`), every undefined-behaviour event of a trace comes after the machine stopped: its
abstract state is `none` (a dead state) or `some none` (a state the machine does not follow)
(`Code.ub_stopped`). A site's template is not undefined behaviour as soon as no such event fires
from it (`not_ub_of_fires`), which the site's event lemmas give. -/

namespace PTX.Flow

open PTX PTX.Proof

noncomputable section

/-- An undefined-behaviour event fires only from that template. -/
theorem fires_ub {pc : Nat} {m : Tmpl} {e : Event} {o : Option TState} {f : Fault}
    (hf : Fires pc m e o) (he : e.kind = .ub f) : m = .ub f := by
  obtain ⟨epc, ek⟩ := e
  simp only at he
  subst he
  cases m <;> simp_all [Fires]

/-- A template from which no undefined-behaviour event fires is not undefined behaviour. -/
theorem not_ub_of_fires {pc : Nat} {m : Tmpl} (h : ∀ f, Fires pc m ⟨pc, .ub f⟩ none → False)
    (f : Fault) : m ≠ .ub f := by
  rintro rfl
  exact h f ⟨rfl, rfl⟩

/-- Instructions whose event is never undefined behaviour in a launch of whole warps: fences
without an address operand, cluster barrier operations, the return, the Tensor Memory waits and
fences, the relinquishment, the bulk-group commit and wait, and a register request of a valid
count. -/
def plainOk : Op → Bool
  | .fence (.proxy _ _ none) | .fenceMbarInit | .cluster _ | .ret | .tcRelinquish _ | .tcWaitLd
  | .tcWaitSt | .tcFenceBefore | .tcFenceAfter | .bulkCommit | .bulkWait _ _ => true
  | .setMaxReg _ n => SetMaxNReg.validCount n
  | _ => false

/-- The event of a plain instruction is not undefined behaviour. -/
theorem plainOk_tmpl {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {op : Op}
    (hb : L.block % 32 = 0) (h : plainOk op = true) (f : Fault) : eventTmpl A L g t op ≠ .ub f := by
  cases op
  case fence fi =>
    cases fi with
    | thread sem scope =>
      have hz : plainOk (.fence (.thread sem scope)) = false := rfl
      rw [hz] at h
      exact absurd h (by simp)
    | proxy k o a =>
      cases a with
      | none => simp [eventTmpl, fenceTmpl]
      | some x =>
        have hz : plainOk (.fence (.proxy k o (some x))) = false := rfl
        rw [hz] at h
        exact absurd h (by simp)
  all_goals simp only [plainOk, Bool.false_eq_true] at h
  all_goals
    simp [eventTmpl, tmaTmpl, widenMbarScope, tcTmpl, tensorStoreTmpl, SetMaxNReg.tmpl, ofExec,
      hb, h, pure, Except.pure]

/-- A response query is not undefined behaviour on a register holding a response that answers
it: any response the status query, a cancelling response the first-CTA query. -/
theorem query_ok {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {q : ClcQuery}
    {dst src : Nat} {r : ClcResponse} (hr : t.regs src = some (.clc r))
    (hq : q = .isCanceled ∨ r.firstCta.isSome) (f : Fault) :
    eventTmpl A L g t (.clcQuery q dst (.reg src)) ≠ .ub f := by
  simp only [eventTmpl, clcTmpl, readValue, readReg, hr, bind, Except.bind, pure, Except.pure]
  rcases hq with rfl | hs
  · simp [clcQueryValue, ofExec]
  · obtain ⟨⟨x, y, z⟩, h⟩ := Option.isSome_iff_exists.mp hs
    cases q <;> simp [clcQueryValue, ofExec, h, pure, Except.pure]

/-- A tile load of the CTA pair, multicast-addressed, whose map, destination, mbarrier and
coordinates evaluate, with a 128-aligned destination, an aligned box and the pair's route, is the
copy of the map's box at the coordinates' origin. -/
theorem cpTensor_tmpl {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {dst mb : Nat}
    {map : Opnd} {cs : List Opnd} {a outer : Nat} {desc : TensorDescriptor.Descriptor outer}
    {dl ml : Loc} {vs : List (BitVec 64)}
    (hm : tensorMap L g t map cs .tile = .ok (a, ⟨outer, desc⟩))
    (hd : sharedEffAddr L g t true dst 0 = .ok dl) (h128 : dl.addr % 128 = 0)
    (hmb : mbarClusterLoc L g t mb 0 = .ok ml) (hvs : cs.mapM (readBits L g t 32) = .ok vs)
    (hbox : TensorDescriptor.BoxAligned desc
      (fun axis => (BitVec.ofNat 32 (vs.getD axis.val 0).toNat).toInt))
    (hr : TensorRoute L (g / L.block) true .two dl ml) :
    eventTmpl A L g t (.cpTensor true true dst 0 map cs mb 0 none .tile) =
      .tensorIssue a ⟨⟨outer, desc, fun axis => (BitVec.ofNat 32 (vs.getD axis.val 0).toNat).toInt,
        dl, none⟩, ml, true, .two⟩ (next t) := by
  have hbox' : requireBoxAligned desc
      (fun axis => (BitVec.ofNat 32 (vs.getD axis.val 0).toNat).toInt) = .ok () :=
    (requireBoxAligned_eq_ok desc _).2 hbox
  have hcopy : tensorLoadCopy L g t true true dst 0 map cs mb 0 .tile =
      .ok (a, ⟨⟨outer, desc, fun axis => (BitVec.ofNat 32 (vs.getD axis.val 0).toNat).toInt,
        dl, none⟩, ml, true, .two⟩) := by
    simp only [tensorLoadCopy, bind, Except.bind, pure, Except.pure, hm, hd, hmb, hvs, hbox', h128,
      TensorMode.transfer, TensorMode.rowCoordinates, ↓reduceIte]
  simp only [eventTmpl, tensorTmpl, cachePolicyRead, ofExec, bind, Except.bind, pure, Except.pure,
    hcopy, hr, ↓reduceIte]

/-- Every lane is a member of the full mask. -/
theorem electMember_full {lane : Nat} (h : lane < 32) : electMember 4294967295 lane := by
  revert lane
  decide

/-- A full-mask election is not undefined behaviour. -/
theorem elect_ok {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {dst : Option Nat}
    {p r : Nat} {ty : Option DType} (hr : t.regs r = some (b32 4294967295)) (f : Fault) :
    eventTmpl A L g t (.warp ⟨.elect, ty, [dst, some p], [], some (.reg r)⟩) ≠ .ub f := by
  have hm := electMember_full (Nat.mod_lt (g % L.block) (show 0 < 32 by decide))
  simp only [eventTmpl, warpTmpl_elect, electTmpl, readBits, readReg, hr, b32, bind, Except.bind,
    pure, Except.pure]
  rw [show (truncBits 32 (BitVec.ofNat 64 4294967295)).toNat = 4294967295 by decide]
  simp [laneOf, hm]

/-- A full-mask warp barrier is not undefined behaviour. -/
theorem warpBar_ok {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {ty : Option DType}
    (f : Fault) :
    eventTmpl A L g t (.warp ⟨.barWarp, ty, [], [], some (.imm (-1))⟩) ≠ .ub f := by
  have hm := electMember_full (Nat.mod_lt (g % L.block) (show 0 < 32 by decide))
  simp only [eventTmpl, warpTmpl_barWarp, warpBarTmpl, readBits, pure, Except.pure]
  rw [show (truncBits 32 (BitVec.ofInt 64 (-1))).toNat = 4294967295 by decide]
  simp [laneOf, hm]

/-- A 32-bit integer register read as 32 bits. -/
theorem readBits_b32' {L : Launch} {g : Nat} {t : TState} {r : Nat} {x : Nat}
    (hr : t.regs r = some (b32 x)) :
    readBits L g t 32 (.reg r) = .ok (truncBits 32 (BitVec.ofNat 64 x)) := by
  simp [readBits, readReg, hr, b32, bind, Except.bind, pure, Except.pure]

/-- A Tensor Memory load of a supported address is not undefined behaviour. -/
theorem tcLd_ok {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {ds : List Nat}
    {ta : Nat} {a : Nat} {sh : TcShape} (hb : L.block % 32 = 0)
    (hn : sh.countOk ds.length = true)
    (hr : t.regs ta = some (b32 a)) (ha : a < 2 ^ 32) (hs : tcDataAddressOk L g sh a = true)
    (f : Fault) : eventTmpl A L g t (.tcLd ds ta sh) ≠ .ub f := by
  have h32 : a < 4294967296 := ha
  have h64 : a < 18446744073709551616 := by omega
  have h0 : tcTmpl L g t (.tcLd ds ta sh) ≠ .ub f := by
    cases sh with
    | packed16 s =>
      have hn' : s.countOk ds.length = true := hn
      simp [tcTmpl, hb, hn', readBits_b32' hr, truncBits, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt h32, Nat.mod_eq_of_lt h64, hs, ofExec, bind, Except.bind, pure,
        Except.pure]
    | _ =>
      simp [tcTmpl, hb, hn, readBits_b32' hr, truncBits, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt h32, Nat.mod_eq_of_lt h64, hs, ofExec, bind, Except.bind, pure,
        Except.pure]
  rcases eventTmpl_tcLd_cases (A := A) (L := L) (g := g) (t := t) (ds := ds) (ta := ta)
    (sh := sh) with h | h | h <;> rw [h]
  · exact h0
  · exact thenWaitLd_ne_ub h0
  · intro h; cases h

/-- A Tensor Memory deallocation of a valid column count is not undefined behaviour. -/
theorem tcDealloc_ok {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {grp : CtaGroup}
    {ra rn : Nat} {w : Nat} {x : BitVec 64} (hb : L.block % 32 = 0)
    (hra : t.regs ra = some (.bits w x)) (hrn : t.regs rn = some (b32 512)) (f : Fault) :
    eventTmpl A L g t (.tcDealloc grp (.reg ra) (.reg rn)) ≠ .ub f := by
  simp only [eventTmpl, tcTmpl, readBits, readReg, hra, hrn, b32, hb, bind, Except.bind, pure,
    Except.pure]
  rw [show (truncBits 32 (BitVec.ofNat 64 512)).toNat = 512 by decide]
  simp [Tmem.validColumns, ofExec]

/-- A shared load of a 4-aligned word is not undefined behaviour. -/
theorem ld_ok {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {d base : Nat}
    {a : Nat} {ik : IType} (hr : t.regs base = some (b32 a)) (ha : a < 2 ^ 32)
    (h4 : a % 4 = 0) (hsub : t.sub = 0) (f : Fault) :
    eventTmpl A L g t (.mem { kind := .load, space := some (.shared .cta), sem := .weak,
                              elem := .int ik 32, addr := ⟨.reg base 32, 0⟩,
                              dsts := [some d] }) ≠ .ub f := by
  have h32 : a < 4294967296 := ha
  have h64 : a < 18446744073709551616 := by omega
  rw [eventTmpl, memTmpl_load (sp := .shared) (base := base) (w := 32) (by cases ik <;> rfl)
    rfl rfl rfl (by simp)]
  simp [loadTmpl, MemAccess.regs, DType.width, effAddr, sharedEffAddr, readReg, hr, b32,
    readBits, truncBits, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h64, Nat.mod_eq_of_lt h32,
    elemAcc, h4, hsub, bind, Except.bind, pure, Except.pure]

/-- Element `t.sub` of a shared vector store of 32-bit words, at an aligned address, of a word
register, is not undefined behaviour. -/
theorem stv_ok {L : Launch} {g : Nat} {t : TState} {base : Nat} {srcs : List Opnd} {a : Nat}
    {r : Nat} {ik : IType} {v : Value} (hr : t.regs base = some (b32 a)) (ha : a < 2 ^ 32)
    (hn : srcs.length = 1 ∨ srcs.length = 2 ∨ srcs.length = 4)
    (hal : a % (4 * srcs.length) = 0) (hs : srcs[t.sub]? = some (.reg r))
    (hv : t.regs r = some v) (hb : v.bytes = 4) (f : Fault) {A : List Assumption} :
    eventTmpl A L g t (.mem { kind := .store, space := some (.shared .cta), sem := .weak,
                              elem := .int ik 32, vec := srcs.length,
                              addr := ⟨.reg base 32, 0⟩, srcs := srcs }) ≠ .ub f := by
  have h32 : a < 4294967296 := ha
  have h64 : a < 18446744073709551616 := by omega
  have hrule : MemAccess.rule { kind := .store, space := some (.shared .cta), sem := .weak,
                                elem := .int ik 32, vec := srcs.length,
                                addr := ⟨.reg base 32, 0⟩, srcs := srcs } =
      some .threadAccess := by
    rcases hn with h | h | h <;> cases ik <;> simp [MemAccess.rule,
      memTypeOk, DType.width, h]
  rw [eventTmpl, memTmpl_store (sp := .shared) (base := base) (w := 32) hrule rfl rfl rfl
    (by simp)]
  have hsv : storeValue 32 v = .ok v := storeValue_of_bytes (w := 32) (by simpa using hb)
  simp [storeTmpl, DType.width, effAddr, sharedEffAddr, readReg, hr, b32, readBits, truncBits,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt h64, Nat.mod_eq_of_lt h32, elemAcc, hal, hs, readValue,
    hv, hsv, bind, Except.bind, pure, Except.pure]

/-- A 32-bit coordinate below `2 ^ 31` is a nonnegative signed integer. -/
theorem toInt_nonneg {n : Nat} (h : n < 2 ^ 31) : 0 ≤ (BitVec.ofNat 32 n).toInt := by
  rw [BitVec.toInt_eq_toNat_cond]
  have : (BitVec.ofNat 32 n).toNat = n := by
    rw [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  rw [this]
  split_ifs <;> omega

/-- A tile store from a 128-aligned shared buffer, with nonnegative coordinates, an aligned box
and a defined cache policy, is the store of the map's box at the coordinates' origin. -/
theorem cpTensorStore_tmpl {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {src : Nat}
    {map p : Opnd} {cs : List Opnd} {a outer : Nat} {desc : TensorDescriptor.Descriptor outer}
    {sl : Loc} {vs : List (BitVec 64)} {x : BitVec 64}
    (hm : tensorMap L g t map cs .tile = .ok (a, ⟨outer, desc⟩))
    (hs : sharedEffAddr L g t false src 0 = .ok sl) (h128 : sl.addr % 128 = 0)
    (hvs : cs.mapM (readBits L g t 32) = .ok vs) (hnn : ∀ v ∈ vs, v.toNat < 2 ^ 31)
    (hbox : TensorDescriptor.BoxAligned desc
      (fun axis => (BitVec.ofNat 32 (vs.getD axis.val 0).toNat).toInt))
    (hp : readBits L g t 64 p = .ok x) :
    eventTmpl A L g t (.cpTensorStore map cs src 0 (some p) .tile none) =
      .tensorStore a ⟨⟨outer, desc, fun axis => (BitVec.ofNat 32 (vs.getD axis.val 0).toNat).toInt,
        sl, none⟩, none⟩ (next t) := by
  have hax : ∀ axis : Fin (outer + 1), 0 ≤ (BitVec.ofNat 32 (vs.getD axis.val 0).toNat).toInt := by
    intro axis
    apply toInt_nonneg
    rw [List.getD_eq_getElem?_getD]
    cases hv : vs[axis.val]? with
    | none => simp
    | some v => exact hnn v (List.mem_of_getElem? hv)
  have hbox' : requireBoxAligned desc
      (fun axis => (BitVec.ofNat 32 (vs.getD axis.val 0).toNat).toInt) = .ok () :=
    (requireBoxAligned_eq_ok desc _).2 hbox
  simp only [eventTmpl, tensorStoreTmpl, tensorStoreSpec, cachePolicyRead, hm, hs, hvs, hp, bind,
    Except.bind, pure, Except.pure, Option.all, h128, ↓reduceIte, hax, implies_true, true_or,
    hbox', TensorMode.transfer, TensorMode.rowCoordinates]
  simp [ofExec]

/-- A mbarrier initialization of a 8-aligned barrier of the thread's CTA, with a count in range,
is not undefined behaviour. -/
theorem mbarInit_ok {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {base c : Nat}
    {a n : Nat} (hr : t.regs base = some (b32 a)) (ha : a < 2 ^ 32) (h8 : a % 8 = 0)
    (hc : t.regs c = some (b32 n)) (hn : 0 < n) (hn' : n < 2 ^ 20) (f : Fault) :
    eventTmpl A L g t (.mbarInit base 0 (.reg c)) ≠ .ub f := by
  have h20 : n < 1048576 := hn'
  have h32 : n < 4294967296 := by omega
  have h64 : n < 18446744073709551616 := by omega
  simp [eventTmpl, tmaTmpl, mbarLoc_b32 hr ha h8, readBits_b32' hc, truncBits, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt h32, Nat.mod_eq_of_lt h64, hn, h20, ofExec, widenMbarScope, bind, Except.bind,
    pure, Except.pure]

/-- A Tensor Memory allocation of 512 columns, storing its address to a 4-aligned shared word, is
not undefined behaviour at its request (`sub = 0`) or its address store. -/
theorem tcAlloc_ok {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {grp : CtaGroup}
    {base nc : Nat} {a : Nat} (hb : L.block % 32 = 0) (hr : t.regs base = some (b32 a))
    (ha : a < 2 ^ 32) (h4 : a % 4 = 0) (hn : t.regs nc = some (b32 512)) (f : Fault) :
    eventTmpl A L g t (.tcAlloc grp base 0 (.reg nc)) ≠ .ub f := by
  have h32 : a < 4294967296 := ha
  have h64 : a < 18446744073709551616 := by omega
  simp only [eventTmpl, tcTmpl, effAddr_b32 hr ha, readBits_b32' hn, hb, bind, Except.bind,
    pure, Except.pure]
  rw [show (truncBits 32 (BitVec.ofNat 64 512)).toNat = 512 by decide]
  by_cases hs : t.sub = 0 <;> simp [Tmem.validColumns, h4, hs, ofExec]

/-- An event that a later event follows fires from the state reached before it, continuing in a
state. -/
theorem Machine.Trace.fired_some {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat}
    {M : Machine K A L g} {σ : M.St} {es : List Event} (h : M.Trace σ es) :
    ∀ {j : Nat} {e : Event}, es[j]? = some e → j + 1 < es.length →
      ∃ τ u, M.after σ (es.take j) = some τ ∧ M.Fired τ e (some u) := by
  induction h with
  | nil σ => intro j e hj; simp at hj
  | step hf hn _ ih =>
    intro j e hj hl
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
      subst hj
      exact ⟨_, _, rfl, hf⟩
    | succ j =>
      simp only [List.take_succ_cons, Machine.after_cons, hn, Option.bind_some]
      exact ih (by simpa using hj) (by simp at hl; omega)
  | last hf => intro j e hj hl; simp at hl
  | dead hf hn hlen _ =>
    intro j e hj hl
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
      subst hj
      exact ⟨_, _, rfl, hf⟩
    | succ j => simp at hl; omega

namespace Code

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat}

/-- No site of the machine has an undefined-behaviour template. -/
def TmplOk (C : Code K A L g) : Prop :=
  ∀ d t ins, C.AtD d t → C.inv d → K.code[C.pc d]? = some ins →
    ∀ f, eventTmpl A L g t ins.op ≠ .ub f

/-- **Undefined behaviour comes after a stop.** In a sound code machine without undefined-behaviour
templates, the abstract state before an undefined-behaviour event of a trace is not followed. -/
theorem ub_stopped {C : Code K A L g} (hC : C.Sound) (hok : C.TmplOk) {es : List Event}
    (hp : Produces K A L g es) {k pc : Nat} {f : Fault} (hk : es[k]? = some ⟨pc, .ub f⟩) :
    C.toMachine.after (some C.init) (es.take k) = none ∨
      C.toMachine.after (some C.init) (es.take k) = some none := by
  have htr := hC.machine.produces hp
  rcases htr.fired hk with ⟨τ, o, ha, hf⟩ | ⟨ha, -⟩
  · cases τ with
    | none => exact .inr ha
    | some d =>
      exfalso
      obtain ⟨t, ins, hat, hinv, hc, hfire⟩ := Code.fired_site hC hf
      exact hok d t ins hat hinv hc f (fires_ub hfire rfl)
  · exact .inl ha

/-- **Undefined behaviour comes after a stop**, given defined templates only at the state the trace
reaches before the undefined-behaviour event (promoted from FlashMLA, `Proof/Lib/UbStopAt.lean`):
for a machine that follows every value its thread reads, whose other states may have templates
that are undefined. -/
theorem ub_stopped_at {C : Code K A L g} (hC : C.Sound) {es : List Event}
    (hp : Produces K A L g es) {k pc : Nat} {f : Fault} (hk : es[k]? = some ⟨pc, .ub f⟩)
    (hok : ∀ d, C.toMachine.after (some C.init) (es.take k) = some (some d) →
      ∀ t ins, C.AtD d t → C.inv d → K.code[C.pc d]? = some ins →
        eventTmpl A L g t ins.op ≠ .ub f) :
    C.toMachine.after (some C.init) (es.take k) = none ∨
      C.toMachine.after (some C.init) (es.take k) = some none := by
  have htr := hC.machine.produces hp
  rcases htr.fired hk with ⟨τ, o, ha, hf⟩ | ⟨ha, -⟩
  · cases τ with
    | none => exact .inr ha
    | some d =>
      exfalso
      obtain ⟨t, ins, hat, hinv, hc, hfire⟩ := Code.fired_site hC hf
      exact hok d ha t ins hat hinv hc (fires_ub hfire rfl)
  · exact .inl ha

end Code

end

end PTX.Flow
