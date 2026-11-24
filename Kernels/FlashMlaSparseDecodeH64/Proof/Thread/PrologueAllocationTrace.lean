-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.GlobalWrites
import Lemmas.Flow.AllocTmpl
import Lemmas.Tmem.Alloc512
import Lemmas.Tmem.TmemPairRecord
import Lemmas.Async.ReadSources
public import Lemmas.Flow.Facts

public section

/-! # The prologue's 512-column allocation result -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.PrologueAllocation
open PTX PTX.Flow PTX.Proof Tmem.Pair AsyncCopy

/-- Shared word where the allocating warp returns its Tensor Memory column. -/
@[expose] def allocAddress (L : Launch) (g : Nat) : Loc :=
  ⟨.shared, ctaOf L g, L.sharedBase + 222752⟩

private theorem address_shape {P : Params} {L : Launch} {mem0 : Mem0}
    (hpre : Pre P L mem0) (g : Nat) : (allocAddress L g).addr < 2 ^ 32 ∧
      (allocAddress L g).addr % 4 = 0 := by
  have ha := hpre.sharedAlignment
  rw [← hpre.sharedBase] at ha
  have hb := sharedBase_lt hpre
  change L.sharedBase + 222752 < 2 ^ 32 ∧ (L.sharedBase + 222752) % 4 = 0
  exact ⟨by omega, by omega⟩

private theorem stores_zero {L : Launch} {mem0 : Mem0} {X : Execution} {g i : Nat}
    (hX : Consistent L kernel Assumptions.all mem0 X) (hblock : L.block = 384)
    (hlane : PTX.laneOf L g = 0) (hsafe : ¬ ResourceUnsafe L X)
    {p p' : Nat} {a : Acc} {bs : List Byte}
    (hi : X.get (g, i) = some ⟨p, .tc (.resource .one (some (allocAddress L g)) (.alloc 512))⟩)
    (hw : X.get (g, i + 1) = some ⟨p', .wr a bs⟩) : bs = (b32 0).toBytes := by
  have hlen := (List.getElem?_eq_some_iff.mp hw).1
  obtain ⟨cta, req, hreq, lane, hown⟩ := hX.tmemPairBlocking.performed hi hlen
  have hv := (hX.tmemPair.1 cta).1 req hreq
  have he := hv.2.2.2.2.1 lane
  rw [hown, hi] at he
  have he := Kind.tc.inj (congrArg Event.kind (Option.some.inj he))
  injection he with _ _ hr
  have ha : ∃ col, req.action = .alloc 512 col := by
    have hreq' := hv.2.1.trans hr.symm
    cases hact : req.action with
    | alloc n col =>
      have hn : n = 512 := by simpa [hact, Tmem.Action.request] using hreq'
      exact ⟨col, by rw [hn]⟩
    | dealloc => simp [hact, Tmem.Action.request] at hreq'
    | relinquish => simp [hact, Tmem.Action.request] at hreq'
  have hn : lane = 0 := by
    have h := congrArg Prod.fst hown
    change req.own.cta * L.block + req.own.warp * 32 + lane.val = g at h
    have hmod := congrArg (fun x : Nat => x % 384 % 32) h
    change g % L.block % 32 = 0 at hlane
    rw [hblock] at hmod hlane
    have hlt := lane.isLt
    exact Fin.ext (by change lane.val = 0; omega)
  obtain ⟨col, hact⟩ := ha
  subst lane
  exact hX.alloc512_result (tmemNoFault_of_safe hsafe cta) hi hreq hown hact hw

/-- The actual allocation instruction requests all 512 columns and writes column zero when its
warp's resource history is safe. -/
theorem alloc_write {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g i : Nat}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (hsafe : ¬ ResourceUnsafe L X)
    (hlane : laneOf L g = 0)
    (hq : Frame.stateAt (Machine.code P L) X g i = some (some (.prologue .alloc)))
    {request store : Event} (hi : X.get (g, i) = some request)
    (hw : X.get (g, i + 1) = some store) :
    X.Writes (g, i + 1) ⟨allocAddress L g, 4, false, false, .cta, 0, false⟩ (b32 0).toBytes := by
  obtain ⟨t, ins, o, hat, _, hcode, hf⟩ := Frame.fired_site hs hX hi hq
  change kernel.code[Flow.tmemAlloc_0]? = some ins at hcode
  obtain rfl := Option.some.inj (hcode.symm.trans Flow.code_tmemAlloc_0)
  have hb : L.block % 32 = 0 := by rw [hpre.block]
  have ha : t.regs 554 = some (b32 (allocAddress L g).addr) := by
    have h := holds_mem hat.2.2.2.2 (mem_factsFrom (by table_decide : 554 ∈ liveAll 91))
    exact h
  have hn : t.regs 555 = some (b32 512) := by
    have h := holds_mem hat.2.2.2.2 (mem_factsFrom (by table_decide : 555 ∈ liveAll 91))
    exact h
  have hsub : t.sub = 0 := hat.2.1
  obtain ⟨hfit, halign⟩ := address_shape hpre g
  rw [tcAlloc_tmpl0 hb ha hfit halign hn hsub] at hf
  have he : request =
      ⟨Flow.tmemAlloc_0, .tc (.resource .one (some (allocAddress L g)) (.alloc 512))⟩ := hf.1
  rw [he] at hi
  have hs' : Frame.stateAt (Machine.code P L) X g (i + 1) =
      some (some (.prologue .allocStore)) := by
    rw [Frame.stateAt_succ hi, hq]
    change Machine.next P L g (.prologue .alloc)
      ⟨Flow.tmemAlloc_0, .tc (.resource .one (some (allocAddress L g)) (.alloc 512))⟩ = _
    simp [Machine.next, next, hlane]; rfl
  obtain ⟨t', ins', o', hat', _, hcode', hf'⟩ := Frame.fired_site hs hX hw hs'
  change kernel.code[Flow.tmemAlloc_0]? = some ins' at hcode'
  obtain rfl := Option.some.inj (hcode'.symm.trans Flow.code_tmemAlloc_0)
  have ha' : t'.regs 554 = some (b32 (allocAddress L g).addr) := by
    have h := holds_mem hat'.2.2.2.2 (mem_factsFrom (by table_decide : 554 ∈ liveAll 91))
    exact h
  have hn' : t'.regs 555 = some (b32 512) := by
    have h := holds_mem hat'.2.2.2.2 (mem_factsFrom (by table_decide : 555 ∈ liveAll 91))
    exact h
  have hs₁ : t'.sub = 1 := hat'.2.1
  rw [tcAlloc_tmpl1 hb ha' hfit halign hn' hs₁] at hf'
  obtain ⟨col, _, hkind, _⟩ := hf'
  rw [hkind] at hw
  have hzero := stores_zero hX hpre.block ((laneOf_core hpre).trans hlane) hsafe hi hw
  exact ⟨_, hzero ▸ hw⟩

set_option maxRecDepth 100000 in
/-- The allocation load's template reads the representative lane's four-byte result word. -/
theorem alloc_read_template {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {t : TState}
    (hpre : Pre P L mem0) (hsub : t.sub = 0) :
    eventTmpl Assumptions.all L g t (.mem allocLoad) =
      .read ⟨allocAddress L g, 4, false, false, .cta, 0, false⟩
        (afterAccessLoad t .same 32 [557]) := by
  obtain ⟨hfit, halign⟩ := address_shape hpre g
  change L.sharedBase + 222752 < 2 ^ 32 at hfit
  have hw : wrapAddr 32 (BitVec.ofNat 64 L.sharedBase) 222752 =
      L.sharedBase + 222752 := by
    have hbase : L.sharedBase < 2 ^ 64 := by omega
    have hfit' : L.sharedBase + 222752 < 2 ^ 64 := by omega
    have hoff : BitVec.ofInt 64 222752 = BitVec.ofNat 64 222752 := by decide
    unfold wrapAddr
    rw [hoff]
    simp only [truncBits, BitVec.toNat_ofNat, BitVec.toNat_add, Nat.mod_eq_of_lt hbase]
    rw [show (222752 : Nat) % 2 ^ 64 = 222752 by decide,
      Nat.mod_eq_of_lt hfit', Nat.mod_eq_of_lt hfit, Nat.mod_eq_of_lt hfit']
  have hr : allocLoad.rule = some .threadAccess := by decide +kernel
  have ha : allocLoad.addr.base = .sharedSym 0 := rfl
  simp only [eventTmpl, memTmpl, hr, ha]
  have hloc : allocLoad.locSpace? = none := rfl
  simp only [hloc]
  have hacc : accessAcc L g t allocLoad =
      .ok ⟨allocAddress L g, 4, false, false, .cta, 0, false⟩ := by
    have hk : accessLoc L g t allocLoad = .ok (allocAddress L g) := by
      simp only [accessLoc, allocLoad, Nat.add_zero, pure, Except.pure, hw]
      rfl
    rw [accessAcc_of_weak (by rfl), hk]
    simp [allocLoad, hsub, DType.width, elemAcc, halign, bind, Except.bind,
      pure, Except.pure, Loc.at]
  simp only [accessTmpl, show allocLoad.kind = .load from rfl, hacc,
    show allocLoad.nc = false from rfl, Bool.false_eq_true, ↓reduceIte]
  rfl

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g i : Nat} (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X) (hs : GlobalWrites.SoundThreads P L)
    (hq : Frame.stateAt (Machine.code P L) X g i = some (some (.prologue .allocRead)))
include hpre hX hs hq

/-- The prologue's read-back instruction accesses the same four-byte word as the allocator. -/
theorem alloc_read {e : Event} (he : X.get (g, i) = some e) :
    ∃ bs, e.kind = .rd ⟨allocAddress L g, 4, false, false, .cta, 0, false⟩ bs := by
  obtain ⟨t, ins, o, hat, _, hcode, hf⟩ := Frame.fired_site hs hX he hq
  change kernel.code[Flow.load_0]? = some ins at hcode
  obtain rfl := Option.some.inj (hcode.symm.trans Flow.code_load_0)
  change Fires Flow.load_0 (eventTmpl Assumptions.all L g t (.mem allocLoad)) e o at hf
  rw [alloc_read_template hpre hat.2.1] at hf
  obtain ⟨bs, _, rfl, _⟩ := hf
  exact ⟨bs, rfl⟩

/-- Once it sees the allocation store, the actual prologue read reaches relinquishment. -/
theorem follows_read {e : Event} (he : X.get (g, i) = some e) {store : EvId}
    (hw : X.Writes store ⟨allocAddress L g, 4, false, false, .cta, 0, false⟩ (b32 0).toBytes)
    (hrf : ∀ k < 4, X.rf (.thread (g, i)) k = some (.thread store)) :
    Frame.stateAt (Machine.code P L) X g (i + 1) =
      some (some (.prologue .relinquish)) := by
  obtain ⟨bs, hk⟩ := alloc_read hpre hX hs hq he
  let a : Acc := ⟨allocAddress L g, 4, false, false, .cta, 0, false⟩
  have hm : X.MemReads (.thread (g, i)) a bs := by
    obtain ⟨tag, kind⟩ := e
    change kind = _ at hk
    subst kind
    exact .inl ⟨tag, he⟩
  have hread := hX.rf _ _ _ hm
  have hlen := hread.1
  change bs.length = 4 at hlen
  have hbytes : (b32 0).toBytes.length = 4 := rfl
  have hbs : bs = (b32 0).toBytes.map some := by
    apply List.ext_getElem?
    intro k
    by_cases h : k < 4
    · have hv := hread.2 k h
      rw [hrf k h] at hv
      obtain ⟨_, _, hwriter, _, hb⟩ := hv
      obtain ⟨hf, rfl⟩ := (show X.MemWrites (.thread store) a (b32 0).toBytes from .inl hw).unique
        hwriter
      rw [List.getElem?_map, List.getElem?_eq_getElem (by omega : k < (b32 0).toBytes.length)]
      simpa [wbyte, ← hf.1, Loc.at, List.getElem?_eq_getElem (by omega :
        k < (b32 0).toBytes.length)] using hb
    · rw [List.getElem?_eq_none (by omega), List.getElem?_map,
        List.getElem?_eq_none (by omega : (b32 0).toBytes.length ≤ k)]
      rfl
  obtain ⟨tag, kind⟩ := e
  change kind = _ at hk
  subst kind
  rw [Frame.stateAt_succ he, hq]
  change Machine.next P L g (.prologue .allocRead) ⟨tag, .rd a bs⟩ = _
  rw [hbs]
  simp [Machine.next, next, rebuild_b32, bind, Except.bind]
  rfl


end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.PrologueAllocation
