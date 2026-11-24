-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderRecurringSources
public import Kernels.TmlFa4Fwd.Proof.GlobalWrites
public import Lemmas.Flow.Vector
public import Lemmas.Protocol.LocalMemory

public import Kernels.TmlFa4Fwd.Proof.LoaderPrefixDemand

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Flow PTX.Proof

noncomputable section

/-- The first saved K or V page pointer read in each recurring packet. -/
def pointerReloadPc : Fin 4 → Nat
  | 0 => 1003
  | 1 => 1238
  | 2 => 1469
  | 3 => 1632

def pointerReloadBase (i : Fin 4) : Nat := if i.val % 2 = 0 then 7293 else 7292

def pointerReloadRegisters : Fin 4 → Nat × Nat
  | 0 => (1998, 1999)
  | 1 => (2077, 2078)
  | 2 => (2156, 2157)
  | 3 => (2198, 2199)

def pointerReloadAddress (l : Launch) (i : Fin 4) : Nat :=
  l.localBase + if i.val % 2 = 0 then 32 else 0

/-- The first and second saved pointers are reloaded at different decoded sites. -/
def pointerSlotReloadPc (i : Fin 4) (slot : Fin 2) : Nat :=
  if slot.val = 0 then pointerReloadPc i
  else (![1072, 1292, 1537, 1685] : Fin 4 → Nat) i

def pointerSlotReloadRegs (i : Fin 4) (slot : Fin 2) : Nat × Nat :=
  if slot.val = 0 then pointerReloadRegisters i
  else let low := (![2019, 2098, 2177, 2219] : Fin 4 → Nat) i; (low, low + 1)

def pointerSlotStore (l : Launch) (g : Nat) (i : Fin 4) (slot : Fin 2) : Acc :=
  {loc := ⟨.local, g, pointerReloadAddress l i + 8 * slot.val⟩, size := 8}

def pointerSlotAccess (l : Launch) (g : Nat) (i : Fin 4) (slot word : Fin 2) : Acc :=
  {loc := (pointerSlotStore l g i slot).loc.at (4 * word.val), size := 4, elem := word.val}

/-- Decoded operands for an ordinary vector reload of a previously saved pointer. -/
structure SavedPointerReload where
  pc : Nat
  baseReg : Nat
  offset : Nat
  lowReg : Nat
  highReg : Nat

def SavedPointerReload.cell (site : SavedPointerReload) (g base : Nat) : Acc :=
  {loc := ⟨.local, g, base + site.offset⟩, size := 8}

def SavedPointerReload.word (site : SavedPointerReload) (g base : Nat) (word : Fin 2) : Acc :=
  {loc := (site.cell g base).loc.at (4 * word.val), size := 4, elem := word.val}

def SavedPointerReload.mem (site : SavedPointerReload) : MemAccess :=
  {kind := .load, space := some .local, sem := .weak, elem := .int .b 32, vec := 2,
   addr := ⟨.reg site.baseReg 64, (site.offset : Int)⟩,
   dsts := [some site.lowReg, some site.highReg]}

/-- Resolve one decoded half of a vector pointer reload. -/
theorem pointerReloadTemplate {l : Launch} {g base : Nat}
    (site : SavedPointerReload) (hRange : 174 ≤ site.pc ∧ site.pc < 1906)
    (hCode : kernel.code[site.pc]? = some ⟨none, .mem site.mem⟩)
    (hBound : base + site.offset < 2 ^ 64) (ha : (base + site.offset) % 8 = 0)
    (word : Fin 2) {s : TState} (hPc : s.pc = site.pc) (hFault : s.fault = none)
    (hSub : s.sub = word.val) (hReg : s.regs site.baseReg = some (b64 base)) :
    out kernel Assumptions.all l g s =
      .ev (.read (site.word g base word) (afterLoad s [site.lowReg, site.highReg])) := by
  have hb : readBits l g s 64 (.reg site.baseReg) = .ok (BitVec.ofNat 64 base) :=
    readBits_b64 hReg (by omega)
  have hLoc : accessLoc l g s site.mem = .ok (site.cell g base).loc := by
    simp only [accessLoc, SavedPointerReload.mem, hb, bind, Except.bind, wrapAddr,
      BitVec.ofInt_natCast, ← BitVec.ofNat_add, truncBits_ofNat hBound (by decide),
      toNat_ofNat_lt hBound, pure, Except.pure, SavedPointerReload.cell]
  have hLo : 174 ≤ s.pc := hPc ▸ hRange.1
  have hHi : s.pc < 1906 := hPc ▸ hRange.2
  rw [loaderOutCore hLo hHi, out_event hFault (by rwa [hPc]) rfl rfl]
  change Out.ev (memTmpl [] l g s site.mem) = _
  have hRule : site.mem.rule = some .threadAccess := rfl
  have hSpace : site.mem.locSpace? = none := rfl
  have hAccess : accessAcc l g s site.mem = .ok (site.word g base word) := by
    rw [accessAcc_of_weak (a := site.mem) rfl, hLoc]
    have hAlign : (site.cell g base).loc.addr % 8 = 0 := ha
    simp [SavedPointerReload.mem, CacheHints.globalOnly, DType.width, hSub,
      bind, Except.bind, elemAcc, hAlign, SavedPointerReload.word, pure, Except.pure]
  simp only [memTmpl, hRule, hSpace, ↓reduceIte, accessTmpl, hAccess]
  change Out.ev (.read (site.word g base word)
    (afterAccessLoad s .same 32 [site.lowReg, site.highReg])) = _
  rw [afterAccessLoad_same]

/-- The decoded pointer load produces its first scalar read at the observed cursor. -/
theorem SavedPointerReload.firstReadOccursInPrefix {l : Launch} {X : Execution} {g index addr : Nat}
    (site : SavedPointerReload) (hRange : 174 ≤ site.pc ∧ site.pc < 1906)
    (hCode : kernel.code[site.pc]? = some ⟨none, .mem site.mem⟩)
    (hBound : addr + site.offset < 2 ^ 64) (hAlign : (addr + site.offset) % 8 = 0)
    {s : TState} (hs : At s site.pc [(site.baseReg, b64 addr)])
    {ending : Option TState}
    (hr : Run kernel Assumptions.all l g s ((X.tr g).drop index) ending)
    (hMore : (X.tr g).drop index ≠ []) :
    ∃ bytes, X.get (g, index) = some ⟨site.pc, .rd (site.word g addr 0) bytes⟩ := by
  have hNext : Next kernel Assumptions.all l g s s
      (.read (site.word g addr 0) (afterLoad s [site.lowReg, site.highReg])) :=
    ⟨.refl, pointerReloadTemplate site hRange hCode hBound hAlign 0 hs.1 hs.2.2.2.1
      hs.2.1 hs.2.2.2.2.1⟩
  obtain ⟨_, _, he, ⟨bytes, _, rfl, _⟩, _⟩ := hNext.continuing_at_nonempty (by
    rintro ev ⟨_, _, _, hBad⟩; cases hBad) hr hMore
  exact ⟨bytes, by simpa only [hs.1] using he⟩

/-- Expected bytes of one scalar half of the saved pointer. -/
def pointerReadBytes (base : Nat) (word : Fin 2) : List (Option Byte) :=
  (List.range 4).map fun k => some ((b64 base).byteAt (4 * word.val + k))

private theorem pointerHalfBytes {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X)
    {g w index base addr : Nat} (site : SavedPointerReload) (word : Fin 2)
    (hOrder : w < index)
    (hStore : X.Writes (g, w) (site.cell g addr) (b64 base).toBytes)
    {bs : List (Option Byte)} (hLen : bs.length = 4)
    (hRead : X.Reads (g, index) (site.word g addr word) bs)
    (hLast : ∀ byte < 8, ∀ j a, X.Access (g, j) a true →
      a.Covers ((site.cell g addr).loc.at byte) → j ≤ w ∨ index < j) :
    bs = pointerReadBytes base word := by
  apply List.ext_getElem?
  intro k
  by_cases hk : k < 4
  · have hword := word.isLt
    have hByte : 4 * word.val + k < 8 := by omega
    have hLoc : (site.word g addr word).loc.at k =
        (site.cell g addr).loc.at (4 * word.val + k) := by
      simp [SavedPointerReload.word, Loc.at, Nat.add_assoc]
    have hCover : (site.cell g addr).Covers
        ((site.word g addr word).loc.at k) := by
      rw [hLoc]
      exact Acc.covers_at hByte
    have hv := local_read_byte_of_last_write hX hRead hStore hk hCover hOrder
      (fun ref a data hWrite hCov => localWriteOwner hX hWrite rfl hCov)
      (fun j a hWrite hCov => hLast _ hByte j a hWrite (hLoc ▸ hCov))
    rw [hv, hLoc]
    have hIndex : 4 * word.val + k < (b64 base).toBytes.length := by
      simpa [b64, Value.toBytes, Value.bytes] using hByte
    rw [wbyte, Loc.at, Nat.add_sub_cancel_left, List.getElem?_eq_getElem hIndex]
    simp [pointerReadBytes, Value.toBytes, b64, hk]
  · have hNone : bs[k]? = none := List.getElem?_eq_none (by omega)
    have hNone' : (pointerReadBytes base word)[k]? = none := by
      apply List.getElem?_eq_none
      simpa [pointerReadBytes] using Nat.le_of_not_gt hk
    rw [hNone, hNone']

section
variable {l : Launch} {m : Mem0} {X : Execution} (hX : Consistent l kernel Assumptions.all m X)
    {g write index base addr : Nat} (site : SavedPointerReload)
    (hRange : 174 ≤ site.pc ∧ site.pc < 1906)
    (hCode : kernel.code[site.pc]? = some ⟨none, .mem site.mem⟩)
    (hAddr : addr + site.offset < 2 ^ 64) (hAlign : (addr + site.offset) % 8 = 0)
    (hDistinct : site.lowReg ≠ site.highReg) (hBase : base < 2 ^ 64) (hOrder : write < index)
    {s : TState} {F : List (Nat × Value)} (hs : At s site.pc ((site.baseReg, b64 addr) :: F))
    (hFresh : ∀ pair ∈ F, pair.1 ≠ site.lowReg ∧ pair.1 ≠ site.highReg)
include hX site hRange hCode hAddr hAlign hDistinct hBase hOrder hs hFresh

/-- Recover the low and high register halves from an actual lane-local reload.
The caller identifies the last eight-byte store before the reload begins. -/
theorem SavedPointerReload.observedWithPrefix {ending : Option TState}
    (hr : Run kernel Assumptions.all l g s ((X.tr g).drop index) ending)
    (hMore : (X.tr g).drop index ≠ [])
    (hNextWord : ∀ {u bytes}, X.get (g, index) = some ⟨site.pc, .rd (site.word g addr 0) bytes⟩ →
      Run kernel Assumptions.all l g u ((X.tr g).drop (index + 1)) ending →
      (X.tr g).drop (index + 1) ≠ [])
    (hStore : X.Writes (g, write) (site.cell g addr) (b64 base).toBytes)
    (hLast : ∀ byte < 8, ∀ j < index, ∀ a, X.Access (g, j) a true →
      a.Covers ((site.cell g addr).loc.at byte) → j ≤ write) :
    ∃ u, At u (site.pc + 1)
        [(site.lowReg, b32 (base % 2 ^ 32)),
         (site.highReg, b32 (base / 2 ^ 32))] ∧
      Holds u.regs F ∧ Run kernel Assumptions.all l g u ((X.tr g).drop (index + 2)) ending ∧
      X.get (g, index) = some ⟨site.pc,
        .rd (site.word g addr 0) (pointerReadBytes base 0)⟩ ∧
      X.get (g, index + 1) = some ⟨site.pc,
        .rd (site.word g addr 1) (pointerReadBytes base 1)⟩ := by
  let rs := [site.lowReg, site.highReg]
  let lo := b32 (base % 2 ^ 32)
  let hi := b32 (base / 2 ^ 32)
  have hNext : Next kernel Assumptions.all l g s s
      (.read (site.word g addr 0) (afterLoad s rs)) :=
    ⟨.refl, pointerReloadTemplate site hRange hCode hAddr hAlign 0 hs.1 hs.2.2.2.1
      hs.2.1 hs.2.2.2.2.1⟩
  obtain ⟨_, _, he0, ⟨bs0, hlen0, rfl, hU0⟩, hr0⟩ := hNext.continuing_at_nonempty (by
    rintro ev ⟨_, _, _, hBad⟩
    cases hBad) hr hMore
  obtain rfl := Option.some.inj hU0
  have hRead0 : X.Reads (g, index) (site.word g addr 0) bs0 := ⟨_, he0⟩
  have noWriteAt {i : Nat} {a dst : Acc} {bs : List (Option Byte)}
      (hRead : X.Reads (g, i) a bs) (hw : X.Access (g, i) dst true) : False := by
    obtain ⟨pc, he⟩ := hRead
    rcases hw with ⟨_, _, hBad⟩ | ⟨_, ⟨_, he'⟩, _⟩ | ⟨_, _, hRmw⟩
    · cases hBad
    · have hBad := Option.some.inj (he.symm.trans he')
      cases hBad
    · exact noActualRmw hX hRmw
  have hB0 := pointerHalfBytes hX site 0 hOrder hStore hlen0 hRead0 (by
    intro byte hb j a ha hc
    rcases lt_trichotomy j index with hLt | rfl | hGt
    · exact Or.inl (hLast byte hb j hLt a ha hc)
    · exact False.elim (noWriteAt hRead0 ha)
    · exact Or.inr hGt)
  subst bs0
  have hLo : rebuild 3 (pointerReadBytes base 0) = .ok lo := by
    simpa [pointerReadBytes, lo, b64, b32, toNat_ofNat_lt hBase] using
      rebuild_b64_half (BitVec.ofNat 64 base) false
  let mid := {s with sub := 1, acc := [lo]}
  have hMid : afterLoad s rs (pointerReadBytes base 0) = mid := by
    rw [afterLoad_mid hLo (by simp [hs.2.1, rs])]
    simp [mid, hs.2.1, hs.2.2.1]
  rw [hMid] at hr0
  have hNext1 : Next kernel Assumptions.all l g mid mid
      (.read (site.word g addr 1) (afterLoad mid rs)) :=
    ⟨.refl, pointerReloadTemplate site hRange hCode hAddr hAlign 1 hs.1 hs.2.2.2.1
      rfl hs.2.2.2.2.1⟩
  have hFirst : X.get (g, index) = some ⟨site.pc,
      .rd (site.word g addr 0) (pointerReadBytes base 0)⟩ := by
    simpa only [hs.1] using he0
  obtain ⟨_, _, he1, ⟨bs1, hlen1, rfl, hU1⟩, hr1⟩ := hNext1.continuing_at_nonempty (by
    rintro ev ⟨_, _, _, hBad⟩
    cases hBad) hr0 (hNextWord hFirst hr0)
  obtain rfl := Option.some.inj hU1
  have hRead1 : X.Reads (g, index + 1) (site.word g addr 1) bs1 := ⟨_, he1⟩
  have hB1 := pointerHalfBytes hX site 1 (by omega) hStore hlen1 hRead1 (by
    intro byte hb j a ha hc
    by_cases hLt : j < index
    · exact Or.inl (hLast byte hb j hLt a ha hc)
    by_cases hGt : index + 1 < j
    · exact Or.inr hGt
    have hEq : j = index ∨ j = index + 1 := by omega
    rcases hEq with rfl | rfl
    · exact False.elim (noWriteAt (a := site.word g addr 0) ⟨_, he0⟩ ha)
    · exact False.elim (noWriteAt hRead1 ha))
  subst bs1
  have hHi : rebuild 3 (pointerReadBytes base 1) = .ok hi := by
    have hH : base / 4294967296 < 4294967296 := by omega
    simpa [pointerReadBytes, hi, b64, b32, toNat_ofNat_lt hBase, Nat.mod_eq_of_lt hH] using
      rebuild_b64_half (BitVec.ofNat 64 base) true
  let u := next (setReg (setReg s site.lowReg lo)
    site.highReg hi)
  have hEnd : afterLoad mid rs (pointerReadBytes base 1) = u := by
    rw [afterLoad_last hHi (by simp [mid, rs])]
    simp [u, mid, next, setRegs, setReg, rs, hs.2.1, hs.2.2.1]
  rw [hEnd] at hr1
  have hFields : Holds u.regs F := by
    apply Epilogue.holdsSchedulerFrame (regs := F.map Prod.fst) hs.2.2.2.2.2
    · intro r hR
      obtain ⟨pair, hm, rfl⟩ := List.mem_map.mp hR
      have hN := hFresh pair hm
      simp [u, next, setReg, hN.1, hN.2]
    · intro pair hp
      exact List.mem_map_of_mem hp
  refine ⟨u, ?_, hFields, by simpa [Nat.add_assoc] using hr1,
    by simpa only [hs.1] using he0, by simpa only [mid, hs.1] using he1⟩
  simp [u, At, next, setReg, hs.1, hDistinct, hs.2.1, hs.2.2.1, hs.2.2.2.1, lo, hi]

theorem SavedPointerReload.observedInPrefix {ending : Option TState} {bound : Nat}
    (hAdvance : site.pc ≤ bound)
    (hr : Run kernel Assumptions.all l g s ((X.tr g).drop index) ending)
    (hDemand : PrefixDemand X g index bound ending)
    (hStore : X.Writes (g, write) (site.cell g addr) (b64 base).toBytes)
    (hLast : ∀ byte < 8, ∀ j < index, ∀ a, X.Access (g, j) a true →
      a.Covers ((site.cell g addr).loc.at byte) → j ≤ write) :
    ∃ u, At u (site.pc + 1)
        [(site.lowReg, b32 (base % 2 ^ 32)),
         (site.highReg, b32 (base / 2 ^ 32))] ∧
      Holds u.regs F ∧ Run kernel Assumptions.all l g u ((X.tr g).drop (index + 2)) ending ∧
      X.get (g, index) = some ⟨site.pc,
        .rd (site.word g addr 0) (pointerReadBytes base 0)⟩ ∧
      X.get (g, index + 1) = some ⟨site.pc,
        .rd (site.word g addr 1) (pointerReadBytes base 1)⟩ :=
  site.observedWithPrefix hX hRange hCode hAddr hAlign hDistinct hBase hOrder hs hFresh hr
    (hDemand.nonempty hr) (fun hRead hRun => (hDemand.advance hRead hAdvance).nonempty hRun)
    hStore hLast

/-- The same pointer reload in a terminated trace. -/
theorem SavedPointerReload.observedBefore
    (hr : Run kernel Assumptions.all l g s ((X.tr g).drop index) none)
    (hStore : X.Writes (g, write) (site.cell g addr) (b64 base).toBytes)
    (hLast : ∀ byte < 8, ∀ j < index, ∀ a, X.Access (g, j) a true →
      a.Covers ((site.cell g addr).loc.at byte) → j ≤ write) :
    ∃ u, At u (site.pc + 1)
        [(site.lowReg, b32 (base % 2 ^ 32)),
         (site.highReg, b32 (base / 2 ^ 32))] ∧
      Holds u.regs F ∧ Run kernel Assumptions.all l g u ((X.tr g).drop (index + 2)) none ∧
      X.get (g, index) = some ⟨site.pc,
        .rd (site.word g addr 0) (pointerReadBytes base 0)⟩ ∧
      X.get (g, index + 1) = some ⟨site.pc,
        .rd (site.word g addr 1) (pointerReadBytes base 1)⟩ :=
  site.observedInPrefix hX hRange hCode hAddr hAlign hDistinct hBase hOrder hs hFresh
    le_rfl hr (.inl rfl) hStore hLast

/-- Recover the low and high register halves from an actual lane-local reload.
The caller identifies the last eight-byte store before the two read events. -/
theorem SavedPointerReload.observed
    (hr : Run kernel Assumptions.all l g s ((X.tr g).drop index) none)
    (hStore : X.Writes (g, write) (site.cell g addr) (b64 base).toBytes)
    (hLast : ∀ word : Fin 2, ∀ byte < 8, ∀ j a, X.Access (g, j) a true →
      a.Covers ((site.cell g addr).loc.at byte) → j ≤ write ∨ index + word.val < j) :
    ∃ u, At u (site.pc + 1)
        [(site.lowReg, b32 (base % 2 ^ 32)),
         (site.highReg, b32 (base / 2 ^ 32))] ∧
      Holds u.regs F ∧ Run kernel Assumptions.all l g u ((X.tr g).drop (index + 2)) none ∧
      X.get (g, index) = some ⟨site.pc,
        .rd (site.word g addr 0) (pointerReadBytes base 0)⟩ ∧
      X.get (g, index + 1) = some ⟨site.pc,
        .rd (site.word g addr 1) (pointerReadBytes base 1)⟩ :=
  site.observedBefore hX hRange hCode hAddr hAlign hDistinct hBase hOrder hs hFresh hr hStore
    (fun byte hb j hj a ha hc => (hLast 0 byte hb j a ha hc).resolve_right
      (by simpa using hj.not_gt))
end

end
end PTX.Kernels.TmlFa4Fwd.Loader
