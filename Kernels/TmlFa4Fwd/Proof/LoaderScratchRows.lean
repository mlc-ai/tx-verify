-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderPageScratch
public import Kernels.TmlFa4Fwd.Proof.GlobalWrites
public import Kernels.TmlFa4Fwd.Flow.Code.Part008
public import Lemmas.Protocol.LocalMemory
public import Kernels.TmlFa4Fwd.Flow.Code.Part012

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Proof PTX.Flow

noncomputable section

structure ScratchReloadSite where
  pc : Nat
  base : Nat
  destination : Nat
  array : Fin 4
  store : Nat

/-- The page and row fields feed the first K and V address preparations. -/
def scratchReloadSite : Fin 4 → ScratchReloadSite
  | 0 => ⟨525, 7536, 7537, 3, 506⟩
  | 1 => ⟨527, 7538, 7539, 2, 511⟩
  | 2 => ⟨790, 7600, 7601, 3, 506⟩
  | 3 => ⟨792, 7602, 7603, 2, 511⟩

def scratchReloadAccess (l : Launch) (g : Nat) (site : ScratchReloadSite) (entry : Fin 2) :
    Acc :=
  {loc := ⟨.local, g, l.localBase + kvLocalOffset site.array entry⟩, size := 4}

def scratchWordAccess (l : Launch) (g : Nat) (site : Fin 4) (entry : Fin 2) : Acc :=
  scratchReloadAccess l g (scratchReloadSite site) entry

def ScratchReloadCode (site : ScratchReloadSite) : Prop :=
    kernel.code[site.pc]? = some ⟨none, .mem
      { kind := .load, space := some .local, sem := .weak, elem := .int .s 32,
        ext := .sign 64, addr := ⟨.reg site.base 64, 0⟩,
        dsts := [some site.destination] }⟩

private theorem scratchReloadCode (site : Fin 4) :
    ScratchReloadCode (scratchReloadSite site) := by
  fin_cases site
  · exact Flow.code_525
  · exact Flow.code_527
  · exact Flow.code_790
  · exact Flow.code_792

/-- The decoded scratch reload produces the signed local-read callback. -/
theorem scratchReloadTemplate {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g : Nat} (site : ScratchReloadSite) (hCode : ScratchReloadCode site)
    (hRange : 174 ≤ site.pc ∧ site.pc < 1906) (hArray : ¬ site.array.val < 2)
    (entry : Fin 2) {t : TState}
    (ht : At t site.pc
      [(site.base, b64
        (l.localBase + kvLocalOffset site.array entry))]) :
    out kernel Assumptions.all l g t = .ev (.read (scratchReloadAccess l g site entry)
      (afterAccessLoad t (.sign 64) 32 [site.destination])) := by
  have hBound := hp.localMemory.2.1
  have hLocal : l.localBase + kvLocalOffset site.array entry < 2 ^ 64 := by
    have hOffset := kvLocalOffset_bound site.array entry (byte := 0) (by
      rw [ite_eq_right hArray]
      decide)
    omega
  have hAlign : (l.localBase + kvLocalOffset site.array entry) % 4 = 0 := by
    simpa only [ite_eq_right hArray] using
      kvLocalOffset_aligned site.array entry hp.localMemory.1
  have hAddr := ht.2.2.2.2.1
  rw [loaderOutCore (by rw [ht.1]; exact hRange.1) (by rw [ht.1]; exact hRange.2)]
  rw [out_event ht.2.2.2.1 (by rw [ht.1]; exact hCode) rfl rfl]
  change Out.ev (accessTmpl [] l g t {
    kind := .load, space := some .local, sem := .weak, elem := .int .s 32, ext := .sign 64,
    addr := ⟨.reg site.base 64, 0⟩,
    dsts := [some site.destination] }) = _
  simp [accessTmpl, accessAcc, accessLoc, elemAcc, wrapAddr, readBits, readReg, hAddr,
    hAlign, ht.2.1, b64, Loc.at, MemAccess.strongLocOk, MemAccess.semAcc, CacheHints.globalOnly,
    DType.width, truncBits_ofNat hLocal (by decide), toNat_ofNat_lt hLocal,
    bind, Except.bind, Functor.map, Except.map, pure, Except.pure, scratchReloadAccess,
    MemAccess.regs]

/-- The actual scratch-slot access is a read, independently of the value it returns. -/
theorem scratchWordLoadPresentInPrefix {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) {g index : Nat} (site : Fin 4) (entry : Fin 2) {t : TState}
    (ht : At t (scratchReloadSite site).pc
      [((scratchReloadSite site).base, b64
        (l.localBase + kvLocalOffset (scratchReloadSite site).array entry))])
    {ending : Option TState}
    (hr : Run kernel Assumptions.all l g t ((X.tr g).drop index) ending)
    (hMore : (X.tr g).drop index ≠ []) :
    ∃ bs, X.get (g, index) = some ⟨(scratchReloadSite site).pc,
      .rd (scratchWordAccess l g site entry) bs⟩ := by
  let s := scratchReloadSite site
  have hRange : 174 ≤ s.pc ∧ s.pc < 1906 := by fin_cases site <;> decide
  have hArray : ¬ s.array.val < 2 := by fin_cases site <;> decide
  have hn : Next kernel Assumptions.all l g t t
      (.read (scratchWordAccess l g site entry)
        (afterAccessLoad t (.sign 64) 32 [s.destination])) :=
    ⟨.refl, scratchReloadTemplate hp s (scratchReloadCode site) hRange hArray entry ht⟩
  obtain ⟨_, _, he, ⟨bs, _, rfl, _⟩, _⟩ := hn.continuing_at_nonempty (by
    rintro e ⟨_, _, _, hBad⟩
    cases hBad) hr hMore
  exact ⟨bs, by simpa only [ht.1] using he⟩

/-- Rebuild the decoded signed-word return from its exact local bytes. -/
theorem scratchReloadReturn {page : Nat} (hPage : page < 2^31)
    (site : ScratchReloadSite) {t : TState} {F : List (Nat × Value)}
    (ht : At t site.pc F) :
    afterAccessLoad t (.sign 64) 32 [site.destination] ((b32 page).toBytes.map some) =
      next (setReg t site.destination (b64 page)) := by
  let word := b32 page
  have hRebuild := rebuild_scalar (v := word) (show 0 < 4 by decide) rfl
  have h64 : page < 2 ^ 64 := by omega
  have h32 : page < 2 ^ 32 := by omega
  have hState :
      afterAccessLoad t (.sign 64) 32 [site.destination]
        (word.toBytes.map some) =
      next (setReg t site.destination (b64 page)) := by
    unfold afterAccessLoad
    rw [hRebuild]
    have hMod : page % 4294967296 = page := Nat.mod_eq_of_lt h32
    have hCmp : page < 2147483648 := hPage
    simp [extendLoaded, word, b32, b64, Value.bitPattern, MemExt.extendBits, toSigned,
      toNat_ofNat_lt h64, hMod, hCmp, truncBits_ofNat h64 (by decide),
      bind, Except.bind, pure, Except.pure, ht.2.1, ht.2.2.1, setRegs, next, setReg]
  exact hState

section
variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {g w i page : Nat} (hwi : w < i)
    (hPage : page < 2 ^ 31) (site : ScratchReloadSite) (hCode : ScratchReloadCode site)
    (hRange : 174 ≤ site.pc ∧ site.pc < 1906) (hArray : ¬ site.array.val < 2) (entry : Fin 2)
    {t : TState}
    (ht : At t site.pc [(site.base, b64 (l.localBase + kvLocalOffset site.array entry))])
include hp hX hwi hPage site hCode hRange hArray entry ht

/-- The K/V page and row reloads recover each lane's latest scratch word, from the
actual event and the kernel's exclusive thread ownership of local memory. -/
theorem scratchWordReloadObservedAtInPrefix {ending : Option TState}
    (hRun : Run kernel Assumptions.all l g t ((X.tr g).drop i) ending)
    (hMore : (X.tr g).drop i ≠ [])
    (hStore : X.get (g, w) = some ⟨site.store,
      .wr (scratchReloadAccess l g site entry) (b32 page).toBytes⟩)
    (hLast : ∀ k < 4, ∀ j dst, X.Access (g, j) dst true →
      dst.Covers ((scratchReloadAccess l g site entry).loc.at k) → j ≤ w ∨ i < j) :
    X.get (g, i) = some ⟨site.pc,
      .rd (scratchReloadAccess l g site entry) ((b32 page).toBytes.map some)⟩ ∧
      At (next (setReg t site.destination (b64 page)))
        (site.pc + 1) [(site.destination, b64 page)] ∧
      Run kernel Assumptions.all l g
        (next (setReg t site.destination (b64 page)))
        ((X.tr g).drop (i + 1)) ending := by
  let acc := scratchReloadAccess l g site entry
  let word := b32 page
  have hNext : Next kernel Assumptions.all l g t t
      (.read acc (afterAccessLoad t (.sign 64) 32 [site.destination])) :=
    ⟨.refl, scratchReloadTemplate hp site hCode hRange hArray entry ht⟩
  obtain ⟨_, _, he, ⟨bs, hLen, rfl, hu⟩, hTail⟩ := hNext.continuing_at_nonempty (by
    rintro e ⟨_, _, _, hBad⟩
    cases hBad) hRun hMore
  obtain rfl := Option.some.inj hu
  rw [ht.1] at he
  have hr : X.Reads (g, i) acc bs := ⟨site.pc, he⟩
  have hw : X.Writes (g, w) acc word.toBytes := ⟨site.store, hStore⟩
  have hWord : bs = word.toBytes.map some := by
    apply List.ext_getElem?
    intro k
    by_cases hk : k < 4
    · have hByte := local_read_byte_of_last_write hX hr hw (k := k) hk
        (Acc.covers_at hk) hwi (fun _ _ _ hWr hCov => localWriteOwner hX hWr rfl hCov) (hLast k hk)
      have hTo : k < word.toBytes.length := by
        simpa [word, b32, Value.toBytes, Value.bytes] using hk
      rw [hByte, List.getElem?_map]
      simp only [wbyte, Loc.at, Nat.add_sub_cancel_left]
      rw [List.getElem?_eq_getElem hTo]
      rfl
    · have hK : bs.length = 4 := hLen
      rw [List.getElem?_eq_none (by omega : bs.length ≤ k)]
      apply Eq.symm
      apply List.getElem?_eq_none
      simpa [word, b32, Value.toBytes, Value.bytes] using Nat.le_of_not_gt hk
  subst bs
  have hState := scratchReloadReturn hPage site ht
  rw [hState] at hTail
  refine ⟨he, ?_, hTail⟩
  have ht' : At t site.pc [] := ht.mono trivial
  exact ht'.set (v := b64 page) (by simp)

end

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {g w i page : Nat} (hwi : w < i)
    (hPage : page < 2 ^ 31) (site : Fin 4) (entry : Fin 2) {t : TState}
    (ht : At t (scratchReloadSite site).pc
      [((scratchReloadSite site).base, b64
        (l.localBase + kvLocalOffset (scratchReloadSite site).array entry))])
include hp hX hwi hPage site entry ht

/-- The K/V page and row reloads recover each lane's latest scratch word, from the
actual event and the kernel's exclusive thread ownership of local memory. -/
theorem scratchWordReloadObservedInPrefix {ending : Option TState}
    (hRun : Run kernel Assumptions.all l g t ((X.tr g).drop i) ending)
    (hMore : (X.tr g).drop i ≠ [])
    (hStore : X.get (g, w) = some ⟨(scratchReloadSite site).store,
      .wr (scratchWordAccess l g site entry) (b32 page).toBytes⟩)
    (hLast : ∀ k < 4, ∀ j dst, X.Access (g, j) dst true →
      dst.Covers ((scratchWordAccess l g site entry).loc.at k) → j ≤ w ∨ i < j) :
    X.get (g, i) = some ⟨(scratchReloadSite site).pc,
      .rd (scratchWordAccess l g site entry) ((b32 page).toBytes.map some)⟩ ∧
      At (next (setReg t (scratchReloadSite site).destination (b64 page)))
        ((scratchReloadSite site).pc + 1) [((scratchReloadSite site).destination, b64 page)] ∧
      Run kernel Assumptions.all l g
        (next (setReg t (scratchReloadSite site).destination (b64 page)))
        ((X.tr g).drop (i + 1)) ending :=
  scratchWordReloadObservedAtInPrefix hp hX hwi hPage (scratchReloadSite site)
    (scratchReloadCode site) (by fin_cases site <;> decide) (by fin_cases site <;> decide)
    entry ht hRun hMore hStore hLast

end
end PTX.Kernels.TmlFa4Fwd.Loader
