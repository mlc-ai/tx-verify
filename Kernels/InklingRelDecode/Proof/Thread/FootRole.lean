-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.WCompAll
public import Kernels.InklingRelDecode.Proof.Thread.ProBOps
public import Lemmas.Flow.LoadShared

@[expose] public section

/-!
# The event of the worker's read of its role byte

`Worker.Site.ldRole` is `ld.shared.b8 %r74, [%r75 + 213332]` with `%r75` the shared base plus the
warp index: a one-byte read at `sharedBase + 213332 + warp` of the thread's CTA. For the warps 4
to 7 that is the byte `213336 + (warp - 4)` of the role table, the four bytes of
`[sharedBase + 213336, sharedBase + 213340)`. `shape_ldRole` says so.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Worker
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {A : List Assumption} {L : Launch} {g : Nat} {t u : TState} {pc : Nat} {e : Event}

/-- `ld.shared.b8 %r d, [%r base + off]` as the decoder gives it: the byte is zero-extended to
32 bits, so the access has no direct location rule and is located by `accessLoc`. -/
def ldByte (base off d : Nat) : MemAccess :=
  { kind := .load, space := some (.shared .cta), sem := .weak, elem := .int .b 8,
    ext := .zero 32, addr := { base := .reg base 32, off := (off : Int) }, dsts := [some d] }

/-- **A one-byte zero-extending shared load at `a + off`** reads one byte there. -/
theorem fires_ld_shared8 {d base a off : Nat} (hr : t.regs base = some (b32 a))
    (ha : a + off < 2 ^ 32) (hs : t.sub = 0)
    (hf : Fires pc (eventTmpl A L g t (.mem (ldByte base off d))) e (some u)) :
    ∃ ac bs, e = ⟨pc, .rd ac bs⟩ ∧ ac.loc = ⟨.shared, g / L.block, a + off⟩ ∧ ac.size = 1 := by
  have hr' : (ldByte base off d).rule = some .threadAccess := by rfl
  have hl : (ldByte base off d).locSpace? = none := by
    simp [MemAccess.locSpace?, ldByte]
  simp only [eventTmpl, memTmpl, hr', hl] at hf
  simp only [accessTmpl] at hf
  rw [accessAcc_of_weak rfl] at hf
  have hb : readBits L g t 32 (.reg base) = .ok (BitVec.ofNat 64 a) := readBits_b32 hr (by omega)
  have ha32 : a < 2 ^ 32 := by omega
  simp only [ldByte, accessLoc, readReg, hr, b32, bind, Except.bind, pure, Except.pure, hb,
    BitVec.toNat_ofNat] at hf
  have hw : wrapAddr 32 (BitVec.ofNat 64 a) (off : Int) = a + off := by
    simp only [wrapAddr, BitVec.ofInt_natCast, ← BitVec.ofNat_add,
      ProA.truncBits_ofNat 32 _ (by decide), BitVec.toNat_ofNat]
    omega
  have hmod : a % 2 ^ 64 < 2 ^ 32 := by omega
  simp only [hmod, ↓reduceIte, hw, elemAcc, hs, Loc.at, DType.width] at hf
  have hg : (false || ({ } : CacheHints).globalOnly || 1 == 8 || 1 == 4 && 8 == 64) = false := by
    decide
  simp only [hg, Bool.false_and, Bool.false_eq_true, ↓reduceIte] at hf
  simp only [Nat.reduceDiv, Nat.mul_one, Nat.mod_one, Nat.reduceMul, Nat.add_zero] at hf
  simp only [show ¬ (1 = 0 ∨ 0 ≠ 0) by decide, ↓reduceIte, pure, Except.pure, Fires] at hf
  obtain ⟨bs, -, he, -⟩ := hf
  exact ⟨_, bs, he, rfl, rfl⟩

theorem ldRole_code : kernel.code[2340]? = some ⟨none, .mem (ldByte 536 213332 535)⟩ :=
  Flow.code_load_203

/-- The address register of the role byte read holds the shared base plus the warp index. -/
theorem roleAddr_eq (hb : L.sharedBase + 213332 + 8 < 2 ^ 32) (g : Nat) (hw : warpOf L g < 8) :
    roleAddr L g = b32 (L.sharedBase + warpOf L g) := by
  unfold roleAddr
  have e1 : Loader.baseW L = BitVec.ofNat 64 (L.sharedBase % 2 ^ 32) := by
    unfold Loader.baseW
    rw [Nat.add_zero, ProA.truncBits_ofNat 32 _ (by decide)]
  have e2 : Loader.addW = ProA.wAdd32 := rfl
  rw [e1, e2, ProA.wAdd32_ofNat]
  unfold b32
  congr 2
  omega

variable {Q : Params} {mem0 : Mem0}

/-- **The worker's read of its role byte.** One byte at `sharedBase + 213332 + warp` of the
thread's CTA (the byte `213336 + (warp - 4)` of the role table for the warps 4 to 7). -/
theorem shape_ldRole (hpre : Pre Q L mem0) {w : D} {e : Event} {u : TState} (hg : g % L.block < 256)
    (hs : w.site = .ldRole)
    (hF : (WComp.code L g Q).toMachine.Fired (some (.worker w)) e (some u)) :
    ∃ ac bs, e = ⟨Site.ldRole.pc, .rd ac bs⟩ ∧
      ac.loc = ⟨.shared, g / L.block, L.sharedBase + 213332 + warpOf L g⟩ ∧ ac.size = 1 := by
  obtain ⟨t, hgood, hfire⟩ := hF
  obtain ⟨hat, hinv⟩ := hgood
  have hinv' : (WComp.code L g Q).inv (.worker w) := hinv
  have hwarp : warpOf L g < 8 := by
    unfold warpOf
    rw [hpre.block] at hg ⊢
    omega
  have hpc : Site.pc w.site = 2340 := by rw [hs]; rfl
  have hc' : kernel.code[2340]? = some ⟨none, .mem (ldByte 536 213332 535)⟩ := ldRole_code
  have hf : Fires 2340 (eventTmpl Loader.asms L g t
      (Instr.op ⟨none, .mem (ldByte 536 213332 535)⟩)) e (some u) := by
    have := hfire
    simp only [Code.toMachine, Code.tmpl] at this
    have hat' : t.pc = 2340 := by
      have : t.pc = w.site.pc := hat.1
      rw [this, hpc]
    rw [hat'] at this
    obtain ⟨ins, hc, -, -⟩ := (WComp.stepAt hpre (.worker w)).site hinv'
    have hc1 : kernel.code[WComp.pc (WComp.WSt.worker w)]? = some ins := hc
    have hc2 : kernel.code[2340]? = some ins := by simpa [WComp.pc, hpc] using hc1
    obtain rfl := Option.some.inj (hc'.symm.trans hc2)
    have hc3 : kernel.code[WComp.pc (WComp.WSt.worker w)]? =
        some ⟨none, .mem (ldByte 536 213332 535)⟩ := by
      simpa [WComp.pc, hpc] using hc'
    rw [hc3] at this
    exact this
  have hsb : L.sharedBase + 213332 + 8 < 2 ^ 32 := by
    have := hpre.sharedRange
    unfold sharedBytes at this
    omega
  have hr : t.regs 536 = some (b32 (L.sharedBase + warpOf L g)) := by
    have h5 : (536, valueOf L g w 536) ∈ WComp.facts L g (.worker w) := by
      show (536, valueOf L g w 536) ∈ Worker.factsAt L g w.site.pc w
      rw [hpc]
      exact Flow.mem_factsFrom (by decide +kernel)
    have := holds_mem hat.2.2.2.2 h5
    rw [this]
    simp only [valueOf]
    simp [roleAddr_eq hsb g hwarp]
  have hsub : t.sub = 0 := by
    have : t.sub = WComp.sub (.worker w) := hat.2.1
    simpa [WComp.sub] using this
  obtain ⟨ac, bs, he, hl, hsz⟩ := fires_ld_shared8 hr (by omega) hsub hf
  refine ⟨ac, bs, ?_, ?_, hsz⟩
  · rw [he]; simp [Site.pc]
  · rw [hl]; congr 1; omega

end
end PTX.Kernels.InklingRelDecode.Proof.Worker
