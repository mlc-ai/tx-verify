-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0
import Lemmas.Flow.LoadShared

@[expose] public section

/-! # Optional launch reads

The sink and runtime-length sites read a single four-byte launch word.
The read-only assumption identifies those bytes in any consistent execution.
-/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.LaunchReads
open PTX PTX.Proof PTX.Flow
open Wg0 (eOf)

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}

/-- A selected non-coherent read at the specified global byte address. -/
def ReadsLaunchWord (e : Event) (addr : Nat) (bs : List (Option Byte)) : Prop :=
  e.kind = .nc {loc := ⟨.global, 0, addr⟩, size := 4} bs ∧ ncLoads.contains e.pc = true

/-- The initial bytes of a known word are exactly those in the selected non-coherent record. -/
theorem rebuild_word {X : Execution} {i : EvId} {e : Event} {addr n : Nat}
    {bs : List (Option Byte)} (hX : Consistent L kernel Assumptions.all mem0 X)
    (hget : X.get i = some e) (hr : ReadsLaunchWord e addr bs)
    (hmem : ∀ k < 4, mem0 ⟨.global, 0, addr + k⟩ = some (some (word32Byte n k))) :
    rebuild 3 bs = .ok (b32 n) := by
  have hc := hX.asm Assumptions.ncReadOnly (by simp [Assumptions.all])
  rcases e with ⟨pc, kind⟩
  obtain ⟨he, hsite⟩ := hr
  change kind = _ at he
  subst kind
  obtain ⟨hlen, hbytes⟩ := hc i pc _ bs hget hsite
  have heq : bs = (b32 n).toBytes.map some := by
    apply List.ext_getElem?
    intro k
    by_cases hk : k < 4
    · have hv := hbytes k hk _ (hmem k hk)
      simp only [Execution.initialByte, Option.getD_some, Loc.at] at hv
      rw [hv]
      simp [Value.toBytes, b32, word32Byte, List.getElem?_range hk, Value.bytes]
    · have hb : bs.length = 4 := hlen
      rw [List.getElem?_eq_none (by omega)]
      symm
      apply List.getElem?_eq_none
      simpa [Value.toBytes, b32, Value.bytes] using Nat.le_of_not_gt hk
  rw [heq]
  exact rebuild_scalar (show 0 < 4 by decide) rfl

section
variable {X : Execution} {i : EvId} {e : Event} {ptr : Nat} {bs : List (Option Byte)}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
include hpre hX

/-- A selected main-length read rebuilds the batch's specified length word. -/
theorem rebuild_main (hb : eOf L g < P.b) (hp : P.topkLenBase = some ptr) (hget : X.get i = some e)
    (hr : ReadsLaunchWord e (ptr + 4 * eOf L g) bs) :
    rebuild 3 bs = .ok (b32 (P.topkLen (eOf L g))) := by
  have hm := hpre.paramTopkLen
  rw [hp] at hm
  exact rebuild_word hX hget hr fun k hk => by
    simpa [Nat.add_assoc] using (hm.2.2 (eOf L g) hb k hk).1

/-- A selected extra-length read rebuilds the batch's specified extra length word. -/
theorem rebuild_extra (hb : eOf L g < P.b) (hp : P.extraTopkLenBase = some ptr)
    (hget : X.get i = some e) (hr : ReadsLaunchWord e (ptr + 4 * eOf L g) bs) :
    rebuild 3 bs = .ok (b32 (P.extraTopkLen (eOf L g))) := by
  have hm := hpre.paramExtraTopkLen
  rw [hp] at hm
  exact rebuild_word hX hget hr fun k hk => by
    simpa [Nat.add_assoc] using (hm.2.2 (eOf L g) hb k hk).1

/-- A selected sink read rebuilds a finite word carrying the specified head's sink. -/
theorem rebuild_sink (hp : P.sinkBase = some ptr) (hget : X.get i = some e)
    (hr : ReadsLaunchWord e (ptr + 4 * Wg0.head L g) bs) :
    ∃ v s, rebuild 3 bs = .ok v ∧ P.sink (Wg0.head L g) = some s ∧
      valFloat .f32 v = .ok s := by
  have hm := hpre.paramSink
  rw [hp] at hm
  obtain ⟨s, bits, hs, hbits, hbytes, hdecode⟩ := hm.2.2 _ (Wg0.head_lt L g)
  refine ⟨b32 bits, s, rebuild_word hX hget hr (fun k hk => by
    simpa [Nat.add_assoc] using hbytes k hk), hs, ?_⟩
  obtain ⟨q, hq, hqs⟩ := Option.map_eq_some_iff.mp hdecode
  rw [← hqs]
  exact valFloat_b32 (by omega) hq
end

private def readOp (ty : DType) (base dst : Nat) : MemAccess :=
  {kind := .load, space := some .global, sem := .weak, elem := ty, nc := true
   addr := ⟨.reg base 64, 0⟩, dsts := [some dst]}

private theorem observes_word {d : Wg0.D} {ty : DType} {base dst addr : Nat}
    {e : Event} {o : Option TState}
    (hf : (Wg0.code P L g).toMachine.Fired (some d) e o)
    (hc : kernel.code[d.site.pc]? = some ⟨none, .mem (readOp ty base dst)⟩)
    (hw : ty.width = 32) (hr : (readOp ty base dst).rule = some .threadAccess)
    (hsize : d.site.elems = 1) (hreg : base ∈ (Flow.live d.site.pc).filter Wg0.tracked.contains)
    (hval : Wg0.valueOf P L g d base = b64 addr)
    (hword : addr < 2 ^ 64) (halign : addr % 4 = 0) (hnc : ncLoads.contains d.site.pc = true) :
    ∃ bs, ReadsLaunchWord e addr bs := by
  obtain ⟨t, ht, hf⟩ := hf
  change (Wg0.code P L g).AtD d t ∧ Wg0.Inv P L g d at ht
  change Fires t.pc (match kernel.code[d.site.pc]? with
    | some ins => eventTmpl Assumptions.all L g t ins.op
    | none => .ub .pcOutOfRange) e o at hf
  have hpc : t.pc = d.site.pc := ht.1.1
  rw [hc] at hf
  change Fires t.pc (eventTmpl Assumptions.all L g t (.mem (readOp ty base dst))) e o at hf
  have hsub : t.sub = 0 := by
    have hi := ht.2.subLt
    rw [hsize] at hi
    have hs : d.sub = 0 := by omega
    exact ht.1.2.1.trans hs
  have hbase := Wg0.reg_value ht.1 hreg
  rw [hval] at hbase
  have hnc' : Assumptions.all.any (·.ncLoads t.pc) = true := by
    rw [hpc]
    exact List.any_eq_true.mpr ⟨Assumptions.ncReadOnly, by simp [Assumptions.all], hnc⟩
  have htmpl := loadTmpl_global_nc (A := Assumptions.all) (L := L) (g := g) (t := t)
    (d := dst) (base := base) (w := 32) hsub hbase hword (by decide) halign hnc'
  rw [eventTmpl, memTmpl_direct_weakLoad (sp := .global) (base := base) (w := 64)
    hr rfl rfl rfl rfl] at hf
  change Fires t.pc (loadTmpl Assumptions.all L g t .global true ty.width [dst] base 0) e o at hf
  rw [hw, htmpl] at hf
  obtain ⟨bs, _, he, _⟩ := hf
  exact ⟨bs, congrArg Event.kind he, by rw [he]; exact hpc ▸ hnc⟩

/-- The WG0 main-length site reads the supplied pointer at the current batch's word. -/
theorem fired_main {d : Wg0.D} {e : Event} {o : Option TState} {ptr : Nat}
    (hpre : Pre P L mem0) (hb : eOf L g < P.b) (hp : P.topkLenBase = some ptr)
    (hd : d.site = .lenOrig) (hf : (Wg0.code P L g).toMachine.Fired (some d) e o) :
    ∃ bs, ReadsLaunchWord e (ptr + 4 * eOf L g) bs := by
  have hspan := (hpre.topkLenAddressable ptr hp).2.2
  have hptr := hpre.topkLenBaseLt ptr hp
  have hoff : ptr + 4 * eOf L g < 2 ^ 64 := by omega
  have halign := Thread.paramAddr_mod4 (Thread.paramWord_80_mod4 hpre) g
  have hword := Thread.paramWord_80_some hpre hp
  rw [Nat.mod_eq_of_lt hptr] at hword
  change (Thread.paramWord L 80 8 + 4 * eOf L g) % 2 ^ 64 % 4 = 0 at halign
  rw [hword, Nat.mod_eq_of_lt hoff] at halign
  have hc : kernel.code[d.site.pc]? = some ⟨none, .mem (readOp (.int .s 32) 3140 2881)⟩ := by
    rw [hd]
    exact Flow.code_168
  refine observes_word hf hc rfl rfl (by rw [hd]; rfl) (by rw [hd]; decide +kernel)
    ?_ hoff halign (by rw [hd]; decide +kernel)
  change b64 ((Thread.paramWord L 80 8 + 4 * eOf L g) % 2 ^ 64) = _
  rw [hword, Nat.mod_eq_of_lt hoff]

/-- The WG0 extra-length site reads the supplied pointer at the current batch's word. -/
theorem fired_extra {d : Wg0.D} {e : Event} {o : Option TState} {ptr : Nat}
    (hpre : Pre P L mem0) (hb : eOf L g < P.b) (hp : P.extraTopkLenBase = some ptr)
    (hd : d.site = .lenExtra) (hf : (Wg0.code P L g).toMachine.Fired (some d) e o) :
    ∃ bs, ReadsLaunchWord e (ptr + 4 * eOf L g) bs := by
  have hspan := (hpre.extraTopkLenAddressable ptr hp).2.2
  have hptr := hpre.extraTopkLenBaseLt ptr hp
  have hoff : ptr + 4 * eOf L g < 2 ^ 64 := by omega
  have halign := Thread.paramAddr_mod4 (Thread.paramWord_144_mod4 hpre) g
  have hword := Thread.paramWord_144_some hpre hp
  rw [Nat.mod_eq_of_lt hptr] at hword
  change (Thread.paramWord L 144 8 + 4 * eOf L g) % 2 ^ 64 % 4 = 0 at halign
  rw [hword, Nat.mod_eq_of_lt hoff] at halign
  have hc : kernel.code[d.site.pc]? = some ⟨none, .mem (readOp (.int .s 32) 3142 2882)⟩ := by
    rw [hd]
    exact Flow.code_181
  refine observes_word hf hc rfl rfl (by rw [hd]; rfl) (by rw [hd]; decide +kernel)
    ?_ hoff halign (by rw [hd]; decide +kernel)
  change b64 ((Thread.paramWord L 144 8 + 4 * eOf L g) % 2 ^ 64) = _
  rw [hword, Nat.mod_eq_of_lt hoff]

/-- The WG0 sink site reads the supplied pointer at the current head's word. -/
theorem fired_sink {d : Wg0.D} {e : Event} {o : Option TState} {ptr : Nat}
    (hpre : Pre P L mem0) (hp : P.sinkBase = some ptr)
    (hd : d.site = .sink) (hf : (Wg0.code P L g).toMachine.Fired (some d) e o) :
    ∃ bs, ReadsLaunchWord e (ptr + 4 * Wg0.head L g) bs := by
  have hspan := (hpre.sinkAddressable ptr hp).2.2
  have hptr := hpre.sinkBaseLt ptr hp
  have hhead := Wg0.head_lt L g
  have hoff : ptr + 4 * Wg0.head L g < 2 ^ 64 := by omega
  have hword := Wg0.paramWord_88_some hpre hp
  change Thread.paramWord L 88 8 = ptr % 2 ^ 64 at hword
  rw [Nat.mod_eq_of_lt hptr] at hword
  have hm := hpre.paramSink
  rw [hp] at hm
  have hal := hm.2.1
  have halign : (ptr + 4 * Wg0.head L g) % 4 = 0 := by omega
  have hc : kernel.code[d.site.pc]? = some ⟨none, .mem (readOp (.float .f32) 3138 932)⟩ := by
    rw [hd]
    exact Flow.code_156
  refine observes_word hf hc rfl rfl (by rw [hd]; rfl) (by rw [hd]; decide +kernel)
    ?_ hoff halign (by rw [hd]; decide +kernel)
  change b64 ((Thread.paramWord L 88 8 + 4 * Wg0.head L g) % 2 ^ 64) = _
  rw [hword, Nat.mod_eq_of_lt hoff]

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.LaunchReads
