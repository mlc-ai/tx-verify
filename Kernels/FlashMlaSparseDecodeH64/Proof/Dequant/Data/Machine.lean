-- SPDX-License-Identifier: Apache-2.0
-- domain: valid-rows
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.Control.Machine
public import Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.Data.Chunk
public import Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.Data.ScaleVals
public import Lemmas.Flow.DataOver

@[expose] public section

/-! # Warpgroup 2 as a data machine

The control machine (`Control.code`) with the data a row reads: the sixteen scale bytes of the
row (`sc`, from the four words of its scale load, `scWord`) and the raw word of each step
(`ws`), from the last raw load of that step. A step is the control step; on the data it adds:

* at the last element of a scale load, the scale word from the four elements, followed only when
  every element is a 32-bit word and every scale byte is below 255 (`ScOk`);
* at raw load `s`, the word of step `s` replaced, followed only when it is a 64-bit word of
  valid e4m3 bytes (`RawOk`).

The state keeps its data valid (`scOk`, `wsOk`): the start's zeros are, and the guards keep them.

The guards are on data only, so the machine lies over the control machine (`over`). Its data facts
(`dF`) are what the coming float runs read: the row's scale halfwords (`scaleFacts`) from the
first raw load to the last store but one; at a raw load `s + 1 ≥ 1` the halfwords of raw word
`s`; at a store `s` the chunk it stores and, before the last, the next raw word. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.Data
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32
open PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Numeric.Dequant
open Classical

noncomputable section

/-- Every scale byte of the row is below 255 (no NaN scale). -/
def ScOk (sc : Nat) : Prop := ∀ i < 16, byteAt sc i < 255

theorem scOk_zero : ScOk 0 := fun i _ => by simp [byteAt]

/-- A raw word: valid e4m3 bytes, 64 bits. -/
def WordOk (x : Nat) : Prop := RawOk x ∧ x < 2 ^ 64

theorem wordOk_zero : WordOk 0 := ⟨fun i _ => by simp [byteAt], by norm_num⟩

/-- A state: the control state, the row's scale bytes and the raw word of each step, valid. -/
structure D where
  c : Control.D
  sc : Nat
  ws : Nat → Nat
  scOk : ScOk sc
  wsOk : ∀ i, WordOk (ws i)

/-- The bits of a loaded value of `n` bits. -/
def wordOf (n : Nat) : Value → Option Nat
  | .bits m x => if m = n ∧ x.toNat < 2 ^ n then some x.toNat else none
  | _ => none

/-- The value a load's bytes rebuild to (as the control machine reads it). -/
def loadVal (bs : List (Option Byte)) : Value := (rebuild 3 bs).toOption.getD (.pred false)

/-- The scale word of four loaded elements, if each is a 32-bit word and the bytes are valid. -/
def scaleOf : List Value → Option {sc // ScOk sc}
  | [v0, v1, v2, v3] =>
    match wordOf 32 v0, wordOf 32 v1, wordOf 32 v2, wordOf 32 v3 with
    | some w0, some w1, some w2, some w3 =>
      if h : ScOk (scWord w0 w1 w2 w3) then some ⟨_, h⟩ else none
    | _, _, _, _ => none
  | _ => none

/-- The raw word of a load, if it is a 64-bit word of valid bytes. -/
def rawOf (v : Value) : Option {x // WordOk x} :=
  match wordOf 64 v with
  | some x => if h : WordOk x then some ⟨x, h⟩ else none
  | none => none

theorem update_ok {ws : Nat → Nat} (h : ∀ i, WordOk (ws i)) (s : Nat) (x : {x // WordOk x}) :
    ∀ i, WordOk (Function.update ws s x.1 i) := fun i => by
  by_cases e : i = s
  · subst e; rw [Function.update_self]; exact x.2
  · rw [Function.update_of_ne e]; exact h i

/-- The data after the control step to `c'` on event `e` (`none`: no longer followed). -/
def dataNext (d : D) (c' : Control.D) (e : Event) : Option D :=
  match d.c.site, e.kind with
  | .scale _, .rd _ bs =>
    if d.c.el + 1 < 4 then some { d with c := c' }
    else (scaleOf (d.c.acc ++ [loadVal bs])).map fun sc =>
      { d with c := c', sc := sc.1, scOk := sc.2 }
  | .raw _ s, .rd _ bs =>
    (rawOf (loadVal bs)).map fun x =>
      { d with c := c', ws := Function.update d.ws s.val x.1, wsOk := update_ok d.wsOk s.val x }
  | _, _ => some { d with c := c' }

theorem dataNext_c {d : D} {c' : Control.D} {e : Event} {d' : D}
    (h : dataNext d c' e = some d') : d'.c = c' := by
  unfold dataNext at h
  split at h
  · split at h
    · cases h; rfl
    · obtain ⟨_, -, rfl⟩ := Option.map_eq_some_iff.mp h; rfl
  · obtain ⟨_, -, rfl⟩ := Option.map_eq_some_iff.mp h; rfl
  · cases h; rfl

/-- **The successor**: the control successor, with the data. -/
def succ (P : Params) (L : Launch) (g : Nat) (d : D) (e : Event) : Option (Option D) :=
  match Control.succ P L g d.c e with
  | none => none
  | some none => some none
  | some (some c') => some (dataNext d c' e)

/-! ### The data facts -/

/-- The first scale halfword register of row `r` (`%rs214` for row 0). -/
def scBase (r : Nat) : Nat := 353 + 24 * r
/-- The halfword registers of raw word `s` of row `r`. -/
def halfReg (r s k : Nat) : Nat := 192 + 40 * r + 5 * s + k
/-- The register of raw word `s` of row `r`. -/
def rawReg (r s : Nat) : Nat :=
  if s = 0 then 3837 + 48 * r else if s = 1 then 3841 + 48 * r else 3847 + 6 * (s - 2) + 48 * r
/-- The chunk register of step `s` of row `r`. -/
def chunkReg (r s : Nat) : Nat := 4039 + 8 * r + s

/-- The halfword facts of a raw word. -/
def halfFacts (r s w : Nat) : List (Nat × Value) :=
  [(halfReg r s 0, bits16 (byteAt w 0 + 256 * byteAt w 1)),
    (halfReg r s 1, bits16 (byteAt w 2 + 256 * byteAt w 3)),
    (halfReg r s 2, bits16 (byteAt w 4 + 256 * byteAt w 5)),
    (halfReg r s 3, bits16 (byteAt w 6 + 256 * byteAt w 7))]

/-- The lane's selector of the scale byte (`%p134`: lanes `4–7` of eight take the odd byte). -/
def hiSel (L : Launch) (g : Nat) : Bool := scmpi .gt .u (Control.r55W L g) 3

/-- The scale byte step `s` of a lane multiplies by. -/
def selByte (L : Launch) (g : Nat) (sc s : Nat) : Nat :=
  if hiSel L g then byteAt sc (2 * s + 1) else byteAt sc (2 * s)

/-- The chunk a lane stores at step `s` of a row. -/
def chunkVal (L : Launch) (g : Nat) (d : D) (s : Nat) : Value :=
  dequantChunk (d.ws s) (selByte L g d.sc s)

/-- **The data facts** of a state, by site. -/
def dF (L : Launch) (g : Nat) (d : D) : List (Nat × Value) :=
  match d.c.site with
  | .raw r s =>
    scaleFacts (scBase r) d.sc ++
      (if s.val = 0 then [] else halfFacts r (s.val - 1) (d.ws (s.val - 1)))
  | .store r s =>
    (if s.val < 7 then
      scaleFacts (scBase r) d.sc ++
        [(rawReg r (s.val + 1), .bits 64 (BitVec.ofNat 64 (d.ws (s.val + 1))))]
    else []) ++ [(chunkReg r s, chunkVal L g d s)]
  | _ => []

/-- **Warpgroup 2 as a data machine** (for the warp word `w`, not read). -/
@[reducible] def code (P : Params) (L : Launch) (g : Nat) (w : BitVec 64) :
    Flow.Code kernel Assumptions.all L g where
  D := D
  init := ⟨(Control.code P L g w).init, 0, fun _ => 0, scOk_zero, fun _ => wordOk_zero⟩
  pc := fun d => (Control.code P L g w).pc d.c
  facts := fun d => (Control.code P L g w).facts d.c ++ dF L g d
  sub := fun d => (Control.code P L g w).sub d.c
  acc := fun d => (Control.code P L g w).acc d.c
  inv := fun d => (Control.code P L g w).inv d.c
  next := succ P L g

/-- **The data machine lies over the control machine.** -/
theorem over (P : Params) (L : Launch) (g : Nat) (w : BitVec 64) :
    Code.Over (code P L g w) (Control.code P L g w) D.c (dF L g) where
  pc _ := rfl
  sub _ := rfl
  acc _ := rfl
  inv _ := Iff.rfl
  facts _ := rfl
  next := by
    intro d e d' h
    change succ P L g d e = _ at h
    unfold succ at h
    split at h
    · cases h
    · cases h
    · rename_i c' hc
      cases h' : dataNext d c' e with
      | none => rw [h'] at h; cases h
      | some d'' =>
        rw [h'] at h
        cases h
        exact hc.trans (by rw [dataNext_c h'])
  stop := by
    intro d e h
    change succ P L g d e = _ at h
    unfold succ at h
    split at h
    · assumption
    · cases h
    · cases h

theorem erases (P : Params) (L : Launch) (g : Nat) (w : BitVec 64) :
    Code.Erases (code P L g w) (Control.code P L g w) D.c :=
  (over P L g w).erases rfl

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.Data
