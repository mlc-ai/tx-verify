-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Prologue.Strict.Frame
public import Kernels.InklingRelDecode.Proof.Prologue.RefWords

@[expose] public section

/-! # What the strict prologue steps assume of a state and of an event

`Ok`: the state's request words are the launch's (`Known`), its broadcast word, its block-table
words and its query halves have the types the spans read them at. `Wf`: the events of the lane's
loads and shuffles carry such words. The trace-level proofs of `Wf` are in `Strict/Trace.lean`. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Prologue.Strict
open PTX PTX.Proof PTX.Flow Control

/-- The request row of lane `g`. -/
def reqOf (L : Launch) (g : Nat) : Nat := (L.ctaidOf (g / L.block)).get .z

/-- The words a strictly followed state holds. -/
def Ok (Q : Params) (L : Launch) (g : Nat) (d : Data.D) : Prop :=
  Known Q (reqOf L g) d.c ∧ (∃ x, d.c.broadcast = .bits 32 x) ∧
    (∀ b h, ∃ p, d.v.pay b h = .bits 32 p) ∧ ∀ k, (d.v.q k).bytes = 2

theorem Ok.qBytes {Q : Params} {L : Launch} {g : Nat} {d : Data.D} (hk : Ok Q L g d) :
    ∀ k, (d.v.q k).bytes = 2 := by
  obtain ⟨-, -, -, h⟩ := hk
  exact h

/-- The payloads of the events of the prologue's loads and shuffles. -/
def Wf (Q : Params) (L : Launch) (g : Nat) (e : Event) : Prop :=
  (∀ i : Fin 3, e.pc = (Site.ld i).pc → ∀ a bs, e.kind = .rd a bs →
    rebuild 3 bs = .ok (b32 (requestWord Q (reqOf L g) i))) ∧
  (∀ b h, e.pc = (Site.lb b h).pc → ∀ a bs, e.kind = .rd a bs → ∃ p, rebuild 3 bs = .ok (b32 p)) ∧
  (∀ j : Fin 64, e.pc = (Site.ldq j).pc → ∀ a bs, e.kind = .rd a bs →
    ∃ v, rebuild 3 bs = .ok v ∧ v.bytes = 2) ∧
  (∀ b, e.pc = (Site.psh b).pc → ∀ m a b' c recv ok, e.kind = .shfl m a b' c recv ok →
    ∃ p, recv = .bits 32 p)

end PTX.Kernels.InklingRelDecode.Proof.Prologue.Strict
