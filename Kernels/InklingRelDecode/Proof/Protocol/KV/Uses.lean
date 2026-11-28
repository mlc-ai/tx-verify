-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Common.Export.Mbar

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.KV
open PTX MbarRow PTX.MbarRow

inductive Ring where | ready | empty deriving DecidableEq, Repr

def Ring.offset : Ring → Fin 3 → Nat
  | .ready => Iface.kvReady
  | .empty => Iface.kvEmpty

def Ring.obj (r : Ring) (L : Launch) (c : Nat) (s : Fin 3) : Loc :=
  ⟨.shared,c,L.sharedBase + r.offset s⟩

private theorem address {L : Launch} {c g : Nat} {s z : Fin 3} {r f : Ring}
    (h : r.obj L c s = loc L g (f.offset z)) : c = g / L.block ∧ r = f ∧ s = z := by
  obtain ⟨_,hc,ha⟩ := Loc.mk.inj h
  refine ⟨hc,?_⟩
  have hs := s.isLt
  have hz := z.isLt
  cases r <;> cases f <;>
    simp only [Ring.offset,Iface.kvReady,Iface.kvEmpty, Nat.add_left_cancel_iff] at ha
  all_goals first | exact ⟨rfl,Fin.ext (by omega)⟩ | omega

private theorem other {L : Launch} {c g off : Nat} {s : Fin 3} {r : Ring}
    (hi : 213280 ≤ off) (h : r.obj L c s = loc L g off) : False := by
  obtain ⟨_,_,ha⟩ := Loc.mk.inj h
  have hs := s.isLt
  cases r <;> simp only [Ring.offset,Iface.kvReady,Iface.kvEmpty] at ha <;> omega

/-- Exhaustive thread-side uses of the two rings. Prefix quantities refer to the issuing lane. -/
inductive Use (Q : Params) (L : Launch) (X : Execution) (c g k : Nat) (e : Event) :
    Ring → Fin 3 → Prop where
  | init {r s} (pc : ∃ j : Fin 12, e.pc = 134 + 4*j.val)
      (kind : e.kind = .mbInit (r.obj L c s) 1) : Use Q L X c g k e r s
  | preload {s} (pc : e.pc ∈ [193,237,279])
      (kind : Arrive e (Ring.ready.obj L c s) 65536) : Use Q L X c g k e .ready s
  | preloadCopy {s} (pc : e.pc ∈ preloadCopies s)
      (kind : Issue e (Ring.ready.obj L c s) 8192) : Use Q L X c g k e .ready s
  | emptyWait (pc : e.pc = 2374) (warp : g % L.block / 32 = 6)
      (kind : Wait e (Ring.empty.obj L c (slot3 (loaderRound Q L X g k)))
        (1 - loaderRound Q L X g k / 3 % 2)) :
      Use Q L X c g k e .empty (slot3 (loaderRound Q L X g k))
  | arrive (pc : e.pc = 2378) (warp : g % L.block / 32 = 6)
      (kind : Arrive e (Ring.ready.obj L c (slot3 (loaderRound Q L X g k - 1))) 65536) :
      Use Q L X c g k e .ready (slot3 (loaderRound Q L X g k - 1))
  | copy (pc : e.pc ∈ [2389,2391,2394,2396,2404,2406,2410,2412]) (warp : g % L.block / 32 = 6)
      (kind : Issue e (Ring.ready.obj L c (slot3 (loaderRound Q L X g k - 1))) 8192) :
      Use Q L X c g k e .ready (slot3 (loaderRound Q L X g k - 1))
  | readyWait (pc : e.pc = 2462) (warp : g % L.block / 32 = 7)
      (kind : Wait e (Ring.ready.obj L c (slot3 (roundAt X g k 2462)))
        (roundAt X g k 2462 / 3 % 2)) :
      Use Q L X c g k e .ready (slot3 (roundAt X g k 2462))
  | notify (pc : e.pc = 2546) (warp : g % L.block / 32 = 7)
      (kind : Commit e (Ring.empty.obj L c (slot3 (roundAt X g k 2510 - 1)))) :
      Use Q L X c g k e .empty (slot3 (roundAt X g k 2510 - 1))

theorem ring_use {Q L X c g k e r s} (rows : MbarRows Q L X) (hg : g < L.threads)
    (he : X.get (g,k) = some e) (hm : Frame.MbarOf e (Ring.obj r L c s)) :
    Use Q L X c g k e r s := by
  cases mbar_use rows hg he hm with
  | startup _ h => cases h
  | dispatch _ h => cases h
  | prologue _ h =>
    cases h with
    | init j pc _ kind _ _ _ _ _ => exact .init ⟨j,pc⟩ kind
    | preloadArrive z pc hl kind =>
      obtain ⟨_,rfl,rfl⟩ := address (f := .ready) hl
      have hd : ∀ j : Fin 3, ([193,237,279] : List Nat)[j.val]! ∈ [193,237,279] := by decide
      exact .preload (pc ▸ hd _) kind
    | preloadCopy z pc hl kind =>
      obtain ⟨_,rfl,rfl⟩ := address (f := .ready) hl
      exact .preloadCopy pc kind
  | softmax _ h =>
    cases h with
    | pArrive _ _ hl _ => exact (other (by unfold Iface.pReady; omega) hl).elim
    | sWait _ hl _ => exact (other (by simp [Iface.sReady]) hl).elim
    | oWait _ hl _ => exact (other (by decide) hl).elim
  | epilogue _ h =>
    cases h with
    | finalWait _ hl _ => exact (other (by decide) hl).elim
  | loader hw h =>
    cases h with
    | emptyWait pc hl kind =>
      obtain ⟨_,rfl,rfl⟩ := address (f := .empty) hl
      exact .emptyWait pc hw.1 kind
    | readyArrive pc _ hl kind =>
      obtain ⟨_,rfl,rfl⟩ := address (f := .ready) hl
      exact .arrive pc hw.1 kind
    | readyCopy pc _ hl kind =>
      obtain ⟨_,rfl,rfl⟩ := address (f := .ready) hl
      exact .copy pc hw.1 kind
  | mma hw h =>
    cases h with
    | readyWait pc hl kind =>
      obtain ⟨_,rfl,rfl⟩ := address (f := .ready) hl
      exact .readyWait pc hw.1 kind
    | emptyCommit pc hl kind =>
      obtain ⟨_,rfl,rfl⟩ := address (f := .empty) hl
      exact .notify pc hw.1 kind
    | pWait _ hl _ => exact (other (by unfold Iface.pReady; omega) hl).elim
    | sCommit _ hl _ => exact (other (by simp [Iface.sReady]) hl).elim
    | doneCommit _ hl _ => exact (other (by decide) hl).elim
    | finalCommit _ hl _ => exact (other (by decide) hl).elim

end PTX.Kernels.InklingRelDecode.Proof.Protocol.KV
