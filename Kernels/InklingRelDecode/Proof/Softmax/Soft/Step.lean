-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Common.ValueThread
import Kernels.InklingRelDecode.Proof.Softmax.Export.Value
public import Kernels.InklingRelDecode.Proof.Common.ValueFollow
public import Kernels.InklingRelDecode.Proof.Common.Where
import Kernels.InklingRelDecode.Proof.Common.ValueSound
import Kernels.InklingRelDecode.Proof.Softmax.LateStep

/-! # The value thread's state at a softmax site and its predecessor

A state of the value thread at a softmax site is the prologue's word, the entry and the softmax
value machine's state (`softDState`); the state before it is the prologue's last state (and the
softmax's state is the empty one) or a softmax state with a value-machine step. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Soft
open PTX PTX.Proof PTX.Flow Control Data

variable {Q : Params} {L : Launch} {g : Nat}

/-- The value thread state at a softmax site. -/
public abbrev softDState (w : Value) (ent : Control.Entry) (y : Data.D) (n : Cls → Nat) :
    (threadD Q L g).D := (.inr ⟨.inl (.prologue w), .inr ⟨ent, .inl y⟩⟩, n)

public theorem softD_shape {s : (threadD Q L g).D} {w : Value} {ent : Control.Entry}
    {c : Control.D} {n : Cls → Nat} (h : eraseThread Q L g s = softState w ent c n) :
    ∃ y : Data.D, y.c = c ∧ s = softDState w ent y n := by
  obtain ⟨a, m⟩ := s
  rcases a with b | ⟨j | r, x⟩
  · cases h
  · cases j with
    | dispatch w' x' => cases h
    | prologue w' =>
      rcases x with d | ⟨en, y⟩
      · cases h
      · rcases y with y | ⟨u, y⟩
        · cases h
          exact ⟨y, rfl, rfl⟩
        · cases h
  · cases h

public theorem softD_pred {s : (threadD Q L g).D} {e : Event} {w : Value}
    {ent : Control.Entry} {y : Data.D} {n : Cls → Nat}
    (hs : (threadD Q L g).next s e = some (some (softDState w ent y n))) :
    (y = {} ∧ ∃ (d : Prologue.Data.D) (cnt : Cls → Nat), s = proDState w d cnt) ∨
      ∃ (old : Data.D) (cnt : Cls → Nat), s = softDState w ent old cnt ∧
        Data.succ ent L g old e = some (some y) := by
  obtain ⟨a, b⟩ := Code.counted_next_some hs
  obtain ⟨s0, cnt⟩ := s
  rcases s0 with start | ⟨r, old⟩
  · change (Startup.succ L g start e).map _ = _ at a
    rcases hn : Startup.succ L g start e with _ | _ | t <;> rw [hn] at a <;>
      try solve | cases a
    simp only [Option.map_some, Option.some.injEq] at a
    obtain ⟨site, tm, x, word⟩ := t
    cases site <;> try contradiction
    rename_i entry
    cases entry <;> cases a
  change ((Code.withStubs (fragD Q L g) Startup.Entry.pc r).next old e).map _ = _ at a
  rcases hn : (Code.withStubs (fragD Q L g) Startup.Entry.pc r).next old e with _ | _ | t <;>
    rw [hn] at a <;> try solve | cases a
  simp only [Option.map_some, Option.some.injEq] at a
  cases a
  rcases old with old | ⟨ent', old⟩
  · change (Prologue.Data.succ Q L g old e).map _ = _ at hn
    rcases hv : Prologue.Data.succ Q L g old e with _ | _ | dn <;> rw [hv] at hn <;>
      try solve | cases hn
    simp only [Option.map_some, Option.some.injEq] at hn
    unfold Code.enter at hn
    split at hn <;> cases hn
    exact .inl ⟨rfl, old, cnt, rfl⟩
  · rcases old with old | ⟨u, old⟩
    · change ((softDCode ent' L g).next (Sum.inl old) e).map
        (Option.map fun d' => (Sum.inr ⟨ent', d'⟩ : (dataDCode Q L g w).D)) = _ at hn
      rcases hv : (softDCode ent' L g).next (Sum.inl old) e with _ | _ | dn <;> rw [hv] at hn <;>
        try solve | cases hn
      simp only [Option.map_some, Option.some.injEq] at hn
      cases hn
      change (Data.succ ent L g old e).map _ = _ at hv
      rcases hs : Data.succ ent L g old e with _ | _ | dn' <;> rw [hs] at hv <;>
        try solve | cases hv
      simp only [Option.map_some, Option.some.injEq] at hv
      unfold Code.enter at hv
      split at hv <;> cases hv
      exact .inr ⟨old, cnt, rfl, hs⟩
    · change ((softDCode ent' L g).next (Sum.inr ⟨u, old⟩) e).map
        (Option.map fun d' => (Sum.inr ⟨ent', d'⟩ : (dataDCode Q L g w).D)) = _ at hn
      rcases hv : (softDCode ent' L g).next (Sum.inr ⟨u, old⟩) e with _ | _ | dn <;>
        rw [hv] at hn <;> try solve | cases hn
      simp only [Option.map_some, Option.some.injEq] at hn
      cases hn
      change ((epilogueDCode _ L g).next old e).map _ = _ at hv
      rcases hv' : (epilogueDCode _ L g).next old e with _ | _ | z <;> rw [hv'] at hv <;>
        cases hv


end PTX.Kernels.InklingRelDecode.Proof.Softmax.Soft
