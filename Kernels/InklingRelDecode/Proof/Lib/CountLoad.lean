-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Spec
public import Lemmas.Flow.SharedSym
import Lemmas.Flow.Final

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Lib
open PTX PTX.Flow PTX.Proof

def countLoad (p : Nat) : MemAccess :=
  { kind := .load, space := some (.shared .cta), sem := .weak, elem := .int .b 32,
    addr := ⟨.sharedSym 0, if p=2345 then 212992 else 212996⟩,
    vec := if p=2345 then 2 else 1, dsts := if p=2345 then [some 1905,some 467] else [some 471],
    srcs := [] }

theorem count_load_shape {A L g t p a bs o Q m} (hp : Pre Q L m)
    (site : p=2345 ∨ p=2423)
    (fire : Fires p (eventTmpl A L g t (.mem (countLoad p))) ⟨p,.rd a bs⟩ o) :
    a.loc=⟨.shared,g/L.block,L.sharedBase+(if p=2345 then 212992 else 212996)+4*t.sub⟩ ∧
    a.size=4 := by
  cases o with
  | none => rcases fires_none_ends fire with ⟨_,bad⟩|bad <;> cases bad
  | some u =>
    have lim := hp.sharedRange
    change L.sharedBase+213340≤2^18 at lim
    let off := if p=2345 then 212992 else 212996
    have small : L.sharedBase+0+off < 2^32 := by dsimp [off]; split <;> omega
    have shape := fires_ldv_sharedSym (a := countLoad p) (L := L) (g := g) (A := A) (t := t)
      (pc := p) (e := ⟨p,.rd a bs⟩) (u := u) (o := 0) (off := off)
    obtain ⟨_,_,eq,addr,size,_⟩ := shape (by rcases site with rfl|rfl <;> rfl)
      rfl (by rcases site with rfl|rfl <;> rfl) rfl rfl rfl rfl
      (by rcases site with rfl|rfl <;> rfl) rfl small fire
    cases eq
    exact ⟨addr,size⟩

end PTX.Kernels.InklingRelDecode.Proof.Lib
