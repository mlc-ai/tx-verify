-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Clc.ClcEffects
public import Lemmas.Clc.ClcOwnership

@[expose] public section

namespace PTX.Clc
noncomputable section

variable {L : Launch} {i : EvId} {s : Spec} {state : State} {e : Effects}

/-- The notification certifies the matching target's actual 16-byte write. -/
theorem completion_has_write (h : EffectsOk L i s state e)
    {cta : Nat} {m : Loc} {n : Nat} (hc : Completion s e cta m n) :
    ∃ a bs, ResponseWrite s e cta a bs ∧ a.size = 16 ∧ bs.length = 16 := by
  have hw := h.notified cta hc.1
  obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp (h.writes cta hw).2
  refine ⟨{ loc := { s.response with cta := cta }, size := 16 }, (Value.clc r).toBytes,
    ⟨hw, r, hr, rfl, rfl⟩, rfl, ?_⟩
  simp [Value.toBytes, Value.bytes]

theorem Extends.refl (e : Effects) : Extends e e := ⟨fun _ h => h, fun _ h => h, fun _ h => h⟩

theorem Extends.trans {e f g : Effects} (h : Extends e f) (k : Extends f g) :
    Extends e g := ⟨fun r hr => k.1 r (h.1 r hr),
      fun _ hm => k.2.1 (h.2.1 hm), fun _ hm => k.2.2 (h.2.2 hm)⟩

/-- Later observations cannot replace a published response with a different payload. -/
theorem ResponseWrite.mono {f : Effects} (h : Extends e f) {c : Nat} {a : Acc} {bs : List Byte}
    (hw : ResponseWrite s e c a bs) : ResponseWrite s f c a bs := by
  obtain ⟨hc, r, hr, ha, hb⟩ := hw
  exact ⟨h.2.1 hc, r, h.1 r hr, ha, hb⟩

theorem Completion.mono {f : Effects} (h : Extends e f) {c : Nat} {m : Loc} {n : Nat}
    (hc : Completion s e c m n) : Completion s f c m n :=
  ⟨h.2.2 hc.1, hc.2⟩

end
end PTX.Clc
