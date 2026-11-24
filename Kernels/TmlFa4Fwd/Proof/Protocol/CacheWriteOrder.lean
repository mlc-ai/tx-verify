-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.PrimingCacheWriteOrder
import Kernels.TmlFa4Fwd.Proof.Thread.LoaderCacheCopyFamily
import Kernels.TmlFa4Fwd.Proof.Thread.LoaderSameUseCopies

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol.LoaderReady
open PTX PTX.AsyncCopy
open Thread.Loader (PrimingCacheVector recurringUseBefore recurringVectorEvent)

private theorem copyFamily {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) {copy : EvId} {s : Spec}
    (hCopy : X.Copy copy s) :
    (∃ (stage : Fin 2) (pair : Fin 16) (upper : Bool),
      PrimingCacheVector X copy stage pair upper s) ∨
      ∃ e, X.get copy = some e ∧ recurringVectorEvent e ∧ e.kind = .copy s := by
  rcases Thread.Loader.copyPrimingOrRecurringVector hX hCopy with ⟨pair,upper,h⟩ |
      ⟨pair,upper,h⟩ | h
  · exact .inl ⟨0,pair,upper,h.primingCacheVector⟩
  · exact .inl ⟨1,pair,upper,h.primingCacheVector⟩
  · exact .inr h

/-- Ordinary cache writes covering the same byte are either one issue or
causally ordered. Both writes can be considered as intents in an arbitrary prefix. -/
theorem cacheCopyWriteOrder {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {a b : EvId} {s t : Spec} {loc : Loc}
    (ha : X.Copy a s) (hb : X.Copy b t) (hs : s.dst.Covers loc) (ht : t.dst.Covers loc) :
    a = b ∨
      modelCausality l X loc (.async a (.write .copy)) (.async b (.write .copy)) ∨
      modelCausality l X loc (.async b (.write .copy)) (.async a (.write .copy)) := by
  rcases copyFamily hX ha with ⟨sa,pa,ua,hpa⟩ | ⟨ea,hea,hva,hka⟩ <;>
    rcases copyFamily hX hb with ⟨sb,pb,ub,hpb⟩ | ⟨eb,heb,hvb,hkb⟩
  · exact .inl (Thread.Loader.overlappingPrimingCopiesEq hp hX hpa hpb hs ht)
  · exact .inr (.inl (primingCopyBeforeRecurringCopy hp hX hpa heb hvb hkb hs ht))
  · exact .inr (.inr (primingCopyBeforeRecurringCopy hp hX hpb hea hva hka ht hs))
  · rcases lt_trichotomy (recurringUseBefore X a) (recurringUseBefore X b) with h | h | h
    · exact .inr (.inl (recurringCopyBeforeLaterRecurringCopy hp hX hea heb hva hvb
        hka hkb hs ht h))
    · exact .inl (Thread.Loader.overlappingPendingCopiesOfSameUse hp hX
        hea heb hva hvb hka hkb hs ht h)
    · exact .inr (.inr (recurringCopyBeforeLaterRecurringCopy hp hX heb hea hvb hva
        hkb hka ht hs h))

end PTX.Kernels.TmlFa4Fwd.Protocol.LoaderReady
