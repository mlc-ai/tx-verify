-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.Events

@[expose] public section

/-! # Event templates a role steps through directly

A proof tool. These invert the templates whose continuation is a state the role already carries,
so a site step names the event and the successor without unfolding the template's monadic
construction:

* `fires_fence_proxy`: a `fence.proxy.proxykind{.sem}.scope` without an address fires the proxy
  fence of its kind and scope and continues at the next instruction (`fires_fenceProxy` is the
  same fact at the template level). This is the proxy fence Wg2's `.fence` site steps through.
* `fires_prefetchBulk`: a `cp.async.bulk.prefetch` whose address, size and optional cache policy
  evaluate, at a 16-byte aligned address and size, fires the bulk prefetch of that range and
  continues at the next instruction. -/

namespace PTX.Flow
open PTX PTX.Proof

noncomputable section

/-- A proxy-fence template fires its proxy fence and advances. -/
theorem fires_fenceProxy {t : TState} {k : ProxyFence} {scope : Option MbarScope} {pc : Nat}
    {e : Event} {o : Option TState}
    (hf : Fires pc (.fenceProxy k scope (next t)) e o) :
    e = ⟨pc, .fenceProxy k scope⟩ ∧ o = some (next t) := hf

/-- A proxy fence without an address fires the proxy fence of its kind with its order's scope:
it records `.fenceProxy` and the thread continues at the next instruction. -/
theorem fires_fence_proxy {A : List Assumption} {L : Launch} {g : Nat} {t : TState}
    {k : ProxyFence} {order : Option (FenceSem × MbarScope)} {pc : Nat} {e : Event}
    {o : Option TState}
    (hf : Fires pc (eventTmpl A L g t (.fence (.proxy k order none))) e o) :
    e = ⟨pc, .fenceProxy k (order.map (·.2))⟩ ∧ o = some (next t) := by
  simp only [eventTmpl, fenceTmpl] at hf
  exact hf

/-- A `cp.async.bulk.prefetch` whose global address and size evaluate, with a defined cache
policy and a 16-byte aligned address and size, fires the bulk prefetch of the global range and
continues at the next instruction. -/
theorem fires_prefetchBulk {A : List Assumption} {L : Launch} {g : Nat} {t : TState}
    {sb : Nat} {soff : Int} {n : Opnd} {policy : Option Opnd} {s : Loc} {size : BitVec 64}
    {pc : Nat} {e : Event} {o : Option TState}
    (hs : effAddr L g t .global sb soff = .ok s) (hn : readBits L g t 32 n = .ok size)
    (hp : bulkPolicy L g t policy = .ok ())
    (hal : size.toNat % 16 = 0 ∧ s.addr % 16 = 0)
    (hf : Fires pc (eventTmpl A L g t (.prefetchBulk sb soff n policy)) e o) :
    e = ⟨pc, .bulkPrefetch { loc := s, size := size.toNat }⟩ ∧ o = some (next t) := by
  simp only [eventTmpl, tensorPrefetchTmpl, ofExec, hs, hn, hp, bind, Except.bind, pure,
    Except.pure, hal] at hf
  exact hf

end
end PTX.Flow
