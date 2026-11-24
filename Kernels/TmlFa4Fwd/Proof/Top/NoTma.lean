-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Assumptions
public import Kernels.TmlFa4Fwd.Proof.SmWarp.Export.Follow
public import Kernels.TmlFa4Fwd.Spec
public import Lemmas.Protocol.BarTable
import Kernels.TmlFa4Fwd.Proof.Common.Sound
import Kernels.TmlFa4Fwd.Proof.Protocol.Mbar.Init
import Kernels.TmlFa4Fwd.Proof.Protocol.Mbar.InitOne
import Kernels.TmlFa4Fwd.Proof.Protocol.Ready.Obj
import Lemmas.Kernel.Safety.Object

@[expose] public section

/-! # ERR-OBJECT-LIFETIME (`TmaUnsafe`)

`noTma_of_rest`, by `Frame.noTmaUnsafe_of_first`:

* no event invalidates an mbarrier (`no_inval`);
* every object with a record is one of the startup's objects (`obj_of_rec`: a record's issuer
  names the object, and an issuer that is no initialization of it has the object's initialization
  by `use_pub`; `init_event` names that object), so it is initialized first (`obj_initFirst`);
* the initialization is published to the issuer of every other record of the object
  (`pub_of_use`, the one initialization by `init_unique`).

The remaining parts are named premises (`TmaRest`): the fault-freedom of the records that are no
initialization (the ring and unit hand-off protocols), that no access meets an object's bytes (the
roles' access frames), and the absence of `cp.async` overlap and of unallocated masked ranges (the
loader's copies). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow AsyncCopy

noncomputable section
set_option maxRecDepth 100000

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **The parts of ERR-OBJECT-LIFETIME that need the hand-off protocols or the access frames.** -/
structure TmaRest (L : Launch) (m : Mem0) (X : Execution) : Prop where
  fault : ∀ o r, r ∈ X.objects o → (∀ n, r.action ≠ .init n) → r.fault = none
  acc : ∀ e a w i o c l, X.Intent e a w → X.MbInit i o c → a.Covers l →
    ¬ Acc.Covers { loc := o, size := 8 } l
  overlap : ¬ CpAsyncOverlap X
  masked : ¬ MaskedRangeUnalloc m X

section
variable (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
  (hFw : Follow p L X)
include hp hX hFw

set_option maxHeartbeats 4000000 in
/-- **An object with a record has an initialization.** -/
theorem obj_of_rec {o : Loc} {r : MBarrier.Record AsyncCopy.Ref} (hr : r ∈ X.objects o) :
    ∃ e c, X.MbInit e o c := by
  obtain ⟨ev, hget, hm, -⟩ := rec_issuer hX hr
  by_cases hi : ∃ c, ev.kind = .mbInit o c
  · obtain ⟨c, hc⟩ := hi
    obtain ⟨pc, kd⟩ := ev
    simp only at hc
    subst hc
    exact ⟨_, c, pc, hget⟩
  · have hni : ∀ c, ev.kind ≠ .mbInit o c := fun c h => hi ⟨c, h⟩
    obtain ⟨h, k⟩ := r.id.issuer
    have hh := Frame.lt_of_get hX hget
    have hub : ∀ f, ev.kind ≠ .ub f := by
      obtain ⟨pc, kd⟩ := ev
      rintro f rfl
      simp only [Frame.MbarOf] at hm
    obtain ⟨σ, hσ, hJ, hi', hev⟩ := Frame.RoleTable.ev_of_ne_ubU (T := table p L)
      (S := fun g => g < L.threads) (fun g hg => thread_sound hp hg) hX (table_shape_of hp hFw)
      (table_followed hp hX hFw) hh hget hub
    obtain ⟨j, c, hj, -⟩ := use_pub hp hX hFw hh hget hσ hJ hi' hev hm hni
    exact ⟨j, c, hj⟩

/-- **ERR-OBJECT-LIFETIME**, from the startup's initializations and the remaining parts. -/
theorem noTma_of_rest (hR : TmaRest L m X) : ¬ TmaUnsafe L m X := by
  refine Frame.noTmaUnsafe_of_first hX (no_inval hp hX hFw) (fun o ho => ?_)
    (fun o e c he s hs hnon => ?_) hR.fault hR.acc hR.overlap hR.masked
  · obtain ⟨r, hr⟩ := List.exists_mem_of_ne_nil _ ho
    obtain ⟨⟨h, k⟩, c, pc, he⟩ := obj_of_rec hp hX hFw hr
    obtain ⟨-, q, -, -, -, -, hl, -⟩ :=
      init_event hp hX hFw (Frame.lt_of_get hX he) he
    subst hl
    exact ⟨initCnt q, obj_initFirst hp hX hFw h q⟩
  · obtain ⟨pc, he⟩ := he
    obtain ⟨h, k⟩ := e
    have hh := Frame.lt_of_get hX he
    obtain ⟨-, q, -, -, -, -, hl, -⟩ := init_event hp hX hFw hh he
    subst hl
    obtain ⟨ev, hget, hm, hinit⟩ := rec_issuer hX hs
    have hni : ∀ c, ev.kind ≠ .mbInit (obj L h (initOff q)) c := fun c hc => by
      obtain ⟨n, hn⟩ := hinit ⟨c, hc⟩
      exact hnon n hn
    obtain ⟨j, ⟨pcj, hj⟩, hpub⟩ := pub_of_use hp hX hFw hget hm hni
    obtain ⟨rfl, -⟩ := init_unique hp hX hFw (Frame.lt_of_get hX hj) hh hj he
    exact hpub

end

end
end PTX.Kernels.TmlFa4Fwd.Proof
