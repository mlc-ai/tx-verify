-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Protocol.Shared.ScratchPublish
public import Kernels.InklingRelDecode.Proof.Lib.ExitPC
import Kernels.InklingRelDecode.Proof.Protocol.Shared.ScratchRound
import Kernels.InklingRelDecode.Proof.Protocol.Shared.ScratchExit
import Kernels.InklingRelDecode.Proof.Lib.BarOne
import Lemmas.Kernel.Safety.HandoffPhased
import Lemmas.Flow.NthEv

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.Shared
open PTX PTX.Frame

/-- **Rounds are ordered by their barrier-zero ordinals.** An event of a data lane, before the
final rendezvous, precedes every event of a data lane of its CTA that has passed more barrier-zero
instances: the later lane passed the instance of the earlier event's ordinal, and the earlier
lane arrives at it after the event. -/
theorem round_before {Q L m X g h u v ea eb} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (a : X.get (g,u)=some ea)
    (b : X.get (h,v)=some eb) (nu : ∀ f, ea.kind≠.ub f) (early : Lib.afterFinal ea.pc=0)
    (other : Lib.finalSync ea.pc=false) (plain : Execution.isBarId 0 ea=false)
    (lg : g%L.block<128) (lh : h%L.block<128) (cta : g/L.block=h/L.block)
    (lt : barOrdinal X g u<barOrdinal X h v) : baseCausality L X (g,u) (h,v) := by
  obtain ⟨i,p,c,md,ilt,eh,ord⟩ := Frame.nth_bar (X:=X) (g:=h) (f:=v) (q:=barOrdinal X g u)
    (id:=0) lt
  obtain ⟨rfl,-⟩ := Lib.recorded_bar hX hp.block eh
  have o : barOrdinal X h i=barOrdinal X g u := ord
  have len : v<(X.tr h).length := (List.getElem?_eq_some_iff.mp b).1
  obtain ⟨j,q,d,peer,eq⟩ := data_arrival hp hX (show X.IsBarrier (h,i) 0 c p from eh)
    (by omega) lh lg cta (fun k p ex => by
      rw [o]
      exact exit_ordinal hp hX a nu early other ex lg lg rfl)
  have e2 : barOrdinal X g j=barOrdinal X h i := eq
  have after : u<j := by
    rcases Nat.lt_trichotomy j u with lt'|rfl|gt
    · have mono := Flow.countP_take_mono (Execution.isBarId 0) (X.tr g) (Nat.succ_le_of_lt lt')
      rw [List.take_add_one,show (X.tr g)[j]?=_ from peer,List.countP_append] at mono
      change barOrdinal X g j+1≤barOrdinal X g u at mono
      omega
    · have : X.get (g,j)=some ⟨q,.bar 0 d .sync⟩ := peer
      rw [a] at this
      cases this
      simp [Execution.isBarId] at plain
    · exact gt
  have peerEv : X.get (g,j)=some ⟨q,.bar 0 d .sync⟩ := peer
  have ordEq : ((X.tr g).take j).countP (Execution.isBarId 0)=
      ((X.tr h).take i).countP (Execution.isBarId 0) := eq
  exact scratch_handoff hp hX peerEv eh cta lg lh ordEq after ilt len

end PTX.Kernels.InklingRelDecode.Proof.Protocol.Shared
