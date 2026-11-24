-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Safety.TcWrites
public import Lemmas.Flow.RoundTrip
public import Lemmas.Flow.AllocTmpl

@[expose] public section

/-! # The undefined-behaviour branch of `Unsafe`, from the interface

No site of a thread's machine has an undefined-behaviour template, so a thread's undefined behaviour
fires after its machine stopped, or at its deallocation after a read of the base word whose bytes
rebuild to no integer (`ThreadFacts.ub_site`). The machine stops only after a read of the
response buffer, right after a successful poll of the response barrier, whose bytes are no
response; after a read of the base word whose bytes rebuild to no value; or after a Tensor Memory
data event (`ThreadFacts.stop_read`). The protocols exclude each: the read after a successful poll
returns the bytes of a response (`ReaderValues`), the base word rebuilds to an integer
(`BaseWord`), and a data event leaves the consumer followed when its loads returned
single-precision floats (`ThreadFacts.cons_data_next`, `LoadWords`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof.Safety

open PTX

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- The base word rebuilds to an integer: the bytes of the allocation's column. -/
theorem baseWord_of_value (hbv : BaseValue L X) : BaseWord L X := by
  intro g k pc a bs hrd hloc hsz
  obtain ⟨-, -, col, -, -, -, rfl⟩ := hbv g k pc a bs hrd hloc hsz
  exact ⟨32, _, Flow.rebuild_b32 col⟩

/-- **No event is undefined behaviour**, given the protocols' response values, base word and
loaded words. -/
theorem no_ub (hX : Consistent L kernel Prod mem0 X) (ht : ThreadFacts L X)
    (hrv : ReaderValues L X) (hbw : BaseWord L X) (hlw : LoadWords X) : ¬ HasUb X := by
  rintro ⟨⟨g, k⟩, pc, f, he⟩
  have hg : g < L.threads := Frame.lt_of_get hX he
  have hlen : k < (X.tr g).length := by simpa using (List.getElem?_eq_some_iff.mp he).1
  rcases ht.ub_site hg he with hk | ⟨-, pcr, a, bs, hrd, hloc, hsz, hrb⟩
  · obtain ⟨i, d, hi, hσ, hn⟩ := Frame.first_stop ht.tracked hg hk
    obtain ⟨e, hei⟩ : ∃ e, X.get (g, i) = some e :=
      ⟨_, List.getElem?_eq_getElem (show i < (X.tr g).length by omega)⟩
    rcases ht.stop_read hg hei (by omega) hσ hn with
      ⟨a, bs, hk', hloc, hsz, hr, hi0, ppc, p, acq, sc, hpoll⟩ | ⟨a, bs, f', hk', hloc, hsz, hr⟩ |
        hdata
    · obtain ⟨-, -, -, rr, -, -, -, -, -, -, hbs⟩ := hrv _ g (i - 1) ppc p acq sc rfl hpoll
      obtain ⟨epc, ek⟩ := e
      simp only at hk'
      subst hk'
      have hb := hbs epc a bs (by rw [show i - 1 + 1 = i by omega]; exact hei) ⟨hloc, hsz⟩
      rw [hb, Flow.responseOf_clc] at hr
      cases hr
    · obtain ⟨epc, ek⟩ := e
      simp only at hk'
      subst hk'
      obtain ⟨w, x, hw⟩ := hbw g i epc a bs hei hloc hsz
      rw [hw] at hr
      cases hr
    · obtain ⟨c, hc⟩ := ht.cons_data_next hg hei hdata hσ
        (fun k' pc' a' vals sh _ hk' => hlw (g, k') a' vals sh ⟨pc', hk'⟩)
      rw [hn] at hc
      cases hc
  · obtain ⟨w, x, hw⟩ := hbw g (k - 1) pcr a bs hrd hloc hsz
    exact hrb w x hw

end PTX.Kernels.Fp16Gemm8192.Proof.Safety
