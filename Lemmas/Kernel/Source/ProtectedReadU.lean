-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Kernel.Source.ProtectedRead
public import Lemmas.Kernel.Safety.TableU

@[expose] public section
namespace PTX.Frame
open PTX.Flow

variable {K : Kernel} {A : List Assumption} {L : Launch} {mem0 : Mem0} {X : Execution}
  {C : (g : Nat) → Code K A L g} {T : RoleTable C} {S : Nat → Prop}
  (hC : ∀ g < L.threads, (C g).SoundU) (hX : Consistent L K A mem0 X) (hT : T.ShapeOkU S)
include hC hX hT

theorem RoleTable.protected_read_of_followedU (hF : T.Followed X S) {r w : EvId} {a dst : Acc}
    {bs : List (Option Byte)} {written : List Byte} (hr : X.MemReads (.thread r) a bs)
    (hw : X.MemWrites (.thread w) dst written) (hloc : dst.loc = a.loc) (hsize : dst.size = a.size)
    (hlen : written.length = a.size)
    (hv : ∀ k < a.size, modelCausality L X (a.loc.at k) (.thread w) (.thread r))
    (hcls : T.WriteClass S X (fun l => ∃ k < a.size, l = a.loc.at k) w r)
    (hout : ∀ ref dst' bytes, X.MemWrites ref dst' bytes → ¬ S ref.issuer.1 →
      ∀ k < a.size, dst'.Covers (a.loc.at k) →
        ref = .thread w ∨ modelCausality L X (a.loc.at k) ref (.thread w) ∨
          modelCausality L X (a.loc.at k) (.thread r) ref) :
    bs = written.map some := by
  refine read_of_last_write hX hr hw hloc hsize hlen hv fun k hk ref dst' bytes hm hc => ?_
  by_cases hg : S ref.issuer.1
  · obtain ⟨e, he, hwo⟩ := memWrites_writeOf hm
    have hu : ∀ f, e.kind ≠ .ub f := by
      obtain ⟨pc,kind⟩ := e
      rintro f rfl
      exact hwo.elim
    obtain ⟨d,hs,hJ,hi,hev⟩ := RoleTable.ev_of_ne_ubU hC hX hT hF hg he hu
    obtain ⟨htw,ho⟩ := hcls _ _ d e hg hs hJ hi hev he dst' hwo ⟨_,hc,k,hk,rfl⟩
    rcases ref with i | ⟨i,part⟩
    · rcases ho with h | h | h
      · exact .inl (by rw [show i = w from h])
      · exact .inr (.inl (.inl h))
      · exact .inr (.inr (.inl h))
    · obtain ⟨e',he',-,hn⟩ := memWrites_async_issuer hm
      change X.get i = some e at he
      rw [he] at he'
      cases he'
      exact (hn htw).elim
  · exact hout ref dst' bytes hm hg k hk hc

end PTX.Frame
