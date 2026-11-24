-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Data.Loaded
public import Kernels.TmlFa4Fwd.Proof.Softmax.Export.Count
public import Kernels.TmlFa4Fwd.Proof.SmWarp.DataEvent
import Lemmas.Flow.NthEv

@[expose] public section
namespace PTX.Kernels.TmlFa4Fwd.Proof.Values
open PTX.Flow Softmax

noncomputable section
open Classical

/-- The softmax data state at a position on the lane's trace. -/
def softState (p : Params) (L : Launch) (X : Execution) (g i : Nat) : Option Softmax.D :=
  match Frame.stateAt (threadD p L) X g i with
  | some (some (.inr ⟨.softmax,d⟩,_)) => some d
  | _ => none

def softRounds (p : Params) (L : Launch) (g : Nat) : Nat :=
  if h : ∃ N, SoftRounds p L g N then h.choose else 0

def wordState (p L X g n) :=
  softState p L X g (nthEv X (Softmax.cls L g .sst) g n)

def packState (p L X g u q) :=
  softState p L X g (nthEv X Tm.isTcSt g (4*u+q))

/-- Read each field from its own store position. A prefix need not contain all stores. -/
def softRow (p : Params) (L : Launch) (X : Execution) (g : Nat) : RowData where
  P u i := match packState p L X g u (i/32) with
    | some ⟨.pst r _,v,_,_⟩ => Data.P p L g v r i
    | _ => 0
  c u := match packState p L X g u 0 with
    | some ⟨.pst r _,v,_,_⟩ => Data.scale p (Data.maximum p L g v r)
    | _ => 1
  f u := if u = 0 then 1 else match wordState p L X g (u-1) with
    | some ⟨.stat pl,v,_,_⟩ => Data.factor p v (bif pl then .plain else .bias)
    | _ => 1
  rs := ((wordState p L X g (softRounds p L g - 1)).map (·.v.rs)).getD 0
  rm := ((wordState p L X g (softRounds p L g)).map (fun d => if d.v.mf then d.v.mr else 0)).getD 0

/-- The final max word also carries a finite versus minus-infinity distinction. -/
def softMaxFinite (p : Params) (L : Launch) (X : Execution) (g : Nat) : Bool :=
  ((wordState p L X g (softRounds p L g)).map (·.v.mf)).getD false

end
end PTX.Kernels.TmlFa4Fwd.Proof.Values
