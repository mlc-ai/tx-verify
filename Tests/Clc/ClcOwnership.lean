-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Clc.ClcOwnership

namespace PTX.Tests.ClcOwnership
open PTX.Clc

-- Failure is possible even with a pending task. It must not prove grid exhaustion.
example : Step (fun task => task < 512) initial
    { initial with response := Function.update initial.response 7 (some none) } :=
  .failure initial 7 rfl
example : ({ initial with response := Function.update initial.response 7 (some none) } :
    State).owner 123 = none := rfl

-- A successful cancellation and an ordinary launch use the same ownership resource.
example : Step (fun task => task < 512) initial {
    owner := Function.update initial.owner 23 (some (.canceled 9))
    response := Function.update initial.response 9 (some (some 23)) } :=
  .success initial 9 23 (by decide) rfl rfl

-- Once launched, no later history can turn this task into a canceled task.
example {s t : State} {valid : Nat → Prop} {task request : Nat}
    (h : Relation.ReflTransGen (Step valid) s t)
    (hl : s.owner task = some .launched) :
    t.owner task ≠ some (.canceled request) := by
  rw [owner_stable h hl]
  simp

-- Repeated observations of the same response are not new cancellation requests.
example {s t : State} {valid : Nat → Prop} {task first second : Nat}
    (h : Relation.ReflTransGen (Step valid) s t)
    (hs : s.owner task = some (.canceled first))
    (ht : t.owner task = some (.canceled second)) : first = second :=
  canceled_unique h hs ht

-- One request cannot own two different tasks, including through later histories.
example {s : State} {valid : Nat → Prop} {a b request : Nat}
    (h : Relation.ReflTransGen (Step valid) initial s)
    (ha : s.owner a = some (.canceled request))
    (hb : s.owner b = some (.canceled request)) : a = b := by
  have hra := canceled_has_response h a request ha
  have hrb := canceled_has_response h b request hb
  simpa using hra.symm.trans hrb

-- An unresolved request cannot already own a canceled task.
example {s : State} {valid : Nat → Prop} {task request : Nat}
    (h : Relation.ReflTransGen (Step valid) initial s)
    (hr : s.response request = none) : s.owner task ≠ some (.canceled request) := by
  intro ho
  have hs := canceled_has_response h task request ho
  simp [hr] at hs

end PTX.Tests.ClcOwnership
