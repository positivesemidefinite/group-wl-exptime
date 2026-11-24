import GroupWL.MachinePrograms.NatArrayLowering

/-! Real bit-string input/output for the natural-array language. The encoding
and decoding scans are fixed Boolean-stack programs with linear exact costs. -/
namespace GroupWL.MachinePrograms.NatArrayLowering

open NatArrayLanguage
open Structured
open Complexity

def bitNat (b : Bool) : ℕ := if b then 1 else 0

variable {K : Type*} [DecidableEq K]

def importBits (raw data : K) : Structured.Program K :=
  .while raw Option.isSome (.pop raw .skip (.push data false)
    (.seq (.push data false) (.push data true)))

theorem importBits_runs (raw data : K) (hne : raw ≠ data) (xs : List Bool) :
    ∀ S : Structured.Store K, S raw = xs →
      Structured.Runs (importBits raw data) S (3*xs.length+xs.count true+1)
        (Function.update (Function.update S raw []) data
          (arrayWord (xs.reverse.map bitNat) ++ S data)) := by
  induction xs with
  | nil =>
    intro S hs
    have he : Function.update (Function.update S raw []) data
        (arrayWord ([].reverse.map bitNat) ++ S data) = S := by
      funext k
      by_cases hk : k=raw <;> by_cases hk' : k=data <;>
        simp [Function.update_apply,hk,hk',hs,hne]
    rw [he]
    exact Structured.Runs.while_false (by simp [hs])
  | cons b xs ih =>
    intro S hs
    let S' := Function.update (Function.update S raw xs) data (arrayWord [bitNat b] ++ S data)
    have hr : S' raw = xs := by simp [S',hne]
    have hd : S' data = arrayWord [bitNat b] ++ S data := by simp [S']
    have first : Structured.Runs (.pop raw .skip (.push data false)
        (.seq (.push data false) (.push data true))) S (2+bitNat b) S' := by
      cases b with
      | false =>
        apply Structured.Runs.pop (t := 1)
        simpa [select,hs,S',bitNat,Ne.symm hne] using
          Structured.Runs.push (Function.update S raw xs) data false
      | true =>
        apply Structured.Runs.pop (t := 2)
        have h1 := Structured.Runs.push (Function.update S raw xs) data false
        simp only [Function.update_of_ne (Ne.symm hne)] at h1
        have h2 := Structured.Runs.push
          (Function.update (Function.update S raw xs) data (false::S data)) data true
        simpa [select,hs,S',bitNat,Ne.symm hne,Function.update_idem] using
          Structured.Runs.seq h1 h2
    have rest := ih S' hr
    have run := Structured.Runs.while_true (test := Option.isSome) (by simp [hs]) first rest
    have he : Function.update (Function.update S' raw []) data
        (arrayWord (xs.reverse.map bitNat) ++ S' data) =
        Function.update (Function.update S raw []) data
          (arrayWord ((b::xs).reverse.map bitNat) ++ S data) := by
      funext k
      by_cases hk : k=data
      · subst k; simp [hd,List.reverse_cons,List.map_append,List.append_assoc]
      · by_cases hk' : k=raw
        · subst k; simp [hne]
        · simp [S',Function.update_of_ne hk,Function.update_of_ne hk']
    rw [he] at run
    cases b <;> convert run using 1 <;> (try simp [importBits,bitNat,List.count_cons]) <;> omega

def exportBits (data raw : K) : Structured.Program K :=
  .while data Option.isSome (.pop data .skip (.push raw false)
    (.seq (discard data) (.push raw true)))

theorem exportBits_runs (data raw : K) (hne : data ≠ raw) (xs : List Bool) :
    ∀ S : Structured.Store K, S data = arrayWord (xs.map bitNat) →
      Structured.Runs (exportBits data raw) S (3*xs.length+xs.count true+1)
        (Function.update (Function.update S data []) raw (xs.reverse ++ S raw)) := by
  induction xs with
  | nil =>
    intro S hs
    have hd : S data = [] := by simpa using hs
    have he : Function.update (Function.update S data []) raw ([].reverse ++ S raw) = S := by
      funext k
      by_cases hk : k=data <;> by_cases hk' : k=raw <;>
        simp [Function.update_apply,hk,hk',hd,hne]
    rw [he]
    exact Structured.Runs.while_false (by simp [hd])
  | cons b xs ih =>
    intro S hs
    let S' := Function.update (Function.update S data (arrayWord (xs.map bitNat))) raw (b::S raw)
    have hd : S' data = arrayWord (xs.map bitNat) := by simp [S',hne]
    have hr : S' raw = b::S raw := by simp [S']
    have first : Structured.Runs (.pop data .skip (.push raw false)
        (.seq (discard data) (.push raw true))) S (2+bitNat b) S' := by
      cases b with
      | false =>
        have hh : S data = false::arrayWord (xs.map bitNat) := by simpa [bitNat] using hs
        apply Structured.Runs.pop (t := 1)
        simpa [select,hh,S',Ne.symm hne] using
          Structured.Runs.push (Function.update S data (arrayWord (xs.map bitNat))) raw false
      | true =>
        have hh : S data = true::false::arrayWord (xs.map bitNat) := by simpa [bitNat] using hs
        apply Structured.Runs.pop (t := 2)
        have h1 := discard_runs (Function.update S data (false::arrayWord (xs.map bitNat))) data
        simp only [Function.update_self,List.tail_cons,Function.update_idem] at h1
        have h2 := Structured.Runs.push (Function.update S data (arrayWord (xs.map bitNat))) raw true
        simpa [select,hh,S',Ne.symm hne,Function.update_idem] using
          Structured.Runs.seq h1 h2
    have rest := ih S' hd
    have run := Structured.Runs.while_true (test := Option.isSome)
      (by cases b <;> simp [hs,bitNat]) first rest
    have he : Function.update (Function.update S' data []) raw (xs.reverse ++ S' raw) =
        Function.update (Function.update S data []) raw ((b::xs).reverse ++ S raw) := by
      funext k
      by_cases hk : k=raw
      · subst k; simp [hr,List.reverse_cons,List.append_assoc]
      · by_cases hk' : k=data
        · subst k; simp [hne]
        · simp [S',Function.update_of_ne hk,Function.update_of_ne hk']
    rw [he] at run
    cases b <;> convert run using 1 <;> (try simp [exportBits,bitNat,List.count_cons]) <;> omega

variable {Reg Arr : Type*} [DecidableEq Reg] [DecidableEq Arr]

def inputStore (input : Arr) (w : BitString) : Store Reg Arr where
  scalar := fun _ => 0
  array := Function.update (fun _ => []) input (w.map bitNat)

theorem importInput_runs (input : Arr) (w : BitString) :
    Structured.Runs (importBits (scratchSlot 15) (arraySlot input))
      (Function.update (fun _ => []) (scratchSlot (Reg := Reg) 15) w.reverse)
      (3*w.length+w.count true+1) (encodeStore (inputStore input w)) := by
  have hr := importBits_runs (scratchSlot (Reg := Reg) 15) (arraySlot input)
    (by simp) w.reverse (Function.update (fun _ => []) (scratchSlot 15) w.reverse) (by simp)
  have he : Function.update
      (Function.update (Function.update (fun _ : StackIndex Reg Arr => []) (scratchSlot 15) w.reverse)
        (scratchSlot 15) []) (arraySlot input)
        (arrayWord (w.reverse.reverse.map bitNat) ++
          Function.update (fun _ : StackIndex Reg Arr => []) (scratchSlot 15) w.reverse (arraySlot input)) =
        encodeStore (inputStore input w) := by
    funext k
    rcases k with (r | a) | i
    · simp [scalarSlot,arraySlot,scratchSlot,encodeStore,inputStore,Function.update_apply]
    · by_cases ha : a=input <;>
        simp [scalarSlot,arraySlot,scratchSlot,encodeStore,inputStore,Function.update_apply,ha]
    · simp [scalarSlot,arraySlot,scratchSlot,encodeStore,inputStore,Function.update_apply]
  rw [he] at hr
  simpa using hr

theorem bitScan_cost (w : BitString) : 3*w.length+w.count true+1 ≤ 4*w.length+1 := by
  have h := List.count_le_length (a := true) (l := w)
  omega

theorem exportOutput_runs (output : Arr) (S : Store Reg Arr) (w : BitString)
    (h : S.array output = w.map bitNat) :
    ∃ T, Structured.Runs (exportBits (arraySlot output) (scratchSlot 14)) (encodeStore S)
      (3*w.length+w.count true+1) T ∧ (T (scratchSlot 14)).reverse = w := by
  refine ⟨Function.update (Function.update (encodeStore S) (arraySlot output) [])
    (scratchSlot 14) w.reverse, ?_, by simp⟩
  have hr := exportBits_runs (arraySlot output) (scratchSlot (Reg := Reg) 14)
    (by simp) w (encodeStore S) (by simp [h])
  simpa using hr

@[simp] theorem encodeStore_nonzero (S : Store Reg Arr) (r : Reg) :
    Option.isSome (encodeStore S (scalarSlot r)).head? = true ↔ S.scalar r ≠ 0 := by
  simp

end GroupWL.MachinePrograms.NatArrayLowering
