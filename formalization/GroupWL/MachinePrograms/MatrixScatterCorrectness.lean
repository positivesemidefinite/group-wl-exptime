import GroupWL.MachinePrograms.MatrixScatter

/-! Entrywise correctness of compact-to-padded row scattering. -/
namespace GroupWL.MachinePrograms.MatrixScatter

theorem scatter_read_miss (neighbors values initial : List ℕ) (width stride offset n z : ℕ)
    (h : ∀ i<n,target neighbors width stride offset i≠z) :
    (scatter neighbors values initial width stride offset n)[z]?=initial[z]? := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [scatter,List.getElem?_set_ne (h n (by omega))]
    exact ih (fun i hi => h i (by omega))

theorem scatter_read_hit (neighbors values initial : List ℕ) (width stride offset n i : ℕ)
    (hi : i<n) (hb : ∀ k<n,target neighbors width stride offset k< initial.length)
    (hinj : ∀ k<n, ∀ l<n, target neighbors width stride offset k=target neighbors width stride offset l → k=l) :
    (scatter neighbors values initial width stride offset n)[target neighbors width stride offset i]?.getD 0=
      values[i]?.getD 0 := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases he : i=n
    · subst i
      rw [scatter,List.getElem?_set_self (by simpa using hb n (by omega)),Option.getD_some]
    · have hne : target neighbors width stride offset n≠target neighbors width stride offset i := by
        intro heq
        exact he (hinj n (by omega) i hi heq).symm
      rw [scatter,List.getElem?_set_ne hne]
      exact ih (by omega) (fun k hk => hb k (by omega))
        (fun k hk l hl => hinj k (by omega) l (by omega))

theorem target_injective (neighbors : List ℕ) (rows width stride offset : ℕ)
    (hwidth : width≤stride)
    (hinj : ∀ a<rows, ∀ b<rows, neighbors[a]?.getD 0=neighbors[b]?.getD 0 → a=b) :
    ∀ i<rows*width, ∀ j<rows*width,
      target neighbors width stride offset i=target neighbors width stride offset j → i=j := by
  intro i hi j hj he
  have hw : 0<width := by nlinarith
  have hs : 0<stride := hw.trans_le hwidth
  have hri : i/width<rows := (Nat.div_lt_iff_lt_mul hw).2 hi
  have hrj : j/width<rows := (Nat.div_lt_iff_lt_mul hw).2 hj
  have hci : i%width<stride := (Nat.mod_lt _ hw).trans_le hwidth
  have hcj : j%width<stride := (Nat.mod_lt _ hw).trans_le hwidth
  have he' : neighbors[i/width]?.getD 0*stride+i%width=
      neighbors[j/width]?.getD 0*stride+j%width := Nat.add_right_cancel he
  have hdi : (neighbors[i/width]?.getD 0*stride+i%width)/stride=neighbors[i/width]?.getD 0 := by
    rw [Nat.mul_comm _ stride,Nat.mul_add_div hs,Nat.div_eq_of_lt hci,Nat.add_zero]
  have hdj : (neighbors[j/width]?.getD 0*stride+j%width)/stride=neighbors[j/width]?.getD 0 := by
    rw [Nat.mul_comm _ stride,Nat.mul_add_div hs,Nat.div_eq_of_lt hcj,Nat.add_zero]
  have hvalues : neighbors[i/width]?.getD 0=neighbors[j/width]?.getD 0 := by
    rw [←hdi,←hdj,he']
  have hrow := hinj _ hri _ hrj hvalues
  have hcol : i%width=j%width := by rw [hvalues] at he'; exact Nat.add_left_cancel he'
  have hei := Nat.mod_add_div i width
  have hej := Nat.mod_add_div j width
  rw [hrow,hcol] at hei
  omega

theorem scatter_values (neighbors values initial : List ℕ) (width stride offset n p : ℕ)
    (hp : 0<p) (hvalues : ∀ x∈values,x<p) (hinitial : ∀ x∈initial,x<p) :
    ∀ x∈scatter neighbors values initial width stride offset n,x<p := by
  induction n with
  | zero => exact hinitial
  | succ n ih =>
    intro x hx
    rcases List.mem_or_eq_of_mem_set hx with hx | hx
    · exact ih x hx
    · subst x
      cases hv : values[n]? with
      | none => exact hp
      | some v => exact hvalues v (List.mem_of_getElem? hv)

end GroupWL.MachinePrograms.MatrixScatter
