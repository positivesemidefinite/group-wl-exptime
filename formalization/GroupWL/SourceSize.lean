import GroupWL.CircuitComparisons
import GroupWL.IncidenceTensor

/-! Polynomial cardinality bounds for the actual site-and-square source. -/
namespace GroupWL.SourceSize

open SourceLayout SourceLayout.ComparisonData CircuitComparisons
open scoped BigOperators

variable {F T E : Type} [Field F] [Fintype T] [Fintype E]
  {r : ℕ} (C : ComparisonData F T E r) (L : ℕ)

def linkEquiv : Link E L ≃ (E ⊕ (E × Fin L)) ⊕ E where
  toFun
    | .first e => .inl (.inl e)
    | .middle e i => .inl (.inr (e,i))
    | .last e => .inr e
  invFun
    | .inl (.inl e) => .first e
    | .inl (.inr (e,i)) => .middle e i
    | .inr e => .last e
  left_inv x := by cases x <;> rfl
  right_inv x := by rcases x with (e | ⟨e,i⟩) | e <;> rfl

theorem card_link : Fintype.card (Link E L) = Fintype.card E * (L+2) := by
  rw [Fintype.card_congr (linkEquiv (E := E) L)]
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
  ring

theorem card_node : Fintype.card (Node T E L) =
    Fintype.card T + Fintype.card E * (L+1) := by
  simp [Node]

theorem card_horizontal_le : Fintype.card (C.Horizontal L) ≤
    4*r*(Fintype.card T + Fintype.card E*(L+1)) := by
  classical
  let f : C.Horizontal L → Node T E L × Fin r × Bool × Bool :=
    fun h => (h.1,h.2.1,h.2.2.1.val,h.2.2.2.val)
  have hf : Function.Injective f := by
    rintro ⟨t,i,⟨a,ha⟩,⟨b,hb⟩⟩ ⟨t',i',⟨a',ha'⟩,⟨b',hb'⟩⟩ h
    simp only [f, Prod.mk.injEq] at h
    rcases h with ⟨rfl,rfl,rfl,rfl⟩
    rfl
  calc
    _ ≤ Fintype.card (Node T E L × Fin r × Bool × Bool) := Fintype.card_le_of_injective f hf
    _ = _ := by simp only [Fintype.card_prod,Fintype.card_fin,Fintype.card_bool,card_node]; ring

theorem card_vertical_le : Fintype.card (C.Vertical L) ≤
    2*r*Fintype.card E*(L+2) := by
  classical
  let f : C.Vertical L → Link E L × Fin r × Bool := fun v => (v.1,v.2.1,v.2.2.val)
  have hf : Function.Injective f := by
    rintro ⟨l,i,⟨a,ha⟩⟩ ⟨l',i',⟨a',ha'⟩⟩ h
    simp only [f, Prod.mk.injEq] at h
    rcases h with ⟨rfl,rfl,rfl⟩
    rfl
  calc
    _ ≤ Fintype.card (Link E L × Fin r × Bool) := Fintype.card_le_of_injective f hf
    _ = _ := by simp only [Fintype.card_prod,Fintype.card_fin,Fintype.card_bool,card_link]; ring

theorem card_square_le : Fintype.card (C.Square L) ≤
    4*r*Fintype.card E*(L+2) := by
  classical
  let f : C.Square L → Link E L × Fin r × Bool × Bool :=
    fun s => (s.1,s.2.1,s.2.2.1.val,s.2.2.2.val)
  have hf : Function.Injective f := by
    rintro ⟨l,i,⟨a,ha⟩,⟨b,hb⟩⟩ ⟨l',i',⟨a',ha'⟩,⟨b',hb'⟩⟩ h
    simp only [f, Prod.mk.injEq] at h
    rcases h with ⟨rfl,rfl,rfl,rfl⟩
    rfl
  calc
    _ ≤ Fintype.card (Link E L × Fin r × Bool × Bool) := Fintype.card_le_of_injective f hf
    _ = _ := by simp only [Fintype.card_prod,Fintype.card_fin,Fintype.card_bool,card_link]; ring

theorem card_readout_le : Fintype.card (C.Readout L) ≤
    4*r*(Fintype.card T + Fintype.card E*(L+1)) + 2*r*Fintype.card E*(L+2) := by
  classical
  calc
    _ = Nat.card (C.Horizontal L ⊕ C.Vertical L) := Nat.card_eq_fintype_card.symm
    _ = Fintype.card (C.Horizontal L) + Fintype.card (C.Vertical L) := by
      rw [Nat.card_sum]; simp only [Nat.card_eq_fintype_card]
    _ ≤ _ := Nat.add_le_add (card_horizontal_le C L) (card_vertical_le C L)

theorem card_block_le : Fintype.card (C.Block L) ≤
    4*r*(Fintype.card T + Fintype.card E*(L+1)) + 4*r*Fintype.card E*(L+2) := by
  classical
  calc
    _ = Nat.card (C.Horizontal L ⊕ C.Square L) := Nat.card_eq_fintype_card.symm
    _ = Fintype.card (C.Horizontal L) + Fintype.card (C.Square L) := by
      rw [Nat.card_sum]; simp only [Nat.card_eq_fintype_card]
    _ ≤ _ := Nat.add_le_add (card_horizontal_le C L) (card_square_le C L)

theorem scope_card_le (B : C.Block L) : (C.scope L B).card ≤ 4 := by
  classical
  cases B <;> simp only [scope]
  · simp
  · exact (Finset.card_insert_le _ _).trans (Nat.succ_le_succ
      ((Finset.card_insert_le _ _).trans (Nat.succ_le_succ
      ((Finset.card_insert_le _ _).trans (by simp)))))

theorem card_incidence_le :
    Fintype.card (IncidenceTensor.Incidence (C.affineSystem (L := L))) ≤
      4 * Fintype.card (C.Block L) := by
  classical
  let e : IncidenceTensor.Incidence (C.affineSystem (L := L)) ≃
      (Σ B : C.Block L, {q : C.Readout L // q ∈ C.scope L B}) :=
    { toFun := fun x => ⟨x.1.1,⟨x.1.2,x.2⟩⟩
      invFun := fun x => ⟨(x.1,x.2.1),x.2.2⟩
      left_inv := by rintro ⟨⟨B,q⟩,h⟩; rfl
      right_inv := by rintro ⟨B,⟨q,h⟩⟩; rfl }
  rw [Fintype.card_congr e, Fintype.card_sigma]
  calc
    _ ≤ ∑ _ : C.Block L, 4 := Finset.sum_le_sum (fun B _ => by
      simpa using scope_card_le C L B)
    _ = _ := by simp [Nat.mul_comm]

section Circuit
variable {G : Type} [Fintype G] (D : AddressedCircuit.Circuit G r)

def primaryEquiv : Primary G ≃ G ⊕ Bool where
  toFun
    | .gate t => .inl t
    | .broadcast => .inr false
    | .dummy => .inr true
  invFun
    | .inl t => .gate t
    | .inr false => .broadcast
    | .inr true => .dummy
  left_inv t := by cases t <;> rfl
  right_inv t := by rcases t with t | (_ | _) <;> rfl

def connectionEquiv : Connection D ≃
    Fin D.edges ⊕ (Fin D.testCount ⊕ (Fin r ⊕
      ((Σ t, Fin (gateDim D t)) ⊕ ((Σ t, Fin (gateDim D t)) ⊕ Bool)))) where
  toFun
    | .circuit e => .inl e
    | .test i => .inr (.inl i)
    | .flip i => .inr (.inr (.inl i))
    | .broadcast t j => .inr (.inr (.inr (.inl ⟨t,j⟩)))
    | .identity t j => .inr (.inr (.inr (.inr (.inl ⟨t,j⟩))))
    | .broadcastIdentity b => .inr (.inr (.inr (.inr (.inr b))))
  invFun
    | .inl e => .circuit e
    | .inr (.inl i) => .test i
    | .inr (.inr (.inl i)) => .flip i
    | .inr (.inr (.inr (.inl ⟨t,j⟩))) => .broadcast t j
    | .inr (.inr (.inr (.inr (.inl ⟨t,j⟩)))) => .identity t j
    | .inr (.inr (.inr (.inr (.inr b)))) => .broadcastIdentity b
  left_inv t := by cases t <;> rfl
  right_inv t := by rcases t with t | t | t | ⟨t,j⟩ | ⟨t,j⟩ | b <;> rfl

theorem card_connection_le : Fintype.card (Connection D) ≤
    D.edges + D.testCount + r + 4*Fintype.card G + 2 := by
  classical
  rw [Fintype.card_congr (connectionEquiv D)]
  simp only [Fintype.card_sum,Fintype.card_fin,Fintype.card_bool,Fintype.card_sigma]
  have h : (∑ t : G, gateDim D t) ≤ 2*Fintype.card G := by
    calc
      _ ≤ ∑ _ : G, 2 := Finset.sum_le_sum (fun t _ => by unfold gateDim; split <;> omega)
      _ = _ := by simp [Nat.mul_comm]
  omega

def comparisonEquiv : Comparison D ≃ Fin D.seedCount ⊕ (Connection D × Option Bool) where
  toFun
    | .seed i => .inl i
    | .copy e b => .inr (e,some b)
    | .sum e => .inr (e,none)
  invFun
    | .inl i => .seed i
    | .inr (e,some b) => .copy e b
    | .inr (e,none) => .sum e
  left_inv t := by cases t <;> rfl
  right_inv t := by rcases t with t | ⟨e,(_ | b)⟩ <;> rfl

theorem card_comparison : Fintype.card (Comparison D) =
    D.seedCount + 3 * Fintype.card (Connection D) := by
  rw [Fintype.card_congr (comparisonEquiv D)]
  simp [Nat.mul_comm]

theorem card_realType : Fintype.card (RealType D) =
    Fintype.card G + 2 + Fintype.card (Connection D) := by
  rw [Fintype.card_sum, Fintype.card_congr (primaryEquiv (G := G))]
  simp

instance circuitBlockNonempty [hr : NeZero r] : Nonempty ((comparisons D F).Block L) := by
  letI := hr
  exact ⟨.inl ⟨.inl (.inl .broadcast),0,
    ⟨false,Finset.mem_univ _⟩,⟨false,Finset.mem_univ _⟩⟩⟩

end Circuit
end GroupWL.SourceSize
