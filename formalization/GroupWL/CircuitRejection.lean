import GroupWL.CircuitComparisons

/-! # Explicit scalar image sets for rejecting addressed circuits -/
set_option linter.unusedSectionVars false

namespace GroupWL.CircuitRejection

attribute [local instance] Classical.propDecidable

open AddressedCircuit CircuitComparisons SourceLayout
variable {T : Type*} {r : ℕ} (C : Circuit T r)
variable (F : Type*) [Field F]

/-- A product of singleton-zero coordinates and free field coordinates. -/
def coordinateBox {d : ℕ} (forced : Fin d → Prop) : Set (Fin d → F) :=
  {x | ∀ j, forced j → x j = 0}

theorem coordinateBox_zero {d : ℕ} (forced : Fin d → Prop) :
    (0 : Fin d → F) ∈ coordinateBox F forced := by
  intro j hj
  rfl

theorem coordinateBox_single {d : ℕ} (forced : Fin d → Prop) (j : Fin d)
    (hj : ¬forced j) (z : F) : Pi.single j z ∈ coordinateBox F forced := by
  classical
  intro k hk
  have hkj : k ≠ j := by intro h; subst k; exact hj hk
  simp [hkj]

theorem coordinateBox_image {d : ℕ} (forced : Fin d → Prop) (j : Fin d) :
    (fun x : Fin d → F => x j) '' coordinateBox F forced =
      if forced j then {0} else Set.univ := by
  classical
  by_cases hj : forced j
  · rw [if_pos hj]
    ext z
    constructor
    · rintro ⟨x,hx,rfl⟩
      exact hx j hj
    · rintro rfl
      exact ⟨0,coordinateBox_zero F forced,rfl⟩
  · rw [if_neg hj]
    ext z
    constructor
    · intro _; trivial
    · intro _
      exact ⟨Pi.single j z,coordinateBox_single F forced j hj z,by simp⟩

def PortTrue (t : T) (a : Address r) (b : Bool) : Prop :=
  ∃ u, C.Wire u (t,a) b ∧ C.True u

def PortForced (t : T) (a : Address r) (b : Bool) : Prop :=
  if C.kind t = .scalar then C.True (t,a) else PortTrue C t a b

theorem portCoordinate_injective {t : T} (ht : C.kind t ≠ .scalar) :
    Function.Injective (portCoordinate C t) := by
  intro b c h
  cases b <;> cases c <;> simp [portCoordinate,ht] at h ⊢

theorem forced_compatible (t : T) (a : Address r) (b c : Bool)
    (hbc : portCoordinate C t b = portCoordinate C t c) :
    PortForced C t a b ↔ PortForced C t a c := by
  by_cases ht : C.kind t = .scalar
  · simp [PortForced,ht]
  · rw [portCoordinate_injective C ht hbc]

def ForcedIndex (t : T) (a : Address r) (j : Fin (gateDim C t)) : Prop :=
  ∃ b, portCoordinate C t b = j ∧ PortForced C t a b

@[simp] theorem forcedIndex_port (t : T) (a : Address r) (b : Bool) :
    ForcedIndex C t a (portCoordinate C t b) ↔ PortForced C t a b := by
  constructor
  · rintro ⟨c,hc,ht⟩
    exact (forced_compatible C t a c b hc).mp ht
  · exact fun h => ⟨b,rfl,h⟩

def gateSet (t : T) (a : Address r) : Set (Fin (gateDim C t) → F) :=
  coordinateBox F (ForcedIndex C t a)

@[simp] theorem gateSet_zero (t : T) (a : Address r) :
    (0 : Fin (gateDim C t) → F) ∈ gateSet C F t a := coordinateBox_zero F _

theorem gateInput_image (t : T) (a : Address r) (b : Bool) :
    gateInput C F t b '' gateSet C F t a =
      if PortForced C t a b then {0} else Set.univ := by
  classical
  change (fun x => x (portCoordinate C t b)) '' coordinateBox F (ForcedIndex C t a) = _
  rw [coordinateBox_image,forcedIndex_port]

theorem true_iff_all_ports (t : T) (a : Address r) :
    C.True (t,a) ↔ ∀ b, PortForced C t a b := by
  cases ht : C.kind t with
  | scalar => simp [PortForced,ht]
  | andGate =>
      simp only [PortForced,ht]
      constructor
      · intro h b
        obtain ⟨u,v,hu,hv,htu,htv⟩ := (C.true_and_iff ht).mp h
        cases b
        · exact ⟨u,hu,htu⟩
        · exact ⟨v,hv,htv⟩
      · intro h
        obtain ⟨u,hu,htu⟩ := h false
        obtain ⟨v,hv,htv⟩ := h true
        exact .andGate ht hu hv htu htv

theorem gateOutput_single (t : T) (b : Bool) (z : F) :
    gateOutput C F t (Pi.single (portCoordinate C t b) z) = z := by
  classical
  by_cases ht : C.kind t = .scalar
  · simp [gateOutput,gateInput,portCoordinate,ht,LinearMap.proj_apply]
  · cases b <;> simp [gateOutput,gateInput,portCoordinate,ht,LinearMap.proj_apply]

theorem gateOutput_zero_of_true (t : T) (a : Address r) (ht : C.True (t,a))
    (x : Fin (gateDim C t) → F) (hx : x ∈ gateSet C F t a) : gateOutput C F t x = 0 := by
  have hp (b : Bool) : x (portCoordinate C t b) = 0 :=
    hx _ ((forcedIndex_port C t a b).mpr ((true_iff_all_ports C t a).mp ht b))
  by_cases hk : C.kind t = .scalar
  · simp [gateOutput,gateInput,hk,LinearMap.proj_apply,hp]
  · simp [gateOutput,gateInput,hk,LinearMap.proj_apply,hp]

theorem gateOutput_image (t : T) (a : Address r) :
    gateOutput C F t '' gateSet C F t a = if C.True (t,a) then {0} else Set.univ := by
  classical
  by_cases ht : C.True (t,a)
  · rw [if_pos ht]
    ext z
    constructor
    · rintro ⟨x,hx,rfl⟩
      exact gateOutput_zero_of_true C F t a ht x hx
    · rintro rfl
      exact ⟨0,gateSet_zero C F t a,(gateOutput C F t).map_zero⟩
  · rw [if_neg ht]
    have hfree : ∃ b, ¬PortForced C t a b := by
      simpa only [not_forall] using mt (true_iff_all_ports C t a).mpr ht
    obtain ⟨b,hb⟩ := hfree
    ext z
    constructor
    · intro _; trivial
    · intro _
      refine ⟨Pi.single (portCoordinate C t b) z,?_,gateOutput_single C F t b z⟩
      exact coordinateBox_single F (ForcedIndex C t a) _
        (fun h => hb ((forcedIndex_port C t a b).mp h)) z

/-- The primary sets are the truth-dependent gate products; the broadcast
and dummy primaries have the full one-dimensional space. -/
def primarySet (t : Primary T) (a : Address r) : Set (Fin (primaryDim C t) → F) :=
  match t with
  | .gate t => gateSet C F t a
  | .broadcast => Set.univ
  | .dummy => Set.univ

@[simp] theorem primarySet_zero (t : Primary T) (a : Address r) :
    (0 : Fin (primaryDim C t) → F) ∈ primarySet C F t a := by
  cases t with
  | gate t => exact gateSet_zero C F t a
  | broadcast => trivial
  | dummy => trivial

/-- Exactly the connections whose source scalar image is singleton zero. -/
def SourceTrue (e : Connection C) (a : Address r) : Prop :=
  match e with
  | .circuit e => C.True ((C.schema e).source,a)
  | .test k => C.True ((C.test k).gate,a)
  | .identity t j => ForcedIndex C t a j
  | _ => False

theorem projection_univ {d : ℕ} (j : Fin d) :
    (LinearMap.proj j : (Fin d → F) →ₗ[F] F) '' Set.univ = Set.univ := by
  ext z
  constructor
  · intro _; trivial
  · intro _
    exact ⟨fun _ => z,Set.mem_univ _,rfl⟩

theorem connection_source_image (e : Connection C) (a : Address r) :
    e.sourceForm C F '' primarySet C F (e.source C) a =
      if SourceTrue C e a then {0} else Set.univ := by
  classical
  cases e with
  | circuit e => exact gateOutput_image C F _ _
  | test k => exact gateOutput_image C F _ _
  | flip i => simpa only [Connection.sourceForm,Connection.source,primarySet,SourceTrue,if_false] using projection_univ F (0:Fin 1)
  | broadcast t j => simpa only [Connection.sourceForm,Connection.source,primarySet,SourceTrue,if_false] using projection_univ F (0:Fin 1)
  | identity t j => exact coordinateBox_image F (ForcedIndex C t a) j
  | broadcastIdentity b => simpa only [Connection.sourceForm,Connection.source,primarySet,SourceTrue,if_false] using projection_univ F (0:Fin 1)

/-- On an active connection a singleton-zero source has singleton-zero target;
an accepting test is the only potentially exceptional case and is excluded. -/
theorem source_true_target (hreject : ¬C.Accepts) (e : Connection C) (a : Address r)
    (hdom : (e.domain C).Contains a) (hs : SourceTrue C e a) :
    e.targetForm C F '' primarySet C F (e.target C) ((e.permutation C).apply a) = {0} ∧
      rejectingConstant C F (.sum e) = 0 := by
  cases e with
  | circuit e =>
      have hw : C.Wire ((C.schema e).source,a)
          ((C.schema e).target,(C.schema e).permutation.apply a) (C.schema e).port :=
        ⟨e,a,hdom,rfl,rfl,rfl⟩
      have hp : PortForced C (C.schema e).target ((C.schema e).permutation.apply a) (C.schema e).port := by
        by_cases hk : C.kind (C.schema e).target = .scalar
        · simp only [PortForced,hk,if_true]
          exact .scalar hk hw hs
        · simp only [PortForced,hk,if_false]
          exact ⟨_,hw,hs⟩
      refine ⟨?_,rfl⟩
      change gateInput C F (C.schema e).target (C.schema e).port ''
        gateSet C F (C.schema e).target ((C.schema e).permutation.apply a) = {0}
      rw [gateInput_image,if_pos hp]
  | test k => exact False.elim (hreject ⟨((C.test k).gate,a),⟨k,rfl,hdom⟩,hs⟩)
  | flip i => exact False.elim hs
  | broadcast t j => exact False.elim hs
  | identity t j =>
      refine ⟨?_,rfl⟩
      change (fun x : Fin (gateDim C t) → F => x j) '' coordinateBox F (ForcedIndex C t a) = {0}
      change ForcedIndex C t a j at hs
      rw [coordinateBox_image,if_pos hs]
  | broadcastIdentity b => exact False.elim hs

/-- The actual two-coordinate buffer, allowing any specified nonempty sum image. -/
def bufferSet (D : Set F) (c : F) : Set (Fin 2 → F) :=
  {x | x 0 + x 1 - c ∈ D}

theorem bufferSet_nonempty (D : Set F) (hD : D.Nonempty) (c : F) :
    (bufferSet F D c).Nonempty := by
  obtain ⟨d,hd⟩ := hD
  refine ⟨![0,c+d],?_⟩
  change 0 + (c+d) - c ∈ D
  convert hd using 1; abel

theorem bufferSet_coordinate (D : Set F) (hD : D.Nonempty) (c : F) (b : Bool) :
    (LinearMap.proj (if b then (1 : Fin 2) else 0) : (Fin 2 → F) →ₗ[F] F) ''
      bufferSet F D c = Set.univ := by
  obtain ⟨d,hd⟩ := hD
  ext z
  constructor
  · intro _; trivial
  · intro _
    cases b
    · refine ⟨![z,c+d-z],?_,rfl⟩
      change z + (c+d-z) - c ∈ D
      convert hd using 1; abel
    · refine ⟨![c+d-z,z],?_,rfl⟩
      change (c+d-z) + z - c ∈ D
      convert hd using 1; abel

theorem bufferSet_sum (D : Set F) (c : F) :
    ((LinearMap.proj (0 : Fin 2) : (Fin 2 → F) →ₗ[F] F) + (LinearMap.proj (1 : Fin 2) : (Fin 2 → F) →ₗ[F] F)) ''
      bufferSet F D c = (fun d => c+d) '' D := by
  ext z
  constructor
  · rintro ⟨x,hx,rfl⟩
    refine ⟨x 0 + x 1 - c,hx,?_⟩
    change c + (x 0 + x 1 - c) = x 0 + x 1
    abel
  · rintro ⟨d,hd,rfl⟩
    refine ⟨![0,c+d],?_,by simp⟩
    change 0 + (c+d) - c ∈ D
    convert hd using 1; abel

noncomputable def targetImage (e : Connection C) (a : Address r) : Set F :=
  e.targetForm C F '' primarySet C F (e.target C) ((e.permutation C).apply a)

theorem targetImage_nonempty (e : Connection C) (a : Address r) :
    (targetImage C F e a).Nonempty :=
  (show (primarySet C F (e.target C) ((e.permutation C).apply a)).Nonempty from
    ⟨0,primarySet_zero C F _ _⟩).image (e.targetForm C F)

noncomputable def buffer (e : Connection C) (a : Address r) : Set (Fin 2 → F) :=
  if SourceTrue C e a then {0} else bufferSet F (targetImage C F e a) (rejectingConstant C F (.sum e))

theorem buffer_nonempty (e : Connection C) (a : Address r) : (buffer C F e a).Nonempty := by
  unfold buffer
  split
  · exact Set.singleton_nonempty _
  · exact bufferSet_nonempty F _ (targetImage_nonempty C F e a) _

theorem buffer_coordinate (e : Connection C) (a : Address r) (b : Bool) :
    (LinearMap.proj (if b then (1 : Fin 2) else 0) : (Fin 2 → F) →ₗ[F] F) ''
      buffer C F e a = if SourceTrue C e a then {0} else Set.univ := by
  by_cases hs : SourceTrue C e a
  · rw [buffer,if_pos hs,if_pos hs]
    simp
  · rw [buffer,if_neg hs,if_neg hs]
    exact bufferSet_coordinate F _ (targetImage_nonempty C F e a) _ b

theorem buffer_sum (hreject : ¬C.Accepts) (e : Connection C) (a : Address r)
    (hdom : (e.domain C).Contains a) :
    ((LinearMap.proj (0 : Fin 2) : (Fin 2 → F) →ₗ[F] F) + (LinearMap.proj (1 : Fin 2) : (Fin 2 → F) →ₗ[F] F)) ''
      buffer C F e a = (fun d => rejectingConstant C F (.sum e)+d) '' targetImage C F e a := by
  by_cases hs : SourceTrue C e a
  · obtain ⟨ht,hc⟩ := source_true_target C F hreject e a hdom hs
    change targetImage C F e a = {0} at ht
    rw [buffer,if_pos hs,ht,hc]
    simp
  · rw [buffer,if_neg hs]
    exact bufferSet_sum F _ _

/-- Explicit primary and private-buffer image sets at every address. -/
noncomputable def rejectingImages : (comparisons C F).ImageSets :=
  fun t a => match t with
  | .inl t => primarySet C F t a
  | .inr e => buffer C F e a

theorem rejectingImages_nonempty : ∀ t a, (rejectingImages C F t a).Nonempty := by
  intro t a
  cases t with
  | inl t => exact ⟨0,primarySet_zero C F t a⟩
  | inr e => exact buffer_nonempty C F e a

/-- Rejection supplies exactly the source scalar-image equalities for the
explicit nonzero rejecting comparison charge. -/
theorem rejecting_constant_images (hreject : ¬C.Accepts) :
    (comparisons C F).ConstantScalarImages (rejectingConstant C F) (rejectingImages C F) := by
  refine ⟨rejectingImages_nonempty C F,?_⟩
  intro e a
  cases e with
  | seed k =>
      let raw : Address r := fun i => (a i).val
      have ht : C.True ((C.seed k).gate,raw) := .seed ⟨k,rfl,fun i => (a i).property⟩
      change gateOutput C F (C.seed k).gate '' gateSet C F (C.seed k).gate raw =
        (fun z : F => 0+z) '' ((0 : (Fin 1 → F) →ₗ[F] F) '' Set.univ)
      rw [gateOutput_image,if_pos ht]
      simp
  | copy e b =>
      let raw : Address r := fun i => (a i).val
      change e.sourceForm C F '' primarySet C F (e.source C) raw =
        (fun z : F => 0+z) ''
          ((LinearMap.proj (if b then (1 : Fin 2) else 0) : (Fin 2 → F) →ₗ[F] F) '' buffer C F e raw)
      simp only [zero_add,Set.image_id']
      rw [connection_source_image,buffer_coordinate]
  | sum e =>
      let raw : Address r := fun i => (a i).val
      exact buffer_sum C F hreject e raw (fun i => (a i).property)

end GroupWL.CircuitRejection
