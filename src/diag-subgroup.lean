import group_theory.subgroup.basic

-- for any type `G` we can define its diagonal type `ΔG={(g,g)|g∈G}`
def Δ (G : Type*) : set (G × G) := { g : G × G | g.fst = g.snd }

-- 14.1
def subgroup_Δ (G : Type*) [group G] : subgroup (G × G) := 
{ carrier := Δ G,
  one_mem' := by { refine rfl, },
  mul_mem' := by { intros a b ga gb,rw Δ at *,finish, },
  inv_mem' := by { intros x hx,rw Δ at *,finish, } }

-- 14.2
theorem normal_Δ_iff_comm (G : Type*) [group G] : (subgroup_Δ G).normal ↔ ∀ g h : G, g * h = h * g :=
begin
  split,
  { intros H g h,
    cases H,
    simp [subgroup_Δ,Δ,*] at *,
    specialize H g g (by refl) g h,
    norm_num at H,
    rw H,
    norm_num,
    exact H,
  },
  {
    intros h,
    fconstructor,
    intros n nsg g,
    simp [subgroup_Δ,Δ,*] at *,
    specialize h g.snd n.snd,
    rw ← h,
    norm_num,
  }
end
