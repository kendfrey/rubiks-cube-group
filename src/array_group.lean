import algebra.group

open array

variables {n : ℕ} {α : Type*} [group α] (a b c : array n α)

instance : has_mul (array n α) := ⟨array.map₂ (*)⟩
instance : has_one (array n α) := ⟨mk_array n 1⟩
instance : has_inv (array n α) := ⟨flip array.map has_inv.inv⟩

private lemma mul_assoc : a * b * c = a * (b * c) :=
begin
  apply array.ext,
  intros i,
  apply mul_assoc,
end

private lemma one_mul : 1 * a = a :=
begin
  apply array.ext,
  intros i,
  apply one_mul,
end

private lemma mul_one : a * 1 = a :=
begin
  apply array.ext,
  intros i,
  apply mul_one,
end

private lemma mul_left_inv : a⁻¹ * a = 1 :=
begin
  apply array.ext,
  intros i,
  apply mul_left_inv,
end

instance array_group : group (array n α) :=
{
  mul := (*),
  mul_assoc := mul_assoc,
  one := 1,
  one_mul := one_mul,
  mul_one := mul_one,
  inv := has_inv.inv,
  mul_left_inv := mul_left_inv,
}

@[simp] lemma array.read_mul {a₁ a₂ : array n α} {i : fin n} : (a₁ * a₂).read i = a₁.read i * a₂.read i := rfl