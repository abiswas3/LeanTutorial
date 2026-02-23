import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Real.Basic
import LeanCourse.Common

section
variable (R : Type*) [Ring R]

#check (add_assoc : ∀ a b c : R, a + b + c = a + (b + c))
#check (add_comm : ∀ a b : R, a + b = b + a)
#check (zero_add : ∀ a : R, 0 + a = a)
#check (neg_add_cancel : ∀ a : R, -a + a = 0)
#check (mul_assoc : ∀ a b c : R, a * b * c = a * (b * c))
#check (mul_one : ∀ a : R, a * 1 = a)
#check (one_mul : ∀ a : R, 1 * a = a)
#check (mul_add : ∀ a b c : R, a * (b + c) = a * b + a * c)
#check (add_mul : ∀ a b c : R, (a + b) * c = a * c + b * c)

end

section
variable (R : Type*) [CommRing R]
variable (a b c d : R)

example : c * b * a = b * (a * c) := by ring

example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := by ring

example : (a + b) * (a - b) = a ^ 2 - b ^ 2 := by ring

example (hyp : c = d * a + b) (hyp' : b = a * d) : c = 2 * a * d := by
  rw [hyp, hyp']
  ring

end

namespace MyRing
variable {R : Type*} [Ring R]

theorem add_zero (a : R) : a + 0 = a := by rw [add_comm, zero_add]

theorem add_right_neg (a : R) : a + -a = 0 := by rw [add_comm, neg_add_cancel]

#check MyRing.add_zero
#check add_zero

end MyRing

namespace MyRing
variable {R : Type*} [Ring R]

theorem neg_add_cancel_left (a b : R) : -a + (a + b) = b := by
  rw [← add_assoc, neg_add_cancel, zero_add]

-- Prove these:
theorem add_neg_cancel_right (a b : R) : a + b + -b = a := by
  rw [add_assoc, add_comm, add_comm b, neg_add_cancel, zero_add]

theorem add_left_cancel {a b c : R} (h : a + b = a + c) : b = c := by
  calc 
    b = a + b - a := by rw [<- add_sub, add_comm a, sub_add, sub_self, sub_zero]
    _ = c + (a - a) := by rw [h, add_comm a, <- add_sub]
    _  = c + 0 := by rw [sub_self]
    _  = c := by rw [add_comm, zero_add]    


theorem add_right_cancel {a b c : R} (h : a + b = c + b) : a = c := by
  calc 
    a = a + 0 := by rw [add_zero]
    _ = a + (b-b) := by rw [sub_self]
    _ = a + b - b := by rw [add_sub]
    _ = c + b - b := by rw [h]
    _ = c + (b-b) := by rw [add_sub]
    _ = c := by rw[sub_self, add_comm, zero_add]

theorem mul_zero (a : R) : a * 0 = 0 := by
  have h : a * 0 + a * 0 = a * 0 + 0 := by
    rw [← mul_add, add_zero, add_zero]
  rw [add_left_cancel h]

-- add_left_cancel h (h : a + b = a + c) : b = c
-- add_zero = a + 0 = 0
-- add_right_cancel {a b c : R} (h : a + b = c + b) : a = c := by
theorem zero_mul (a : R) : 0 * a = 0 := by
  have h: 0*a + 0*a = 0*a + 0 := by {
    rw [<- add_mul]
    rw [zero_add]
    rw [add_zero]
  }
  rw [add_left_cancel h]
  

#check add_sub -- a + (b-c) = (a + b) - c
#check sub_add -- a - b + c = a - (b-c)
theorem neg_eq_of_add_eq_zero {a b : R} (h : a + b = 0) : -a = b := by
  calc -a = -a + 0 := by rw [add_zero]
       _   = -a + (a + b) := by rw[h]
       _   = (-a + a) + b := by rw[<- add_assoc]
       _   = 0 + b := by rw [neg_add_cancel]
       _  =  b := by rw[zero_add]

theorem eq_neg_of_add_eq_zero {a b : R} (h : a + b = 0) : a = -b := by
    have h1: -b = a := by {
    calc 
      -b = -b + 0 := by rw[add_zero]
      _ = -b + (a+b) := by rw [h]
      _ = -b + (b + a) := by rw [add_comm a]
      _ = -b + b + a := by rw [add_assoc]
      _ = 0 + a := by rw [neg_add_cancel]
      _ = a := by rw[zero_add]
    }
    rw [h1]


theorem neg_zero : (-0 : R) = 0 := by
  apply neg_eq_of_add_eq_zero
  rw [add_zero]

-- theorem eq_neg_of_add_eq_zero {a b : R} (h : a + b = 0) : a = -b 
theorem neg_neg (a : R) : - -a = a := by{
  symm  -- makes goal  a = - -a
  have h1 : a + -a = 0 := by rw [ add_comm, neg_add_cancel] 
  -- a will play the role of a, -a will be b so i'll get a = - -a
  apply eq_neg_of_add_eq_zero
  -- backward reasoning, if h1: P -> Q then apply/exact h1 will try to match Q 
  -- which we have a = -b, in the form of a = - -a
  -- Then the goal becomes proving  h: a + -a = 0
  rw [h1] -- exact h1 also works 
}
end MyRing



-- Examples.
section
variable {R : Type*} [Ring R]

example (a b : R) : a - b = a + -b :=
  sub_eq_add_neg a b

end

example (a b : ℝ) : a - b = a + -b :=
  rfl

example (a b : ℝ) : a - b = a + -b := by
  rfl

namespace MyRing
variable {R : Type*} [Ring R]

-- #check (zero_add : ∀ a : R, 0 + a = a)
-- #check (neg_add_cancel : ∀ a : R, -a + a = 0)
-- sub_eq_add_neg  a - b = a + -b
theorem self_sub (a : R) : a - a = 0 := by
  rw [<- neg_add_cancel a]
  rw [add_comm]
  rw [sub_eq_add_neg]

theorem one_add_one_eq_two : 1 + 1 = (2 : R) := by
  norm_num

theorem two_mul (a : R) : 2 * a = a + a := by
rw [<- one_add_one_eq_two]
rw [add_mul]
rw [one_mul]

end MyRing

section
variable (A : Type*) [AddGroup A]

#check (add_assoc : ∀ a b c : A, a + b + c = a + (b + c))
#check (zero_add : ∀ a : A, 0 + a = a)
#check (neg_add_cancel : ∀ a : A, -a + a = 0)

end

section
variable {G : Type*} [Group G]

#check (mul_assoc : ∀ a b c : G, a * b * c = a * (b * c))
#check (one_mul : ∀ a : G, 1 * a = a)
#check (inv_mul_cancel : ∀ a : G, a⁻¹ * a = 1)

namespace MyGroup

theorem mul_inv_cancel (a : G) : a * a⁻¹ = 1 := by
  -- This specialises h
  have h := inv_mul_cancel a⁻¹  -- h : (a⁻¹)⁻¹ * a⁻¹ = 1
  calc 
    a * a⁻¹ = 1*(a * a⁻¹) := by rw [one_mul (a * a⁻¹)]
     _      = ((a⁻¹)⁻¹ *a⁻¹ ) *(a * a⁻¹) := by rw [<- h]
     _      = (a⁻¹)⁻¹ *(a⁻¹  * (a * a⁻¹)) := by rw [mul_assoc]
     _      = (a⁻¹)⁻¹ *((a⁻¹  * a) * a⁻¹) := by rw [<- mul_assoc a⁻¹ ]
     _      = (a⁻¹)⁻¹ *(1 * a⁻¹) := by rw [inv_mul_cancel]
     _      = (a⁻¹)⁻¹ *a⁻¹ := by rw [one_mul]
     _      = 1 := by rw [h]

theorem mul_one (a : G) : a * 1 = a := by
  rw [<- inv_mul_cancel a]
  rw [<- mul_assoc ]
  rw [mul_inv_cancel a]
  rw [one_mul]

-- I had to define this theorem -- could have done have h1 by calc
theorem inv_eq_of_mul_eq_one {a b : G} (h : a * b = 1) : a⁻¹ = b := by
    calc a⁻¹ = a⁻¹ * 1       := by rw [mul_one]
           _ = a⁻¹ * (a * b) := by rw [h]
           _ = (a⁻¹ * a) * b := by rw [← mul_assoc]
           _ = 1 * b          := by rw [inv_mul_cancel]
           _ = b              := by rw [one_mul]

-- this is an importnat one 
theorem mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by{
  apply inv_eq_of_mul_eq_one 
  calc a*b *( b⁻¹ * a⁻¹) = a * ((b* b⁻¹) * a⁻¹ ) := by rw [mul_assoc, <- mul_assoc b]
          _                = a * (1 * a⁻¹  ) := by rw [mul_inv_cancel b]
          _                = a * a⁻¹ := by rw [one_mul]
          _                = 1 := by rw [mul_inv_cancel]

}
end MyGroup

end
