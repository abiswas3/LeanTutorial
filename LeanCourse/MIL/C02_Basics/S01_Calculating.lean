import LeanCourse.Common
import Mathlib.Data.Real.Basic
-- An example.
example (a b c : ℝ) : a * b * c = b * (a * c) := by
  rw [mul_comm a b]
  rw [mul_assoc b a c]

-- Try these.
-- mul_assoc.{u_1} {G : Type u_1} [Semigroup G] (a b c : G) : a * b * c = a * (b * c)
example (a b c : ℝ) : c * b * a = b * (a * c) := by{
  rw [mul_assoc] -- c(ba)
  rw [mul_comm] -- (ba)c 
  rw [mul_assoc] -- b(ac)

}

example (a b c : ℝ) : a * (b * c) = b * (a * c) := by
  rw [mul_comm b c] -- a(cb) == b(ac)
  rw [mul_comm a (c*b)] -- (cb) a = b(ac)
  rw [mul_comm c b] -- b c a = b(ac)
  rw [mul_assoc b c a] -- b (ca) = b(ac)
  rw [mul_comm c a]  -- b (ac) = b(ac)


-- An example.
example (a b c : ℝ) : a * b * c = b * c * a := by
  rw [mul_assoc]
  rw [mul_comm]

/- Try doing the first of these without providing any arguments at all,
   and the second with only one argument. -/
example (a b c : ℝ) : a * (b * c) = b * (c * a) := by
  rw [mul_comm]
  rw [mul_assoc]

example (a b c : ℝ) : a * (b * c) = b * (a * c) := by
  rw [mul_comm a]
  rw [mul_assoc b]
  rw [mul_comm a]
  

-- Using facts from the local context.
example (a b c d e f : ℝ) (h : a * b = c * d) (h' : e = f) : a * (b * e) = c * (d * f) := by
  rw [h']
  rw [← mul_assoc]
  rw [h]
  rw [mul_assoc]

example (a b c d e f : ℝ) (h : b * c = e * f) : a * b * c * d = a * e * f * d := by
  rw [mul_assoc a b c]
  rw [h]
  rw [<- mul_assoc a e f]

example (a b c d : ℝ) (hyp : c = b * a - d) (hyp' : d = a * b) : c = 0 := by
  calc 
    c = b*a - d := by rw [hyp]
    _ = b*a - a*b := by rw [hyp']
    _ = a*b - a*b := by rw[mul_comm b a]
    _ = 0 := by rw [sub_self]

example (a b c d e f : ℝ) (h : a * b = c * d) (h' : e = f) : a * (b * e) = c * (d * f) := by
  rw [h', ← mul_assoc, h, mul_assoc]

section

variable (a b c d e f : ℝ)

example (h : a * b = c * d) (h' : e = f) : a * (b * e) = c * (d * f) := by
  rw [h', <- mul_assoc a, h, mul_assoc]
end

section
variable (a b c : ℝ)

#check a
#check a + b
#check (a : ℝ)
#check mul_comm a b
#check (mul_comm a b : a * b = b * a)
#check mul_assoc c a b
#check mul_comm a
#check mul_comm

end

section
variable (a b : ℝ)

example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := by
  rw [mul_add, add_mul, add_mul]
  rw [← add_assoc, add_assoc (a * a)]
  rw [mul_comm b a, ← two_mul]

example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b :=
  calc
    (a + b) * (a + b) = a * a + b * a + (a * b + b * b) := by
      rw [mul_add, add_mul, add_mul]
    _ = a * a + (b * a + a * b) + b * b := by
      rw [← add_assoc, add_assoc (a * a)]
    _ = a * a + 2 * (a * b) + b * b := by
      rw [mul_comm b a, ← two_mul]

example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b :=
  calc
    (a + b) * (a + b) = a * a + b * a + (a * b + b * b) := by
      rw [mul_add, add_mul, add_mul, <- add_assoc]

    _ = a * a + (b * a + a * b) + b * b := by
      rw [<- add_assoc, add_assoc (a*a)]
    _ = a * a + 2 * (a * b) + b * b := by
      rw [mul_comm a b]
      ring
end

-- Try these. For the second, use the theorems listed underneath.
section
variable (a b c d : ℝ)

example : (a + b) * (c + d) = a * c + a * d + b * c + b * d := by
  rw [mul_add, add_mul, add_mul, <- add_assoc, add_assoc (a*c), add_comm (b*c), <- add_assoc]

-- NOTE: challenging exercise
-- add_sub a b c : a + (b - c) = a + b - c 
-- sub_add a b c : a - b + c = a - (b - c)
-- sub_add_eq_add_sub.{u_1} {α : Type u_1} [SubtractionCommMonoid α] (a b c : α) : a - b + c = a + c - b
example (a b : ℝ) : (a + b) * (a - b) = a ^ 2 - b ^ 2 := by {
  rw [mul_sub, add_mul, add_mul] 
  rw [add_comm (a*b), <- sub_add_eq_add_sub, sub_add, mul_comm b a, <- add_sub, sub_self, <- pow_two b, <- pow_two a, add_zero  ]
  

}

#check pow_two a
#check mul_sub a b c
#check add_mul a b c
#check add_sub a b c
#check sub_add a b c 
#check sub_sub a b c
#check add_zero a

end

-- Examples.

section
variable (a b c d : ℝ)

example (a b c d : ℝ) (hyp : c = d * a + b) (hyp' : b = a * d) : c = 2 * a * d := by
  rw [hyp'] at hyp
  rw [mul_comm d a] at hyp
  rw [← two_mul (a * d)] at hyp
  rw [← mul_assoc 2 a d] at hyp
  exact hyp

example : c * b * a = b * (a * c) := by
  ring

example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := by
  ring

example : (a + b) * (a - b) = a ^ 2 - b ^ 2 := by
  ring

example (hyp : c = d * a + b) (hyp' : b = a * d) : c = 2 * a * d := by
  rw [hyp, hyp']
  ring

end

example (a b c : ℕ) (h : a + b = c) : (a + b) * (a + b) = a * c + b * c := by
  nth_rw 2 [h]
  rw [add_mul]

-- Converting goals
example (x y : ℝ) (h: x^2 = y^2) : x^4 = y^4 := by {
  -- convert the goal to  (x ^ 2) ^ 2 = y ^ 4
  -- this will only be possible if (x^4 = (x^2)^2 
  -- so we need a proof of that 
  convert_to (x ^ 2) ^ 2 = y ^ 4
  . ring 
  rw [h] -- this will replace x² to y²  |- (y^2)^2 = y^4
  ring 
}
