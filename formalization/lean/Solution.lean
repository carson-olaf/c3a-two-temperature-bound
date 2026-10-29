module

public import C3a.Main

@[expose] public section

/-! # Palomar interface to the finite two-temperature proof

The imported concrete definitions are Kleinwaks's original definitions.
This module does not import Challenge or its deliberate proof placeholder.
-/

namespace PalomarC3a

/-- The strict bound `C₃ₐ > 1.21418`, supplied by the existing finite proof. -/
theorem c3a_gt_121418 : (60709 / 50000 : ℝ) < MaskedDigit.C3a :=
  C3a.c3a_gt_121418

end PalomarC3a
