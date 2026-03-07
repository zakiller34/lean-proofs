/-!
# Modal Logic — S5 Collapse (MSC 03B45)

Under Spinoza's necessitarianism (1P33), there is only one possible world.
Modal operators therefore collapse: □p ↔ p ↔ ◇p.

We model necessity and possibility as the identity on Prop.
Intermediate steps that exploit the modal distinction are preserved
as structured arguments, but collapse is built into the definitions.
-/

namespace Spinoza

/-- Necessity (S5-collapse): □p ≡ p -/
def Necessarily (p : Prop) : Prop := p

/-- Possibility (S5-collapse): ◇p ≡ p -/
def Possibly (p : Prop) : Prop := p

@[simp] theorem necessarily_iff (p : Prop) : Necessarily p ↔ p := Iff.rfl
@[simp] theorem possibly_iff   (p : Prop) : Possibly p ↔ p := Iff.rfl

theorem necessarily_intro {p : Prop} (h : p) : Necessarily p := h
theorem necessarily_elim  {p : Prop} (h : Necessarily p) : p := h

theorem possibly_intro {p : Prop} (h : p) : Possibly p := h
theorem possibly_elim  {p : Prop} (h : Possibly p) : p := h

/-- Under S5-collapse, necessity implies possibility -/
theorem nec_implies_pos {p : Prop} (h : Necessarily p) : Possibly p := h

/-- Under S5-collapse, necessary truth of God's existence implies unique determination -/
theorem nec_of_truth (p : Prop) (h : p) : Necessarily p := h

end Spinoza
