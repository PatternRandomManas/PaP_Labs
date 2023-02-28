import PnP2023.Lec_01_25.Answer

namespace Waffle

theorem Answer.eq_of_le_le (a b  : Answer) : 
  a ≤ b → b ≤ a → a = b := 
  by
    intro h₁ h₂
    cases c₁:h₁
    case le_yes => 
      cases c₂:h₂
      case le_yes => rfl
      case refl => rfl
    case no_le => 
      cases c₂:h₂
      case refl => rfl 
      case no_le => rfl      
    case refl => rfl 

/- Correct solution -/