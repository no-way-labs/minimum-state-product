/-
  AllNormalFormFalse.lean -- Proves allNormalForm_false.

  The key argument: under hall_normal (all phases normal form), every phase
  has a length-1 localized suffix (or EC). The suffix's mover is left(t) or
  right(t). Combined with hfull and n >= 9, this forces all movers into the
  5-neighborhood of t, which contradicts hno_safe via
  movers_in_five_contradicts_hno_safe.

  Actually, the localized suffix only constrains the LAST step of each phase,
  not all steps. The proof below uses a direct approach.
-/
import LeanMn.LowerBound.Archive.EntryConflict.WaterfallBridge
import LeanMn.LowerBound.Archive.EntryConflict.OppositeStart

namespace LeanMn

variable {sys : System}

private theorem five_way_restart_transport
    {A B C D E LK RK : Prop}
    (h : A ∨ B ∨ C ∨ D ∨ E)
    (hB : B → LK)
    (hC : C → LK)
    (hD : D → RK)
    (hE : E → RK) :
    A ∨ LK ∨ RK := by
  rcases h with hA | hB0 | hC0 | hD0 | hE0
  · exact Or.inl hA
  · exact Or.inr (Or.inl (hB hB0))
  · exact Or.inr (Or.inl (hC hC0))
  · exact Or.inr (Or.inr (hD hD0))
  · exact Or.inr (Or.inr (hE hE0))

private theorem four_way_and_transport
    {A B C D S : Prop}
    (h : (A ∨ B ∨ C ∨ D) ∧ S) :
    (A ∧ S) ∨ (B ∧ S) ∨ (C ∧ S) ∨ (D ∧ S) := by
  rcases h with ⟨hcases, hs⟩
  rcases hcases with hA | hB | hC | hD
  · exact Or.inl ⟨hA, hs⟩
  · exact Or.inr (Or.inl ⟨hB, hs⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨hC, hs⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨hD, hs⟩))

private theorem nine_way_prev_transport
    {A L4S L4X L2S L2X RL2X RL2S RR4X RR4S LL4 LL2 RL2 RR4 : Prop}
    (h : A ∨ L4S ∨ L4X ∨ L2S ∨ L2X ∨ RL2X ∨ RL2S ∨ RR4X ∨ RR4S)
    (hL4S : L4S → LL4 ∨ LL2)
    (hL4X : L4X → LL4 ∨ LL2)
    (hL2S : L2S → LL4 ∨ LL2)
    (hL2X : L2X → LL4 ∨ LL2)
    (hRL2X : RL2X → RL2 ∨ RR4)
    (hRL2S : RL2S → RL2 ∨ RR4)
    (hRR4X : RR4X → RL2 ∨ RR4)
    (hRR4S : RR4S → RL2 ∨ RR4) :
    A ∨ LL4 ∨ LL2 ∨ RL2 ∨ RR4 := by
  rcases h with hA | hL4S0 | hL4X0 | hL2S0 | hL2X0 | hRL2X0 | hRL2S0 | hRR4X0 | hRR4S0
  · exact Or.inl hA
  · rcases hL4S hL4S0 with hLL4 | hLL2
    · exact Or.inr (Or.inl hLL4)
    · exact Or.inr (Or.inr (Or.inl hLL2))
  · rcases hL4X hL4X0 with hLL4 | hLL2
    · exact Or.inr (Or.inl hLL4)
    · exact Or.inr (Or.inr (Or.inl hLL2))
  · rcases hL2S hL2S0 with hLL4 | hLL2
    · exact Or.inr (Or.inl hLL4)
    · exact Or.inr (Or.inr (Or.inl hLL2))
  · rcases hL2X hL2X0 with hLL4 | hLL2
    · exact Or.inr (Or.inl hLL4)
    · exact Or.inr (Or.inr (Or.inl hLL2))
  · rcases hRL2X hRL2X0 with hRL2 | hRR4
    · exact Or.inr (Or.inr (Or.inr (Or.inl hRL2)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr hRR4)))
  · rcases hRL2S hRL2S0 with hRL2 | hRR4
    · exact Or.inr (Or.inr (Or.inr (Or.inl hRL2)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr hRR4)))
  · rcases hRR4X hRR4X0 with hRL2 | hRR4
    · exact Or.inr (Or.inr (Or.inr (Or.inl hRL2)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr hRR4)))
  · rcases hRR4S hRR4S0 with hRL2 | hRR4
    · exact Or.inr (Or.inr (Or.inr (Or.inl hRL2)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr hRR4)))

private theorem tagged_two_way_transport
    {P Q A B C : Prop}
    (tag : P → Q)
    (h : A → B ∨ C) :
    (P ∧ A) → (Q ∧ B) ∨ (Q ∧ C) := by
  intro hp
  rcases hp with ⟨hpfx, ha⟩
  rcases h ha with hb | hc
  · exact Or.inl ⟨tag hpfx, hb⟩
  · exact Or.inr ⟨tag hpfx, hc⟩

private theorem grouped_restart_exact_split_transport
    {A LP RP L1 L2 L3 L4 R1 R2 R3 R4 LS RS : Prop}
    (h : A ∨ (LP ∧ LS) ∨ (RP ∧ RS))
    (hL : LP → L1 ∨ L2 ∨ L3 ∨ L4)
    (hR : RP → R1 ∨ R2 ∨ R3 ∨ R4) :
    A ∨ (L1 ∧ LS) ∨ (L2 ∧ LS) ∨ (L3 ∧ LS) ∨ (L4 ∧ LS) ∨
      (R1 ∧ RS) ∨ (R2 ∧ RS) ∨ (R3 ∧ RS) ∨ (R4 ∧ RS) := by
  rcases h with hA | hL0 | hR0
  · exact Or.inl hA
  · rcases four_way_and_transport ⟨hL hL0.1, hL0.2⟩ with hL1 | hL2 | hL3 | hL4
    · exact Or.inr (Or.inl hL1)
    · exact Or.inr (Or.inr (Or.inl hL2))
    · exact Or.inr (Or.inr (Or.inr (Or.inl hL3)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hL4))))
  · rcases four_way_and_transport ⟨hR hR0.1, hR0.2⟩ with hR1 | hR2 | hR3 | hR4
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hR1)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hR2))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hR3)))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hR4)))))))

private theorem nine_way_transport
    {A B C D E F G H I B' C' D' E' F' G' H' I' : Prop}
    (h : A ∨ B ∨ C ∨ D ∨ E ∨ F ∨ G ∨ H ∨ I)
    (hB : B → B') (hC : C → C') (hD : D → D') (hE : E → E')
    (hF : F → F') (hG : G → G') (hH : H → H') (hI : I → I') :
    A ∨ B' ∨ C' ∨ D' ∨ E' ∨ F' ∨ G' ∨ H' ∨ I' := by
  rcases h with hA | hB0 | hC0 | hD0 | hE0 | hF0 | hG0 | hH0 | hI0
  · exact Or.inl hA
  · exact Or.inr (Or.inl (hB hB0))
  · exact Or.inr (Or.inr (Or.inl (hC hC0)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (hD hD0))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (hE hE0)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (hF hF0))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (hG hG0)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (hH hH0))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (hI hI0))))))))

private theorem restart_started_to_prev_transport
    {A LP RP LS RS : Prop}
    {L1 L2 L3 L4 R1 R2 R3 R4 : Prop}
    {TL1 TL2 TL3 TL4 TR1 TR2 TR3 TR4 : Prop}
    {LL4 LL2 RL2 RR4 : Prop}
    (h : A ∨ (LP ∧ LS) ∨ (RP ∧ RS))
    (hL : LP → L1 ∨ L2 ∨ L3 ∨ L4)
    (hR : RP → R1 ∨ R2 ∨ R3 ∨ R4)
    (hTL1 : (L1 ∧ LS) → TL1)
    (hTL2 : (L2 ∧ LS) → TL2)
    (hTL3 : (L3 ∧ LS) → TL3)
    (hTL4 : (L4 ∧ LS) → TL4)
    (hTR1 : (R1 ∧ RS) → TR1)
    (hTR2 : (R2 ∧ RS) → TR2)
    (hTR3 : (R3 ∧ RS) → TR3)
    (hTR4 : (R4 ∧ RS) → TR4)
    (hPL1 : TL1 → LL4 ∨ LL2)
    (hPL2 : TL2 → LL4 ∨ LL2)
    (hPL3 : TL3 → LL4 ∨ LL2)
    (hPL4 : TL4 → LL4 ∨ LL2)
    (hPR1 : TR1 → RL2 ∨ RR4)
    (hPR2 : TR2 → RL2 ∨ RR4)
    (hPR3 : TR3 → RL2 ∨ RR4)
    (hPR4 : TR4 → RL2 ∨ RR4) :
    A ∨ LL4 ∨ LL2 ∨ RL2 ∨ RR4 := by
  have hexact :
      A ∨ (L1 ∧ LS) ∨ (L2 ∧ LS) ∨ (L3 ∧ LS) ∨ (L4 ∧ LS) ∨
        (R1 ∧ RS) ∨ (R2 ∧ RS) ∨ (R3 ∧ RS) ∨ (R4 ∧ RS) :=
    grouped_restart_exact_split_transport h hL hR
  have htail :
      A ∨ TL1 ∨ TL2 ∨ TL3 ∨ TL4 ∨ TR1 ∨ TR2 ∨ TR3 ∨ TR4 :=
    nine_way_transport hexact hTL1 hTL2 hTL3 hTL4 hTR1 hTR2 hTR3 hTR4
  exact nine_way_prev_transport htail hPL1 hPL2 hPL3 hPL4 hPR1 hPR2 hPR3 hPR4

private theorem restart_kout_started_cycle_transport
    {A LP RP LS RS : Prop}
    {L1 L2 L3 L4 R1 R2 R3 R4 : Prop}
    {TL1 TL2 TL3 TL4 TR1 TR2 TR3 TR4 : Prop}
    {LL4 LL2 RL2 RR4 LK RK : Prop}
    (h : A ∨ (LP ∧ LS) ∨ (RP ∧ RS))
    (hL : LP → L1 ∨ L2 ∨ L3 ∨ L4)
    (hR : RP → R1 ∨ R2 ∨ R3 ∨ R4)
    (hTL1 : (L1 ∧ LS) → TL1)
    (hTL2 : (L2 ∧ LS) → TL2)
    (hTL3 : (L3 ∧ LS) → TL3)
    (hTL4 : (L4 ∧ LS) → TL4)
    (hTR1 : (R1 ∧ RS) → TR1)
    (hTR2 : (R2 ∧ RS) → TR2)
    (hTR3 : (R3 ∧ RS) → TR3)
    (hTR4 : (R4 ∧ RS) → TR4)
    (hPL1 : TL1 → LL4 ∨ LL2)
    (hPL2 : TL2 → LL4 ∨ LL2)
    (hPL3 : TL3 → LL4 ∨ LL2)
    (hPL4 : TL4 → LL4 ∨ LL2)
    (hPR1 : TR1 → RL2 ∨ RR4)
    (hPR2 : TR2 → RL2 ∨ RR4)
    (hPR3 : TR3 → RL2 ∨ RR4)
    (hPR4 : TR4 → RL2 ∨ RR4)
    (hLL4 : LL4 → LK)
    (hLL2 : LL2 → LK)
    (hRL2 : RL2 → RK)
    (hRR4 : RR4 → RK) :
    A ∨ LK ∨ RK := by
  have hprev :
      A ∨ LL4 ∨ LL2 ∨ RL2 ∨ RR4 :=
    restart_started_to_prev_transport
      h hL hR
      hTL1 hTL2 hTL3 hTL4
      hTR1 hTR2 hTR3 hTR4
      hPL1 hPL2 hPL3 hPL4
      hPR1 hPR2 hPR3 hPR4
  exact five_way_restart_transport hprev hLL4 hLL2 hRL2 hRR4

private theorem restart_kout_started_cycle_transport2
    {A LP RP LS RS : Prop}
    {L1 L2 L3 L4 R1 R2 R3 R4 : Prop}
    {TL1 TL2 TL3 TL4 TR1 TR2 TR3 TR4 : Prop}
    {LL4 LL2 RL2 RR4 : Prop}
    (h : A ∨ (LP ∧ LS) ∨ (RP ∧ RS))
    (hL : LP → L1 ∨ L2 ∨ L3 ∨ L4)
    (hR : RP → R1 ∨ R2 ∨ R3 ∨ R4)
    (hTL1 : (L1 ∧ LS) → TL1)
    (hTL2 : (L2 ∧ LS) → TL2)
    (hTL3 : (L3 ∧ LS) → TL3)
    (hTL4 : (L4 ∧ LS) → TL4)
    (hTR1 : (R1 ∧ RS) → TR1)
    (hTR2 : (R2 ∧ RS) → TR2)
    (hTR3 : (R3 ∧ RS) → TR3)
    (hTR4 : (R4 ∧ RS) → TR4)
    (hPL1 : TL1 → LL4 ∨ LL2)
    (hPL2 : TL2 → LL4 ∨ LL2)
    (hPL3 : TL3 → LL4 ∨ LL2)
    (hPL4 : TL4 → LL4 ∨ LL2)
    (hPR1 : TR1 → RL2 ∨ RR4)
    (hPR2 : TR2 → RL2 ∨ RR4)
    (hPR3 : TR3 → RL2 ∨ RR4)
    (hPR4 : TR4 → RL2 ∨ RR4)
    (hLL4 : LL4 → (LP ∧ LS))
    (hLL2 : LL2 → (LP ∧ LS))
    (hRL2 : RL2 → (RP ∧ RS))
    (hRR4 : RR4 → (RP ∧ RS)) :
    A ∨ (LP ∧ LS) ∨ (RP ∧ RS) := by
  exact restart_kout_started_cycle_transport
    (restart_kout_started_cycle_transport
      h hL hR
      hTL1 hTL2 hTL3 hTL4
      hTR1 hTR2 hTR3 hTR4
      hPL1 hPL2 hPL3 hPL4
      hPR1 hPR2 hPR3 hPR4
      hLL4 hLL2 hRL2 hRR4)
    hL hR
    hTL1 hTL2 hTL3 hTL4
    hTR1 hTR2 hTR3 hTR4
    hPL1 hPL2 hPL3 hPL4
    hPR1 hPR2 hPR3 hPR4
    hLL4 hLL2 hRL2 hRR4

private theorem restart_kout_started_cycle_transport6
    {A LP RP LS RS : Prop}
    {L1 L2 L3 L4 R1 R2 R3 R4 : Prop}
    {TL1 TL2 TL3 TL4 TR1 TR2 TR3 TR4 : Prop}
    {LL4 LL2 RL2 RR4 : Prop}
    (h : A ∨ (LP ∧ LS) ∨ (RP ∧ RS))
    (hL : LP → L1 ∨ L2 ∨ L3 ∨ L4)
    (hR : RP → R1 ∨ R2 ∨ R3 ∨ R4)
    (hTL1 : (L1 ∧ LS) → TL1)
    (hTL2 : (L2 ∧ LS) → TL2)
    (hTL3 : (L3 ∧ LS) → TL3)
    (hTL4 : (L4 ∧ LS) → TL4)
    (hTR1 : (R1 ∧ RS) → TR1)
    (hTR2 : (R2 ∧ RS) → TR2)
    (hTR3 : (R3 ∧ RS) → TR3)
    (hTR4 : (R4 ∧ RS) → TR4)
    (hPL1 : TL1 → LL4 ∨ LL2)
    (hPL2 : TL2 → LL4 ∨ LL2)
    (hPL3 : TL3 → LL4 ∨ LL2)
    (hPL4 : TL4 → LL4 ∨ LL2)
    (hPR1 : TR1 → RL2 ∨ RR4)
    (hPR2 : TR2 → RL2 ∨ RR4)
    (hPR3 : TR3 → RL2 ∨ RR4)
    (hPR4 : TR4 → RL2 ∨ RR4)
    (hLL4 : LL4 → (LP ∧ LS))
    (hLL2 : LL2 → (LP ∧ LS))
    (hRL2 : RL2 → (RP ∧ RS))
    (hRR4 : RR4 → (RP ∧ RS)) :
    A ∨ (LP ∧ LS) ∨ (RP ∧ RS) := by
  exact restart_kout_started_cycle_transport2
    (restart_kout_started_cycle_transport2
      (restart_kout_started_cycle_transport2
        h hL hR
        hTL1 hTL2 hTL3 hTL4
        hTR1 hTR2 hTR3 hTR4
        hPL1 hPL2 hPL3 hPL4
        hPR1 hPR2 hPR3 hPR4
        hLL4 hLL2 hRL2 hRR4)
      hL hR
      hTL1 hTL2 hTL3 hTL4
      hTR1 hTR2 hTR3 hTR4
      hPL1 hPL2 hPL3 hPL4
      hPR1 hPR2 hPR3 hPR4
      hLL4 hLL2 hRL2 hRR4)
    hL hR
    hTL1 hTL2 hTL3 hTL4
    hTR1 hTR2 hTR3 hTR4
    hPL1 hPL2 hPL3 hPL4
    hPR1 hPR2 hPR3 hPR4
    hLL4 hLL2 hRL2 hRR4

private theorem restart_kout_started_cycle_transport10
    {A LP RP LS RS : Prop}
    {L1 L2 L3 L4 R1 R2 R3 R4 : Prop}
    {TL1 TL2 TL3 TL4 TR1 TR2 TR3 TR4 : Prop}
    {LL4 LL2 RL2 RR4 : Prop}
    (h : A ∨ (LP ∧ LS) ∨ (RP ∧ RS))
    (hL : LP → L1 ∨ L2 ∨ L3 ∨ L4)
    (hR : RP → R1 ∨ R2 ∨ R3 ∨ R4)
    (hTL1 : (L1 ∧ LS) → TL1)
    (hTL2 : (L2 ∧ LS) → TL2)
    (hTL3 : (L3 ∧ LS) → TL3)
    (hTL4 : (L4 ∧ LS) → TL4)
    (hTR1 : (R1 ∧ RS) → TR1)
    (hTR2 : (R2 ∧ RS) → TR2)
    (hTR3 : (R3 ∧ RS) → TR3)
    (hTR4 : (R4 ∧ RS) → TR4)
    (hPL1 : TL1 → LL4 ∨ LL2)
    (hPL2 : TL2 → LL4 ∨ LL2)
    (hPL3 : TL3 → LL4 ∨ LL2)
    (hPL4 : TL4 → LL4 ∨ LL2)
    (hPR1 : TR1 → RL2 ∨ RR4)
    (hPR2 : TR2 → RL2 ∨ RR4)
    (hPR3 : TR3 → RL2 ∨ RR4)
    (hPR4 : TR4 → RL2 ∨ RR4)
    (hLL4 : LL4 → (LP ∧ LS))
    (hLL2 : LL2 → (LP ∧ LS))
    (hRL2 : RL2 → (RP ∧ RS))
    (hRR4 : RR4 → (RP ∧ RS)) :
    A ∨ (LP ∧ LS) ∨ (RP ∧ RS) := by
  exact restart_kout_started_cycle_transport2
    (restart_kout_started_cycle_transport2
      (restart_kout_started_cycle_transport6
        h hL hR
        hTL1 hTL2 hTL3 hTL4
        hTR1 hTR2 hTR3 hTR4
        hPL1 hPL2 hPL3 hPL4
        hPR1 hPR2 hPR3 hPR4
        hLL4 hLL2 hRL2 hRR4)
      hL hR
      hTL1 hTL2 hTL3 hTL4
      hTR1 hTR2 hTR3 hTR4
      hPL1 hPL2 hPL3 hPL4
      hPR1 hPR2 hPR3 hPR4
      hLL4 hLL2 hRL2 hRR4)
    hL hR
    hTL1 hTL2 hTL3 hTL4
    hTR1 hTR2 hTR3 hTR4
    hPL1 hPL2 hPL3 hPL4
    hPR1 hPR2 hPR3 hPR4
    hLL4 hLL2 hRL2 hRR4

private theorem restart_kout_started_to_tail_transport
    {A LP RP LS RS : Prop}
    {L1 L2 L3 L4 R1 R2 R3 R4 : Prop}
    {TL1 TL2 TL3 TL4 TR1 TR2 TR3 TR4 : Prop}
    (h : A ∨ (LP ∧ LS) ∨ (RP ∧ RS))
    (hL : LP → L1 ∨ L2 ∨ L3 ∨ L4)
    (hR : RP → R1 ∨ R2 ∨ R3 ∨ R4)
    (hTL1 : (L1 ∧ LS) → TL1)
    (hTL2 : (L2 ∧ LS) → TL2)
    (hTL3 : (L3 ∧ LS) → TL3)
    (hTL4 : (L4 ∧ LS) → TL4)
    (hTR1 : (R1 ∧ RS) → TR1)
    (hTR2 : (R2 ∧ RS) → TR2)
    (hTR3 : (R3 ∧ RS) → TR3)
    (hTR4 : (R4 ∧ RS) → TR4) :
    A ∨ TL1 ∨ TL2 ∨ TL3 ∨ TL4 ∨ TR1 ∨ TR2 ∨ TR3 ∨ TR4 := by
  have hexact :
      A ∨ (L1 ∧ LS) ∨ (L2 ∧ LS) ∨ (L3 ∧ LS) ∨ (L4 ∧ LS) ∨
        (R1 ∧ RS) ∨ (R2 ∧ RS) ∨ (R3 ∧ RS) ∨ (R4 ∧ RS) :=
    grouped_restart_exact_split_transport h hL hR
  exact nine_way_transport hexact hTL1 hTL2 hTL3 hTL4 hTR1 hTR2 hTR3 hTR4

/-! ### Core EC lemmas -/

theorem phase_context_match_ec
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (phase : TernaryPhase gc t)
    (k : Fin gc.configs.length)
    (hk_ge : phase.a.val < k.val) (hk_lt : k.val < phase.s.val)
    (hL : (gc.configs.get k) (left t) = (gc.configs.get phase.s) (left t))
    (hR : (gc.configs.get k) (right t) = (gc.configs.get phase.s) (right t)) :
    hasEntryConflict gc :=
  ⟨phase.s, k, t, phase.hs_mover,
   phase.ht_nofire k (by omega) hk_lt,
   hL.symm,
   (configVal_eq_of_noFire_between gc t k.val phase.s.val
     (Nat.le_of_lt hk_lt) phase.s.isLt
     (fun j hj1 hj2 => phase.ht_nofire j (by omega) hj2)).symm,
   hR.symm⟩

theorem phase_even_remaining_ec
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (hbL : sys.rs.m (left t) = 2) (hbR : sys.rs.m (right t) = 2)
    (phase : TernaryPhase gc t)
    (k : Fin gc.configs.length)
    (hk_ge : phase.a.val < k.val) (hk_lt : k.val < phase.s.val)
    (hL_even : Even (gc.intervalFireCount (left t) k.val phase.s.val))
    (hR_even : Even (gc.intervalFireCount (right t) k.val phase.s.val)) :
    hasEntryConflict gc := by
  have hL := binary_config_eq_of_even_intervalFireCount gc (left t) hbL
    k.val phase.s.val (Nat.le_of_lt hk_lt) phase.s.isLt hL_even
  have hR := binary_config_eq_of_even_intervalFireCount gc (right t) hbR
    k.val phase.s.val (Nat.le_of_lt hk_lt) phase.s.isLt hR_even
  exact ⟨phase.s, k, t, phase.hs_mover,
    phase.ht_nofire k (by omega) hk_lt, hL.symm,
    (configVal_eq_of_noFire_between gc t k.val phase.s.val
      (Nat.le_of_lt hk_lt) phase.s.isLt
      (fun j hj1 hj2 => phase.ht_nofire j (by omega) hj2)).symm,
    hR.symm⟩

theorem post_firing_match_ec
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (post s₂ : Fin gc.configs.length)
    (hpost_lt : post.val < s₂.val)
    (hpost_nonmover : gc.moverAt post ≠ t)
    (hs₂_mover : gc.moverAt s₂ = t)
    (ht_nofire : ∀ k : Fin gc.configs.length,
      post.val ≤ k.val → k.val < s₂.val → gc.moverAt k ≠ t)
    (hL : (gc.configs.get post) (left t) = (gc.configs.get s₂) (left t))
    (hR : (gc.configs.get post) (right t) = (gc.configs.get s₂) (right t)) :
    hasEntryConflict gc := by
  have hS : (gc.configs.get post) t = (gc.configs.get s₂) t :=
    configVal_eq_of_noFire_between gc t post.val s₂.val
      (Nat.le_of_lt hpost_lt) s₂.isLt ht_nofire
  exact ⟨s₂, post, t, hs₂_mover, hpost_nonmover, hL.symm, hS.symm, hR.symm⟩

private theorem exists_first_fire_in_interval
    (gc : GoodCycle sys) (p : Fin sys.rs.n)
    (a b : Nat) (hab : a ≤ b) (hb : b < gc.configs.length)
    (hfc : gc.intervalFireCount p a b ≥ 1) :
    ∃ k : Fin gc.configs.length, a ≤ k.val ∧ k.val < b ∧ gc.moverAt k = p ∧
      ∀ j : Fin gc.configs.length, a ≤ j.val → j.val < k.val → gc.moverAt j ≠ p := by
  classical
  let S := (Finset.univ : Finset (Fin gc.configs.length)).filter
    (fun k => a ≤ k.val ∧ k.val < b ∧ gc.moverAt k = p)
  have hne : S.Nonempty := by
    by_contra hempty; simp only [Finset.not_nonempty_iff_eq_empty] at hempty
    have : gc.intervalFireCount p a b = 0 :=
      intervalFireCount_eq_zero_of_noFire gc p hab (by omega)
        (fun k hka hkb hmov => by
          have : k ∈ S := by simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨hka, hkb, hmov⟩
          simp [hempty] at this)
    omega
  let kmin := S.min' hne
  have hm : kmin ∈ S := Finset.min'_mem S hne
  simp [S] at hm; obtain ⟨hka, hkb, hkmov⟩ := hm
  exact ⟨kmin, hka, hkb, hkmov, fun j hja hjk hjmov => by
    have : j ∈ S := by simp [S, hja, hjmov]; omega
    have := Finset.min'_le S j this; omega⟩

private theorem exists_later_firing (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (hfc2 : gc.fireCount t ≥ 2)
    (s₁ : Fin gc.configs.length) (hs₁ : gc.moverAt s₁ = t)
    (hs₁_first : ∀ k : Fin gc.configs.length, k.val < s₁.val → gc.moverAt k ≠ t) :
    ∃ s₂ : Fin gc.configs.length, s₁.val < s₂.val ∧ gc.moverAt s₂ = t := by
  by_contra hall; push_neg at hall
  have honly : ∀ k : Fin gc.configs.length, gc.moverAt k = t → k = s₁ := by
    intro k hk; by_contra hne
    rcases Nat.lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with h | h
    · exact absurd hk (hs₁_first k h)
    · exact absurd hk (hall k h)
  have : gc.fireCount t = 1 := by
    rw [gc.fireCount_eq_sum_moverAt t]
    have hsub : ∀ k : Fin gc.configs.length,
        (if gc.moverAt k = t then (1:Nat) else 0) = (if k = s₁ then 1 else 0) := by
      intro k; by_cases hk : gc.moverAt k = t
      · rw [if_pos hk, if_pos (honly k hk)]
      · rw [if_neg hk]; by_cases hks : k = s₁
        · subst hks; contradiction
        · rw [if_neg hks]
    simp_rw [hsub, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  omega

/-! ### Main theorem -/

set_option maxHeartbeats 1000000 in
theorem allNormalForm_false
    (gc : GoodCycle sys) (_hn : sys.rs.n ≥ 9)
    (_hconv : converges sys gc)
    (_hno_safe : ¬∃ q : Fin sys.rs.n, ∀ k : Fin gc.configs.length,
      gc.moverAt k ≠ q ∧ gc.moverAt k ≠ left q ∧ gc.moverAt k ≠ right q)
    (_hsub : subThreshold sys.rs) (_h3bin : hasGe3Binary sys.rs)
    (t : Fin sys.rs.n)
    (hbL : sys.rs.m (left t) = 2) (hbR : sys.rs.m (right t) = 2)
    (hfull : ∀ p : Fin sys.rs.n, gc.fireCount p > 0)
    (hfc2 : gc.fireCount t ≥ 2)
    (hfc_lt : gc.fireCount t < gc.configs.length)
    (hall_normal : ∀ phase : TernaryPhase gc t,
      isNormalFormGap gc t phase) :
    False := by
  by_cases hall5 : ∀ k : Fin gc.configs.length,
      gc.moverAt k = left (left t) ∨
      gc.moverAt k = left t ∨
      gc.moverAt k = t ∨
      gc.moverAt k = right t ∨
      gc.moverAt k = right (right t)
  · exact movers_in_five_contradicts_hno_safe gc (by omega) _hno_safe t hall5
  · push_neg at hall5
    let outsideSet : Finset (Fin gc.configs.length) :=
      (Finset.univ : Finset (Fin gc.configs.length)).filter
        (fun k =>
          gc.moverAt k ≠ left (left t) ∧
          gc.moverAt k ≠ left t ∧
          gc.moverAt k ≠ t ∧
          gc.moverAt k ≠ right t ∧
          gc.moverAt k ≠ right (right t))
    have houtside_ne : outsideSet.Nonempty := by
      obtain ⟨k0, hkll, hkl, hkt, hkr, hkrr⟩ := hall5
      exact ⟨k0, by simp [outsideSet, hkll, hkl, hkt, hkr, hkrr]⟩
    obtain ⟨k_out, hk_out_mem, hk_out_max⟩ :=
      Finset.exists_max_image outsideSet Fin.val houtside_ne
    have hk_outside :
        gc.moverAt k_out ≠ left (left t) ∧
        gc.moverAt k_out ≠ left t ∧
        gc.moverAt k_out ≠ t ∧
        gc.moverAt k_out ≠ right t ∧
        gc.moverAt k_out ≠ right (right t) := by
      simp [outsideSet] at hk_out_mem
      exact hk_out_mem
    have hk_out_last :
        ∀ k : Fin gc.configs.length,
          k_out.val < k.val →
          gc.moverAt k = left (left t) ∨
          gc.moverAt k = left t ∨
          gc.moverAt k = t ∨
          gc.moverAt k = right t ∨
          gc.moverAt k = right (right t) := by
      intro k hkgt
      by_cases hlocal :
          gc.moverAt k = left (left t) ∨
          gc.moverAt k = left t ∨
          gc.moverAt k = t ∨
          gc.moverAt k = right t ∨
          gc.moverAt k = right (right t)
      · exact hlocal
      · exfalso
        have hmem : k ∈ outsideSet := by
          refine Finset.mem_filter.mpr ?_
          refine ⟨Finset.mem_univ k, ?_⟩
          push_neg at hlocal
          exact hlocal
        have := hk_out_max k hmem
        omega
    have houtside_phase :
        (∃ phase0 : TernaryPhase gc t,
          phase0.a = k_out ∧
          ∃ a0 : Fin gc.configs.length,
            phase0.a.val ≤ a0.val ∧
            a0.val < phase0.s.val ∧
            gc.moverAt a0 ≠ left (left t) ∧
            gc.moverAt a0 ≠ left t ∧
            gc.moverAt a0 ≠ t ∧
            gc.moverAt a0 ≠ right t ∧
            gc.moverAt a0 ≠ right (right t) ∧
            ∀ k : Fin gc.configs.length,
              a0.val < k.val → k.val < phase0.s.val →
              gc.moverAt k = left (left t) ∨
              gc.moverAt k = left t ∨
              gc.moverAt k = right t ∨
              gc.moverAt k = right (right t)) ∨
        (¬∃ s : Fin gc.configs.length, k_out.val < s.val ∧ gc.moverAt s = t) := by
      by_cases hafter : ∃ s : Fin gc.configs.length, k_out.val < s.val ∧ gc.moverAt s = t
      · left
        have hkt : gc.moverAt k_out ≠ t := by
          simp [outsideSet] at hk_out_mem
          exact hk_out_mem.2.2.1
        obtain ⟨phase0, hphase0a⟩ :=
          exists_ternaryPhase_starting_at gc t k_out hkt hafter
        rcases phase_last_outside_or_all_local gc t phase0 with hall_local | hlast
        · exfalso
          have hk_local := hall_local k_out (by simpa [hphase0a]) (by
            simpa [hphase0a] using phase0.ha_lt_s)
          have hkll : gc.moverAt k_out ≠ left (left t) := by
            simp [outsideSet] at hk_out_mem
            exact hk_out_mem.1
          have hkl : gc.moverAt k_out ≠ left t := by
            simp [outsideSet] at hk_out_mem
            exact hk_out_mem.2.1
          have hkr : gc.moverAt k_out ≠ right t := by
            simp [outsideSet] at hk_out_mem
            exact hk_out_mem.2.2.2.1
          have hkrr : gc.moverAt k_out ≠ right (right t) := by
            simp [outsideSet] at hk_out_mem
            exact hk_out_mem.2.2.2.2
          rcases hk_local with hk | hk | hk | hk
          · exact hkll hk
          · exact hkl hk
          · exact hkr hk
          · exact hkrr hk
        · rcases hlast with ⟨a0, ha0_ge, ha0_lt, ha0_ll, ha0_l, ha0_t, ha0_r, ha0_rr, htail⟩
          have ha0_eq : a0 = k_out := by
            by_cases hEq : a0 = k_out
            · exact hEq
            have hkout_lt_a0 : k_out.val < a0.val := by
              have hneqval : a0.val ≠ k_out.val := by
                intro hval
                exact hEq (Fin.ext hval)
              omega
            have ha0_local := hk_out_last a0 hkout_lt_a0
            rcases ha0_local with hk | hk | hk | hk | hk
            · exact False.elim (ha0_ll hk)
            · exact False.elim (ha0_l hk)
            · exact False.elim (ha0_t hk)
            · exact False.elim (ha0_r hk)
            · exact False.elim (ha0_rr hk)
          refine ⟨phase0, hphase0a, k_out, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · simpa [hphase0a] using ha0_ge
          · simpa [ha0_eq] using ha0_lt
          · simpa [ha0_eq] using ha0_ll
          · simpa [ha0_eq] using ha0_l
          · simpa [ha0_eq] using ha0_t
          · simpa [ha0_eq] using ha0_r
          · simpa [ha0_eq] using ha0_rr
          · simpa [ha0_eq] using htail
      · exact Or.inr hafter
    have houtside_refined :
        (∃ phase0 : TernaryPhase gc t,
          phase0.a = k_out ∧
          ∃ a0 : Fin gc.configs.length,
            phase0.a.val ≤ a0.val ∧
            a0.val < phase0.s.val ∧
            gc.moverAt a0 ≠ left (left t) ∧
            gc.moverAt a0 ≠ left t ∧
            gc.moverAt a0 ≠ t ∧
            gc.moverAt a0 ≠ right t ∧
            gc.moverAt a0 ≠ right (right t) ∧
            (∀ k : Fin gc.configs.length,
              a0.val < k.val → k.val < phase0.s.val →
              gc.moverAt k = left (left t) ∨
              gc.moverAt k = left t ∨
              gc.moverAt k = right t ∨
              gc.moverAt k = right (right t)) ∧
            ∃ a1 : Fin gc.configs.length,
              a0.val < a1.val ∧
              a1.val < phase0.s.val ∧
              ((gc.moverAt a0 = left (left (left t)) ∧
                gc.moverAt a1 = left (left t)) ∨
               (gc.moverAt a0 = right (right (right t)) ∧
                gc.moverAt a1 = right (right t)))) ∨
        (¬∃ s : Fin gc.configs.length, k_out.val < s.val ∧ gc.moverAt s = t) := by
      rcases houtside_phase with hphase | hwrap
      · left
        rcases hphase with ⟨phase0, hphase0a, a0, ha0_ge, ha0_lt, ha0_ll, ha0_l, ha0_t, ha0_r, ha0_rr, htail⟩
        rcases normal_phase_has_localized_short_suffix_or_ec gc t hall_normal phase0 with hec | hshort
        · exact False.elim (entryConflict_impossible gc hec)
        · rcases hshort with ⟨phase1, hs1, hlen1, hstart1, _hloc1⟩
          have ha0_lt_phase1a : a0.val < phase1.a.val := by
            by_contra hge
            have hEqVal : a0.val = phase1.a.val := by omega
            have hEq : a0 = phase1.a := Fin.ext hEqVal
            rcases hstart1 with hL | hR
            · exact ha0_l (by simpa [hEq] using hL)
            · exact ha0_r (by simpa [hEq] using hR)
          have hphase1_a : phase1.a.val = phase0.s.val - 1 := by
            have hs1_val : phase1.s.val = phase0.s.val := by
              simpa using congrArg Fin.val hs1
            rw [hs1_val] at hlen1
            omega
          have ha1_lt_s : a0.val + 1 < phase0.s.val := by
            rw [hphase1_a] at ha0_lt_phase1a
            omega
          have ha1_lt_len : a0.val + 1 < gc.configs.length := by
            exact lt_trans ha1_lt_s phase0.s.isLt
          let a1 : Fin gc.configs.length := ⟨a0.val + 1, ha1_lt_len⟩
          have ha1_gt : a0.val < a1.val := by
            dsimp [a1]
            omega
          have ha1_lt_phase : a1.val < phase0.s.val := by
            dsimp [a1]
            exact ha1_lt_s
          have ha1_local := htail a1 ha1_gt ha1_lt_phase
          have ha1_eq_next : nextIndex gc.configs a0 = a1 := by
            apply Fin.ext
            simp [nextIndex, a1]
            exact Nat.mod_eq_of_lt ha1_lt_len
          have hnext_local := gc.next_mover_is_local a0
          rw [ha1_eq_next] at hnext_local
          have hentry_side :
              (gc.moverAt a0 = left (left (left t)) ∧ gc.moverAt a1 = left (left t)) ∨
              (gc.moverAt a0 = right (right (right t)) ∧ gc.moverAt a1 = right (right t)) := by
            rcases ha1_local with ha1ll | ha1l | ha1r | ha1rr
            · rcases hnext_local with hleft | hself | hright
              · exfalso
                have : gc.moverAt a0 = left t := by
                  have htmp : left t = gc.moverAt a0 := by
                    simpa [ha1ll, right_left_eq_self] using congrArg right hleft
                  exact htmp.symm
                exact ha0_l this
              · exfalso
                exact ha0_ll (by simpa [ha1ll] using hself.symm)
              · have htmp : left (left (left t)) = gc.moverAt a0 := by
                  simpa [ha1ll, left_right_eq_self] using congrArg left hright
                exact Or.inl ⟨htmp.symm, ha1ll⟩
            · rcases hnext_local with hleft | hself | hright
              · exfalso
                have : gc.moverAt a0 = t := by
                  have htmp : t = gc.moverAt a0 := by
                    simpa [ha1l, right_left_eq_self] using congrArg right hleft
                  exact htmp.symm
                exact ha0_t this
              · exfalso
                exact ha0_l (by simpa [ha1l] using hself.symm)
              · exfalso
                have : gc.moverAt a0 = left (left t) := by
                  have htmp : left (left t) = gc.moverAt a0 := by
                    simpa [ha1l, left_right_eq_self] using congrArg left hright
                  exact htmp.symm
                exact ha0_ll this
            · rcases hnext_local with hleft | hself | hright
              · exfalso
                have : gc.moverAt a0 = right (right t) := by
                  have htmp : right (right t) = gc.moverAt a0 := by
                    simpa [ha1r, right_left_eq_self] using congrArg right hleft
                  exact htmp.symm
                exact ha0_rr this
              · exfalso
                exact ha0_r (by simpa [ha1r] using hself.symm)
              · exfalso
                have : gc.moverAt a0 = t := by
                  have htmp : t = gc.moverAt a0 := by
                    simpa [ha1r, left_right_eq_self] using congrArg left hright
                  exact htmp.symm
                exact ha0_t this
            · rcases hnext_local with hleft | hself | hright
              · have htmp : right (right (right t)) = gc.moverAt a0 := by
                  simpa [ha1rr, right_left_eq_self] using congrArg right hleft
                exact Or.inr ⟨htmp.symm, ha1rr⟩
              · exfalso
                exact ha0_rr (by simpa [ha1rr] using hself.symm)
              · exfalso
                have : gc.moverAt a0 = right t := by
                  have htmp : right t = gc.moverAt a0 := by
                    simpa [ha1rr, left_right_eq_self] using congrArg left hright
                  exact htmp.symm
                exact ha0_r this
          exact ⟨phase0, hphase0a, a0, ha0_ge, ha0_lt, ha0_ll, ha0_l, ha0_t, ha0_r, ha0_rr,
            htail, a1, ha1_gt, ha1_lt_phase, hentry_side⟩
      · exact Or.inr hwrap
    have hk_out_suffix_six_or_last :
        (k_out.val + 1 = gc.configs.length) ∨
        ((∀ k : Fin gc.configs.length,
            k_out.val ≤ k.val →
            gc.moverAt k = left (left (left t)) ∨
            gc.moverAt k = left (left t) ∨
            gc.moverAt k = left t ∨
            gc.moverAt k = t ∨
            gc.moverAt k = right t ∨
            gc.moverAt k = right (right t)) ∨
         (∀ k : Fin gc.configs.length,
            k_out.val ≤ k.val →
            gc.moverAt k = left (left t) ∨
            gc.moverAt k = left t ∨
            gc.moverAt k = t ∨
            gc.moverAt k = right t ∨
            gc.moverAt k = right (right t) ∨
            gc.moverAt k = right (right (right t)))) := by
      by_cases hk_last : k_out.val + 1 = gc.configs.length
      · exact Or.inl hk_last
      · have hk1_lt : k_out.val + 1 < gc.configs.length := by omega
        let a1 : Fin gc.configs.length := ⟨k_out.val + 1, hk1_lt⟩
        have ha1_eq_next : nextIndex gc.configs k_out = a1 := by
          apply Fin.ext
          simp [nextIndex, a1]
          exact Nat.mod_eq_of_lt hk1_lt
        have ha1_local :
            gc.moverAt a1 = left (left t) ∨
            gc.moverAt a1 = left t ∨
            gc.moverAt a1 = t ∨
            gc.moverAt a1 = right t ∨
            gc.moverAt a1 = right (right t) := by
          exact hk_out_last a1 (by
            dsimp [a1]
            omega)
        have hside :
            gc.moverAt k_out = left (left (left t)) ∨
            gc.moverAt k_out = right (right (right t)) :=
          outside_step_followed_by_local_five_forces_side gc t k_out a1
            ha1_eq_next hk_outside ha1_local
        exact Or.inr (last_outside_suffix_in_left_or_right_six gc t k_out hside hk_out_last)
    have houtside_suffix_six :
        (∃ phase0 : TernaryPhase gc t,
          phase0.a = k_out ∧
          ((∀ k : Fin gc.configs.length,
              k_out.val ≤ k.val →
              gc.moverAt k = left (left (left t)) ∨
              gc.moverAt k = left (left t) ∨
              gc.moverAt k = left t ∨
              gc.moverAt k = t ∨
              gc.moverAt k = right t ∨
              gc.moverAt k = right (right t)) ∨
           (∀ k : Fin gc.configs.length,
              k_out.val ≤ k.val →
              gc.moverAt k = left (left t) ∨
              gc.moverAt k = left t ∨
              gc.moverAt k = t ∨
              gc.moverAt k = right t ∨
              gc.moverAt k = right (right t) ∨
              gc.moverAt k = right (right (right t))))) ∨
        (¬∃ s : Fin gc.configs.length, k_out.val < s.val ∧ gc.moverAt s = t) := by
      rcases houtside_refined with hphase | hwrap
      · left
        rcases hphase with ⟨phase0, hphase0a, a0, ha0_ge, ha0_lt, ha0_ll, ha0_l, ha0_t, ha0_r, ha0_rr,
          htail, a1, ha1_gt, ha1_lt, hentry_side⟩
        have ha0_eq : a0 = k_out := by
          by_cases hEq : a0 = k_out
          · exact hEq
          have hkout_lt_a0 : k_out.val < a0.val := by
            have hneqval : a0.val ≠ k_out.val := by
              intro hval
              exact hEq (Fin.ext hval)
            omega
          have ha0_local := hk_out_last a0 hkout_lt_a0
          rcases ha0_local with hk | hk | hk | hk | hk
          · exact False.elim (ha0_ll hk)
          · exact False.elim (ha0_l hk)
          · exact False.elim (ha0_t hk)
          · exact False.elim (ha0_r hk)
          · exact False.elim (ha0_rr hk)
        have ha0_side :
            gc.moverAt k_out = left (left (left t)) ∨
            gc.moverAt k_out = right (right (right t)) := by
          rcases hentry_side with hleft | hright
          · exact Or.inl (by simpa [ha0_eq] using hleft.1)
          · exact Or.inr (by simpa [ha0_eq] using hright.1)
        have htail_one_sided :
            (∀ k : Fin gc.configs.length,
              k_out.val ≤ k.val → k.val < phase0.s.val →
              gc.moverAt k = left (left (left t)) ∨
              gc.moverAt k = left (left t) ∨
              gc.moverAt k = left t) ∨
            (∀ k : Fin gc.configs.length,
              k_out.val ≤ k.val → k.val < phase0.s.val →
              gc.moverAt k = right t ∨
              gc.moverAt k = right (right t) ∨
              gc.moverAt k = right (right (right t))) := by
          apply last_outside_phase_tail_one_sided gc t phase0 (by omega) k_out
          · simpa [hphase0a] using ha0_ge
          · simpa [ha0_eq] using ha0_lt
          · exact ha0_side
          · simpa [ha0_eq] using htail
        have hsix := last_outside_suffix_in_left_or_right_six gc t k_out ha0_side hk_out_last
        have _htail_one_sided := htail_one_sided
        exact ⟨phase0, hphase0a, hsix⟩
      · exact Or.inr hwrap
    have hwrap_tail_one_sided_or_last :
        (¬∃ s : Fin gc.configs.length, k_out.val < s.val ∧ gc.moverAt s = t) →
        (k_out.val + 1 = gc.configs.length) ∨
        ((∀ k : Fin gc.configs.length,
            k_out.val ≤ k.val →
            gc.moverAt k = left (left (left t)) ∨
            gc.moverAt k = left (left t) ∨
            gc.moverAt k = left t) ∨
         (∀ k : Fin gc.configs.length,
            k_out.val ≤ k.val →
            gc.moverAt k = right t ∨
            gc.moverAt k = right (right t) ∨
            gc.moverAt k = right (right (right t)))) := by
      intro hwrap
      exact last_outside_no_t_suffix_one_sided_or_last gc t (by omega) k_out
        hk_outside hk_out_last (fun k hkgt hkt => hwrap ⟨k, hkgt, hkt⟩)
    have hresidue_geometric :
        (k_out.val + 1 = gc.configs.length) ∨
        (∃ j : Fin gc.configs.length,
          j.val < k_out.val ∧
          (gc.moverAt j = left (left (left (left t))) ∨
            gc.moverAt j = right (right (right t))) ∧
          (∀ k : Fin gc.configs.length,
            j.val < k.val →
            gc.moverAt k = left (left (left t)) ∨
            gc.moverAt k = left (left t) ∨
            gc.moverAt k = left t ∨
            gc.moverAt k = t ∨
            gc.moverAt k = right t ∨
            gc.moverAt k = right (right t))) ∨
        (∃ j : Fin gc.configs.length,
          j.val < k_out.val ∧
          (gc.moverAt j = left (left (left t)) ∨
            gc.moverAt j = right (right (right (right t)))) ∧
          (∀ k : Fin gc.configs.length,
            j.val < k.val →
            gc.moverAt k = left (left t) ∨
            gc.moverAt k = left t ∨
            gc.moverAt k = t ∨
            gc.moverAt k = right t ∨
            gc.moverAt k = right (right t) ∨
            gc.moverAt k = right (right (right t)))) := by
      rcases houtside_suffix_six with hphase | hwrap
      · rcases hphase with ⟨phase0, hphase0a, hsix⟩
        rcases hsix with hleftsix | hrightsix
        · rcases all_left_six_or_prefix_bad_left4_or_right3_strong gc t k_out hleftsix with hall | hprefix
          · exfalso
            exact movers_in_left_six_contradicts_hno_safe gc _hn _hno_safe t hall
          · exact Or.inr (Or.inl hprefix)
        · rcases all_right_six_or_prefix_bad_left3_or_right4_strong gc t k_out hrightsix with hall | hprefix
          · exfalso
            exact movers_in_right_six_contradicts_hno_safe gc _hn _hno_safe t hall
          · exact Or.inr (Or.inr hprefix)
      · rcases hwrap_tail_one_sided_or_last hwrap with hk_last | htail_side
        · exact Or.inl hk_last
        · rcases htail_side with hleft3 | hright3
          · have hleftsix :
                ∀ k : Fin gc.configs.length,
                  k_out.val ≤ k.val →
                  gc.moverAt k = left (left (left t)) ∨
                    gc.moverAt k = left (left t) ∨
                    gc.moverAt k = left t ∨
                    gc.moverAt k = t ∨
                    gc.moverAt k = right t ∨
                    gc.moverAt k = right (right t) := by
              intro k hk_ge
              rcases hleft3 k hk_ge with hk | hk | hk
              · exact Or.inl hk
              · exact Or.inr (Or.inl hk)
              · exact Or.inr (Or.inr (Or.inl hk))
            rcases all_left_six_or_prefix_bad_left4_or_right3_strong gc t k_out hleftsix with hall | hprefix
            · exfalso
              exact movers_in_left_six_contradicts_hno_safe gc _hn _hno_safe t hall
            · exact Or.inr (Or.inl hprefix)
          · have hrightsix :
                ∀ k : Fin gc.configs.length,
                  k_out.val ≤ k.val →
                  gc.moverAt k = left (left t) ∨
                    gc.moverAt k = left t ∨
                    gc.moverAt k = t ∨
                    gc.moverAt k = right t ∨
                    gc.moverAt k = right (right t) ∨
                    gc.moverAt k = right (right (right t)) := by
              intro k hk_ge
              rcases hright3 k hk_ge with hk | hk | hk
              · exact Or.inr (Or.inr (Or.inr (Or.inl hk)))
              · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hk))))
              · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hk))))
            rcases all_right_six_or_prefix_bad_left3_or_right4_strong gc t k_out hrightsix with hall | hprefix
            · exfalso
              exact movers_in_right_six_contradicts_hno_safe gc _hn _hno_safe t hall
            · exact Or.inr (Or.inr hprefix)
    let LeftResidue : Prop :=
      (gc.moverAt k_out = left (left (left t))) ∧
      ∃ j : Fin gc.configs.length,
        j.val < k_out.val ∧
        (gc.moverAt j = left (left (left (left t))) ∨
          gc.moverAt j = right (right (right t))) ∧
        (∀ k : Fin gc.configs.length,
          j.val < k.val →
          gc.moverAt k = left (left (left t)) ∨
            gc.moverAt k = left (left t) ∨
            gc.moverAt k = left t ∨
            gc.moverAt k = t ∨
            gc.moverAt k = right t ∨
            gc.moverAt k = right (right t))
    let RightResidue : Prop :=
      (gc.moverAt k_out = right (right (right t))) ∧
      ∃ j : Fin gc.configs.length,
        j.val < k_out.val ∧
        (gc.moverAt j = left (left (left t)) ∨
          gc.moverAt j = right (right (right (right t)))) ∧
        (∀ k : Fin gc.configs.length,
          j.val < k.val →
          gc.moverAt k = left (left t) ∨
            gc.moverAt k = left t ∨
            gc.moverAt k = t ∨
            gc.moverAt k = right t ∨
            gc.moverAt k = right (right t) ∨
            gc.moverAt k = right (right (right t)))
    have hresidue_oriented :
        (k_out.val + 1 = gc.configs.length) ∨ LeftResidue ∨ RightResidue := by
      rcases hresidue_geometric with hk_last | hleft | hright
      · exact Or.inl hk_last
      · rcases hleft with ⟨j, hj_lt, hj_edge, hj_tail⟩
        have hk_tail := hj_tail k_out hj_lt
        have hk_left3 : gc.moverAt k_out = left (left (left t)) := by
          rcases hk_tail with hk | hk | hk | hk | hk | hk
          · exact hk
          · exact False.elim (hk_outside.1 hk)
          · exact False.elim (hk_outside.2.1 hk)
          · exact False.elim (hk_outside.2.2.1 hk)
          · exact False.elim (hk_outside.2.2.2.1 hk)
          · exact False.elim (hk_outside.2.2.2.2 hk)
        exact Or.inr (Or.inl ⟨hk_left3, j, hj_lt, hj_edge, hj_tail⟩)
      · rcases hright with ⟨j, hj_lt, hj_edge, hj_tail⟩
        have hk_tail := hj_tail k_out hj_lt
        have hk_right3 : gc.moverAt k_out = right (right (right t)) := by
          rcases hk_tail with hk | hk | hk | hk | hk | hk
          · exact False.elim (hk_outside.1 hk)
          · exact False.elim (hk_outside.2.1 hk)
          · exact False.elim (hk_outside.2.2.1 hk)
          · exact False.elim (hk_outside.2.2.2.1 hk)
          · exact False.elim (hk_outside.2.2.2.2 hk)
          · exact hk
        exact Or.inr (Or.inr ⟨hk_right3, j, hj_lt, hj_edge, hj_tail⟩)
    let LeftSharp : Prop :=
      ∃ j j1 : Fin gc.configs.length,
        j.val < k_out.val ∧
        j1.val = j.val + 1 ∧
        ((gc.moverAt j = left (left (left (left t))) ∧
            gc.moverAt j1 = left (left (left t))) ∨
          (gc.moverAt j = right (right (right t)) ∧
            gc.moverAt j1 = right (right t))) ∧
        (∀ k : Fin gc.configs.length,
          j.val < k.val →
          gc.moverAt k = left (left (left t)) ∨
            gc.moverAt k = left (left t) ∨
            gc.moverAt k = left t ∨
            gc.moverAt k = t ∨
            gc.moverAt k = right t ∨
            gc.moverAt k = right (right t))
    let RightSharp : Prop :=
      ∃ j j1 : Fin gc.configs.length,
        j.val < k_out.val ∧
        j1.val = j.val + 1 ∧
        ((gc.moverAt j = left (left (left t)) ∧
            gc.moverAt j1 = left (left t)) ∨
          (gc.moverAt j = right (right (right (right t))) ∧
            gc.moverAt j1 = right (right (right t)))) ∧
        (∀ k : Fin gc.configs.length,
          j.val < k.val →
          gc.moverAt k = left (left t) ∨
            gc.moverAt k = left t ∨
            gc.moverAt k = t ∨
            gc.moverAt k = right t ∨
            gc.moverAt k = right (right t) ∨
            gc.moverAt k = right (right (right t)))
    have hresidue_sharp :
        (k_out.val + 1 = gc.configs.length) ∨ LeftSharp ∨ RightSharp := by
      rcases hresidue_oriented with hk_last | hleft | hright
      · exact Or.inl hk_last
      · rcases hleft with ⟨_hk_left3, j, hj_lt, hj_edge, hj_tail⟩
        have hj1_lt_len : j.val + 1 < gc.configs.length := by
          have : j.val + 1 ≤ k_out.val := by omega
          exact lt_of_le_of_lt this k_out.isLt
        let j1 : Fin gc.configs.length := ⟨j.val + 1, hj1_lt_len⟩
        have hsucc :=
          left_prefix_edge_successor_shape gc t (by omega) j hj1_lt_len hj_edge hj_tail
        exact Or.inr (Or.inl ⟨j, j1, hj_lt, rfl, hsucc, hj_tail⟩)
      · rcases hright with ⟨_hk_right3, j, hj_lt, hj_edge, hj_tail⟩
        have hj1_lt_len : j.val + 1 < gc.configs.length := by
          have : j.val + 1 ≤ k_out.val := by omega
          exact lt_of_le_of_lt this k_out.isLt
        let j1 : Fin gc.configs.length := ⟨j.val + 1, hj1_lt_len⟩
        have hsucc :=
          right_prefix_edge_successor_shape gc t (by omega) j hj1_lt_len hj_edge hj_tail
        exact Or.inr (Or.inr ⟨j, j1, hj_lt, rfl, hsucc, hj_tail⟩)
    let LeftFromLeft4 : Prop :=
      ∃ j j1 : Fin gc.configs.length,
        j.val < k_out.val ∧
        j1.val = j.val + 1 ∧
        gc.moverAt j = left (left (left (left t))) ∧
        gc.moverAt j1 = left (left (left t)) ∧
        (∀ k : Fin gc.configs.length,
          j.val < k.val →
          gc.moverAt k = left (left (left t)) ∨
            gc.moverAt k = left (left t) ∨
            gc.moverAt k = left t ∨
            gc.moverAt k = t ∨
            gc.moverAt k = right t ∨
            gc.moverAt k = right (right t))
    let LeftFromRight3 : Prop :=
      ∃ j j1 : Fin gc.configs.length,
        j.val < k_out.val ∧
        j1.val = j.val + 1 ∧
        gc.moverAt j = right (right (right t)) ∧
        gc.moverAt j1 = right (right t) ∧
        (∀ k : Fin gc.configs.length,
          j.val < k.val →
          gc.moverAt k = left (left (left t)) ∨
            gc.moverAt k = left (left t) ∨
            gc.moverAt k = left t ∨
            gc.moverAt k = t ∨
            gc.moverAt k = right t ∨
            gc.moverAt k = right (right t))
    let RightFromLeft3 : Prop :=
      ∃ j j1 : Fin gc.configs.length,
        j.val < k_out.val ∧
        j1.val = j.val + 1 ∧
        gc.moverAt j = left (left (left t)) ∧
        gc.moverAt j1 = left (left t) ∧
        (∀ k : Fin gc.configs.length,
          j.val < k.val →
          gc.moverAt k = left (left t) ∨
            gc.moverAt k = left t ∨
            gc.moverAt k = t ∨
            gc.moverAt k = right t ∨
            gc.moverAt k = right (right t) ∨
            gc.moverAt k = right (right (right t)))
    let RightFromRight4 : Prop :=
      ∃ j j1 : Fin gc.configs.length,
        j.val < k_out.val ∧
        j1.val = j.val + 1 ∧
        gc.moverAt j = right (right (right (right t))) ∧
        gc.moverAt j1 = right (right (right t)) ∧
        (∀ k : Fin gc.configs.length,
          j.val < k.val →
          gc.moverAt k = left (left t) ∨
            gc.moverAt k = left t ∨
            gc.moverAt k = t ∨
            gc.moverAt k = right t ∨
            gc.moverAt k = right (right t) ∨
            gc.moverAt k = right (right (right t)))
    have hresidue_patterned :
        (k_out.val + 1 = gc.configs.length) ∨
        LeftFromLeft4 ∨ LeftFromRight3 ∨ RightFromLeft3 ∨ RightFromRight4 := by
      rcases hresidue_sharp with hk_last | hleft | hright
      · exact Or.inl hk_last
      · rcases hleft with ⟨j, j1, hj_lt, hj1_succ, hshape, hj_tail⟩
        rcases hshape with hsame | hcross
        · exact Or.inr (Or.inl ⟨j, j1, hj_lt, hj1_succ, hsame.1, hsame.2, hj_tail⟩)
        · exact Or.inr (Or.inr (Or.inl ⟨j, j1, hj_lt, hj1_succ, hcross.1, hcross.2, hj_tail⟩))
      · rcases hright with ⟨j, j1, hj_lt, hj1_succ, hshape, hj_tail⟩
        rcases hshape with hsame | hcross
        · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨j, j1, hj_lt, hj1_succ, hsame.1, hsame.2, hj_tail⟩)))
        · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨j, j1, hj_lt, hj1_succ, hcross.1, hcross.2, hj_tail⟩)))
    have hk_out_left3_of_leftFromLeft4 :
        LeftFromLeft4 → gc.moverAt k_out = left (left (left t)) := by
      intro h
      rcases h with ⟨j, _j1, hj_lt, _hj1_succ, _hj, _hj1, hj_tail⟩
      exact outside_of_left_six_tail_eq_left3 gc t j k_out hj_lt hk_outside hj_tail
    have hk_out_left3_of_leftFromRight3 :
        LeftFromRight3 → gc.moverAt k_out = left (left (left t)) := by
      intro h
      rcases h with ⟨j, _j1, hj_lt, _hj1_succ, _hj, _hj1, hj_tail⟩
      exact outside_of_left_six_tail_eq_left3 gc t j k_out hj_lt hk_outside hj_tail
    have hk_out_right3_of_rightFromLeft3 :
        RightFromLeft3 → gc.moverAt k_out = right (right (right t)) := by
      intro h
      rcases h with ⟨j, _j1, hj_lt, _hj1_succ, _hj, _hj1, hj_tail⟩
      exact outside_of_right_six_tail_eq_right3 gc t j k_out hj_lt hk_outside hj_tail
    have hk_out_right3_of_rightFromRight4 :
        RightFromRight4 → gc.moverAt k_out = right (right (right t)) := by
      intro h
      rcases h with ⟨j, _j1, hj_lt, _hj1_succ, _hj, _hj1, hj_tail⟩
      exact outside_of_right_six_tail_eq_right3 gc t j k_out hj_lt hk_outside hj_tail
    let LeftFromLeft4Final : Prop :=
      gc.moverAt k_out = left (left (left t)) ∧ LeftFromLeft4
    let LeftFromRight3Final : Prop :=
      gc.moverAt k_out = left (left (left t)) ∧ LeftFromRight3
    let RightFromLeft3Final : Prop :=
      gc.moverAt k_out = right (right (right t)) ∧ RightFromLeft3
    let RightFromRight4Final : Prop :=
      gc.moverAt k_out = right (right (right t)) ∧ RightFromRight4
    have hresidue_final :
        (k_out.val + 1 = gc.configs.length) ∨
        LeftFromLeft4Final ∨ LeftFromRight3Final ∨ RightFromLeft3Final ∨ RightFromRight4Final := by
      rcases hresidue_patterned with hk_last | hLL4 | hLR3 | hRL3 | hRR4
      · exact Or.inl hk_last
      · exact Or.inr (Or.inl ⟨hk_out_left3_of_leftFromLeft4 hLL4, hLL4⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨hk_out_left3_of_leftFromRight3 hLR3, hLR3⟩))
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hk_out_right3_of_rightFromLeft3 hRL3, hRL3⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hk_out_right3_of_rightFromRight4 hRR4, hRR4⟩)))
    let LeftTailResidue : Prop :=
      ∃ cut : Fin gc.configs.length,
        cut.val ≤ k_out.val ∧
        gc.moverAt cut = left (left (left t)) ∧
        (∀ k : Fin gc.configs.length,
          cut.val ≤ k.val →
          gc.moverAt k = left (left (left t)) ∨
            gc.moverAt k = left (left t) ∨
            gc.moverAt k = left t ∨
            gc.moverAt k = t ∨
            gc.moverAt k = right t ∨
            gc.moverAt k = right (right t))
    let RightTailResidue : Prop :=
      ∃ cut : Fin gc.configs.length,
        cut.val ≤ k_out.val ∧
        gc.moverAt cut = right (right (right t)) ∧
        (∀ k : Fin gc.configs.length,
          cut.val ≤ k.val →
          gc.moverAt k = left (left t) ∨
            gc.moverAt k = left t ∨
            gc.moverAt k = t ∨
            gc.moverAt k = right t ∨
            gc.moverAt k = right (right t) ∨
            gc.moverAt k = right (right (right t)))
    have hleft_same_tail :
        LeftFromLeft4Final → LeftTailResidue := by
      intro h
      rcases h with ⟨_hk_out_left3, j, j1, hj_lt, hj1_succ, _hj_left4, hj1_left3, hj_tail⟩
      have hj1_le_kout : j1.val ≤ k_out.val := by
        rw [hj1_succ]
        omega
      refine ⟨j1, hj1_le_kout, hj1_left3, ?_⟩
      intro k hk_ge
      have hj_lt_k : j.val < k.val := by
        rw [hj1_succ] at hk_ge
        omega
      exact hj_tail k hj_lt_k
    have hright_same_tail :
        RightFromRight4Final → RightTailResidue := by
      intro h
      rcases h with ⟨_hk_out_right3, j, j1, hj_lt, hj1_succ, _hj_right4, hj1_right3, hj_tail⟩
      have hj1_le_kout : j1.val ≤ k_out.val := by
        rw [hj1_succ]
        omega
      refine ⟨j1, hj1_le_kout, hj1_right3, ?_⟩
      intro k hk_ge
      have hj_lt_k : j.val < k.val := by
        rw [hj1_succ] at hk_ge
        omega
      exact hj_tail k hj_lt_k
    have hleft_cross_tail :
        LeftFromRight3Final → LeftTailResidue := by
      intro h
      rcases h with ⟨hk_out_left3, j, j1, hj_lt, hj1_succ, hj_right3, hj1_right2, hj_tail⟩
      have hj_lt_j1 : j.val < j1.val := by
        rw [hj1_succ]
        omega
      have hj1_ne_kout : j1 ≠ k_out := by
        intro hEq
        apply right2_ne_left3 (by omega) t
        calc
          right (right t) = gc.moverAt j1 := hj1_right2.symm
          _ = gc.moverAt k_out := by rw [hEq]
          _ = left (left (left t)) := hk_out_left3
      have hj1_lt_kout : j1.val < k_out.val := by
        have hle : j1.val ≤ k_out.val := by
          rw [hj1_succ]
          omega
        have hneq : j1.val ≠ k_out.val := by
          intro hval
          exact hj1_ne_kout (Fin.ext hval)
        omega
      rcases first_left3_after_right2_in_leftsix_tail gc t (by omega) j j1 k_out
        hj_lt_j1 hj1_lt_kout hj1_right2 hk_out_left3 hj_tail with
        ⟨a, _prev, _hj1_lt_prev, _hprev_succ, ha_le_kout, _hprev_left2, ha_left3⟩
      refine ⟨a, ha_le_kout, ha_left3, ?_⟩
      intro k hk_ge
      have hj_lt_k : j.val < k.val := by
        have hj_lt_a : j.val < a.val := by omega
        omega
      exact hj_tail k hj_lt_k
    have hright_cross_tail :
        RightFromLeft3Final → RightTailResidue := by
      intro h
      rcases h with ⟨hk_out_right3, j, j1, hj_lt, hj1_succ, hj_left3, hj1_left2, hj_tail⟩
      have hj_lt_j1 : j.val < j1.val := by
        rw [hj1_succ]
        omega
      have hj1_ne_kout : j1 ≠ k_out := by
        intro hEq
        apply left2_ne_right3 (by omega) t
        calc
          left (left t) = gc.moverAt j1 := hj1_left2.symm
          _ = gc.moverAt k_out := by rw [hEq]
          _ = right (right (right t)) := hk_out_right3
      have hj1_lt_kout : j1.val < k_out.val := by
        have hle : j1.val ≤ k_out.val := by
          rw [hj1_succ]
          omega
        have hneq : j1.val ≠ k_out.val := by
          intro hval
          exact hj1_ne_kout (Fin.ext hval)
        omega
      rcases first_right3_after_left2_in_rightsix_tail gc t (by omega) j j1 k_out
        hj_lt_j1 hj1_lt_kout hj1_left2 hk_out_right3 hj_tail with
        ⟨a, _prev, _hj1_lt_prev, _hprev_succ, ha_le_kout, _hprev_right2, ha_right3⟩
      refine ⟨a, ha_le_kout, ha_right3, ?_⟩
      intro k hk_ge
      have hj_lt_k : j.val < k.val := by
        have hj_lt_a : j.val < a.val := by omega
        omega
      exact hj_tail k hj_lt_k
    have hresidue_tail :
        (k_out.val + 1 = gc.configs.length) ∨ LeftTailResidue ∨ RightTailResidue := by
      rcases hresidue_final with hk_last | hLL4 | hLR3 | hRL3 | hRR4
      · exact Or.inl hk_last
      · exact Or.inr (Or.inl (hleft_same_tail hLL4))
      · exact Or.inr (Or.inl (hleft_cross_tail hLR3))
      · exact Or.inr (Or.inr (hright_cross_tail hRL3))
      · exact Or.inr (Or.inr (hright_same_tail hRR4))
    have hleft_tail_min :
        LeftTailResidue →
        ∃ cut : Fin gc.configs.length,
          cut.val ≤ k_out.val ∧
          gc.moverAt cut = left (left (left t)) ∧
          (∀ k : Fin gc.configs.length,
            cut.val ≤ k.val →
            gc.moverAt k = left (left (left t)) ∨
              gc.moverAt k = left (left t) ∨
              gc.moverAt k = left t ∨
              gc.moverAt k = t ∨
              gc.moverAt k = right t ∨
              gc.moverAt k = right (right t)) ∧
          ∀ cut' : Fin gc.configs.length,
            cut'.val < cut.val →
            ¬ (cut'.val ≤ k_out.val ∧
              gc.moverAt cut' = left (left (left t)) ∧
              (∀ k : Fin gc.configs.length,
                cut'.val ≤ k.val →
                gc.moverAt k = left (left (left t)) ∨
                  gc.moverAt k = left (left t) ∨
                  gc.moverAt k = left t ∨
                  gc.moverAt k = t ∨
                  gc.moverAt k = right t ∨
                  gc.moverAt k = right (right t))) := by
      intro h
      rcases h with ⟨cut0, hcut0_le, hcut0_left3, hcut0_tail⟩
      let leftTailSet : Finset (Fin gc.configs.length) :=
        (Finset.univ : Finset (Fin gc.configs.length)).filter
          (fun cut =>
            cut.val ≤ k_out.val ∧
            gc.moverAt cut = left (left (left t)) ∧
            (∀ k : Fin gc.configs.length,
              cut.val ≤ k.val →
              gc.moverAt k = left (left (left t)) ∨
                gc.moverAt k = left (left t) ∨
                gc.moverAt k = left t ∨
                gc.moverAt k = t ∨
                gc.moverAt k = right t ∨
                gc.moverAt k = right (right t)))
      have hcut0_mem : cut0 ∈ leftTailSet := by
        refine Finset.mem_filter.mpr ?_
        exact ⟨Finset.mem_univ cut0, hcut0_le, hcut0_left3, hcut0_tail⟩
      obtain ⟨cut, hcut_mem, hcut_min⟩ :=
        Finset.exists_min_image leftTailSet Fin.val ⟨cut0, hcut0_mem⟩
      refine ⟨cut, ?_, ?_, ?_, ?_⟩
      · simp [leftTailSet] at hcut_mem
        exact hcut_mem.1
      · simp [leftTailSet] at hcut_mem
        exact hcut_mem.2.1
      · simp [leftTailSet] at hcut_mem
        exact hcut_mem.2.2
      · intro cut' hlt hprop
        have hcut'_mem : cut' ∈ leftTailSet := by
          refine Finset.mem_filter.mpr ?_
          exact ⟨Finset.mem_univ cut', hprop.1, hprop.2.1, hprop.2.2⟩
        have hle := hcut_min cut' hcut'_mem
        have : cut.val ≤ cut'.val := by simpa using hle
        omega
    have hright_tail_min :
        RightTailResidue →
        ∃ cut : Fin gc.configs.length,
          cut.val ≤ k_out.val ∧
          gc.moverAt cut = right (right (right t)) ∧
          (∀ k : Fin gc.configs.length,
            cut.val ≤ k.val →
            gc.moverAt k = left (left t) ∨
              gc.moverAt k = left t ∨
              gc.moverAt k = t ∨
              gc.moverAt k = right t ∨
              gc.moverAt k = right (right t) ∨
              gc.moverAt k = right (right (right t))) ∧
          ∀ cut' : Fin gc.configs.length,
            cut'.val < cut.val →
            ¬ (cut'.val ≤ k_out.val ∧
              gc.moverAt cut' = right (right (right t)) ∧
              (∀ k : Fin gc.configs.length,
                cut'.val ≤ k.val →
                gc.moverAt k = left (left t) ∨
                  gc.moverAt k = left t ∨
                  gc.moverAt k = t ∨
                  gc.moverAt k = right t ∨
                  gc.moverAt k = right (right t) ∨
                  gc.moverAt k = right (right (right t)))) := by
      intro h
      rcases h with ⟨cut0, hcut0_le, hcut0_right3, hcut0_tail⟩
      let rightTailSet : Finset (Fin gc.configs.length) :=
        (Finset.univ : Finset (Fin gc.configs.length)).filter
          (fun cut =>
            cut.val ≤ k_out.val ∧
            gc.moverAt cut = right (right (right t)) ∧
            (∀ k : Fin gc.configs.length,
              cut.val ≤ k.val →
              gc.moverAt k = left (left t) ∨
                gc.moverAt k = left t ∨
                gc.moverAt k = t ∨
                gc.moverAt k = right t ∨
                gc.moverAt k = right (right t) ∨
                gc.moverAt k = right (right (right t))))
      have hcut0_mem : cut0 ∈ rightTailSet := by
        refine Finset.mem_filter.mpr ?_
        exact ⟨Finset.mem_univ cut0, hcut0_le, hcut0_right3, hcut0_tail⟩
      obtain ⟨cut, hcut_mem, hcut_min⟩ :=
        Finset.exists_min_image rightTailSet Fin.val ⟨cut0, hcut0_mem⟩
      refine ⟨cut, ?_, ?_, ?_, ?_⟩
      · simp [rightTailSet] at hcut_mem
        exact hcut_mem.1
      · simp [rightTailSet] at hcut_mem
        exact hcut_mem.2.1
      · simp [rightTailSet] at hcut_mem
        exact hcut_mem.2.2
      · intro cut' hlt hprop
        have hcut'_mem : cut' ∈ rightTailSet := by
          refine Finset.mem_filter.mpr ?_
          exact ⟨Finset.mem_univ cut', hprop.1, hprop.2.1, hprop.2.2⟩
        have hle := hcut_min cut' hcut'_mem
        have : cut.val ≤ cut'.val := by simpa using hle
        omega
    have hleft_tail_prev_shape :
        LeftTailResidue →
        ∃ cut prev : Fin gc.configs.length,
          prev.val + 1 = cut.val ∧
          cut.val ≤ k_out.val ∧
          (gc.moverAt prev = left (left (left (left t))) ∨
            gc.moverAt prev = left (left t)) ∧
          gc.moverAt cut = left (left (left t)) ∧
          (∀ k : Fin gc.configs.length,
            cut.val ≤ k.val →
            gc.moverAt k = left (left (left t)) ∨
              gc.moverAt k = left (left t) ∨
              gc.moverAt k = left t ∨
              gc.moverAt k = t ∨
              gc.moverAt k = right t ∨
              gc.moverAt k = right (right t)) := by
      intro h
      rcases hleft_tail_min h with
        ⟨cut, hcut_le, hcut_left3, hcut_tail, hcut_min⟩
      rcases all_left_six_or_prefix_bad_left4_or_right3_strong gc t cut hcut_tail with hall | hprefix
      · exact False.elim (movers_in_left_six_contradicts_hno_safe gc _hn _hno_safe t hall)
      · rcases hprefix with ⟨j, hj_lt, hj_edge, hj_tail⟩
        have hj1_lt_len : j.val + 1 < gc.configs.length := by
          exact lt_of_le_of_lt (Nat.succ_le_of_lt hj_lt) cut.isLt
        let j1 : Fin gc.configs.length := ⟨j.val + 1, hj1_lt_len⟩
        have hsucc :=
          left_prefix_edge_successor_shape gc t (by omega) j hj1_lt_len hj_edge hj_tail
        rcases hsucc with hsame | hcross
        · have hj1_le_kout : j1.val ≤ k_out.val := by
            rw [show j1.val = j.val + 1 by rfl]
            omega
          have hj1_tail :
              ∀ k : Fin gc.configs.length,
                j1.val ≤ k.val →
                gc.moverAt k = left (left (left t)) ∨
                  gc.moverAt k = left (left t) ∨
                  gc.moverAt k = left t ∨
                  gc.moverAt k = t ∨
                  gc.moverAt k = right t ∨
                  gc.moverAt k = right (right t) := by
            intro k hk_ge
            have hj_lt_k : j.val < k.val := by
              rw [show j1.val = j.val + 1 by rfl] at hk_ge
              omega
            exact hj_tail k hj_lt_k
          have hnot_lt : ¬ j1.val < cut.val := by
            intro hj1_lt_cut
            exact (hcut_min j1 hj1_lt_cut) ⟨hj1_le_kout, hsame.2, hj1_tail⟩
          have hj1_le_cut : j1.val ≤ cut.val := by
            rw [show j1.val = j.val + 1 by rfl]
            omega
          have hj1_eq_cut : j1 = cut := by
            apply Fin.ext
            exact Nat.le_antisymm hj1_le_cut (Nat.le_of_not_gt hnot_lt)
          refine ⟨cut, j, ?_, hcut_le, ?_, hcut_left3, hcut_tail⟩
          · simpa [j1] using congrArg Fin.val hj1_eq_cut
          · left
            exact hsame.1
        · have hj1_ne_cut : j1 ≠ cut := by
            intro hEq
            apply right2_ne_left3 (by omega) t
            calc
              right (right t) = gc.moverAt j1 := hcross.2.symm
              _ = gc.moverAt cut := by rw [hEq]
              _ = left (left (left t)) := hcut_left3
          have hj1_lt_cut : j1.val < cut.val := by
            have hj1_le_cut : j1.val ≤ cut.val := by
              rw [show j1.val = j.val + 1 by rfl]
              omega
            have hneq : j1.val ≠ cut.val := by
              intro hval
              exact hj1_ne_cut (Fin.ext hval)
            omega
          rcases first_left3_after_right2_in_leftsix_tail gc t (by omega) j j1 cut
            (by
              rw [show j1.val = j.val + 1 by rfl]
              omega) hj1_lt_cut hcross.2 hcut_left3 hj_tail with
            ⟨a, prev, _hj1_lt_prev, hprev_succ, ha_le_cut, hprev_left2, ha_left3⟩
          have ha_eq_cut : a = cut := by
            by_contra hneq
            have ha_lt_cut : a.val < cut.val := by
              have hneqv : a.val ≠ cut.val := by
                intro hval
                exact hneq (Fin.ext hval)
              omega
            have hprop :
                a.val ≤ k_out.val ∧
                gc.moverAt a = left (left (left t)) ∧
                (∀ k : Fin gc.configs.length,
                  a.val ≤ k.val →
                  gc.moverAt k = left (left (left t)) ∨
                    gc.moverAt k = left (left t) ∨
                    gc.moverAt k = left t ∨
                    gc.moverAt k = t ∨
                    gc.moverAt k = right t ∨
                    gc.moverAt k = right (right t)) := by
              refine ⟨le_trans ha_le_cut hcut_le, ha_left3, ?_⟩
              intro k hk_ge
              have hj_lt_k : j.val < k.val := by
                have hj_lt_a : j.val < a.val := by
                  have hj1_lt_a : j1.val < a.val := by
                    rw [← hprev_succ]
                    omega
                  rw [show j1.val = j.val + 1 by rfl] at hj1_lt_a
                  omega
                omega
              exact hj_tail k hj_lt_k
            exact (hcut_min a ha_lt_cut) hprop
          refine ⟨cut, prev, ?_, hcut_le, ?_, hcut_left3, hcut_tail⟩
          · simpa [ha_eq_cut] using hprev_succ
          · right
            exact hprev_left2
    have hright_tail_prev_shape :
        RightTailResidue →
        ∃ cut prev : Fin gc.configs.length,
          prev.val + 1 = cut.val ∧
          cut.val ≤ k_out.val ∧
          (gc.moverAt prev = right (right t) ∨
            gc.moverAt prev = right (right (right (right t)))) ∧
          gc.moverAt cut = right (right (right t)) ∧
          (∀ k : Fin gc.configs.length,
            cut.val ≤ k.val →
            gc.moverAt k = left (left t) ∨
              gc.moverAt k = left t ∨
              gc.moverAt k = t ∨
              gc.moverAt k = right t ∨
              gc.moverAt k = right (right t) ∨
              gc.moverAt k = right (right (right t))) := by
      intro h
      rcases hright_tail_min h with
        ⟨cut, hcut_le, hcut_right3, hcut_tail, hcut_min⟩
      rcases all_right_six_or_prefix_bad_left3_or_right4_strong gc t cut hcut_tail with hall | hprefix
      · exact False.elim (movers_in_right_six_contradicts_hno_safe gc _hn _hno_safe t hall)
      · rcases hprefix with ⟨j, hj_lt, hj_edge, hj_tail⟩
        have hj1_lt_len : j.val + 1 < gc.configs.length := by
          exact lt_of_le_of_lt (Nat.succ_le_of_lt hj_lt) cut.isLt
        let j1 : Fin gc.configs.length := ⟨j.val + 1, hj1_lt_len⟩
        have hsucc :=
          right_prefix_edge_successor_shape gc t (by omega) j hj1_lt_len hj_edge hj_tail
        rcases hsucc with hcross | hsame
        · have hj1_ne_cut : j1 ≠ cut := by
            intro hEq
            apply left2_ne_right3 (by omega) t
            calc
              left (left t) = gc.moverAt j1 := hcross.2.symm
              _ = gc.moverAt cut := by rw [hEq]
              _ = right (right (right t)) := hcut_right3
          have hj1_lt_cut : j1.val < cut.val := by
            have hj1_le_cut : j1.val ≤ cut.val := by
              rw [show j1.val = j.val + 1 by rfl]
              omega
            have hneq : j1.val ≠ cut.val := by
              intro hval
              exact hj1_ne_cut (Fin.ext hval)
            omega
          rcases first_right3_after_left2_in_rightsix_tail gc t (by omega) j j1 cut
            (by
              rw [show j1.val = j.val + 1 by rfl]
              omega) hj1_lt_cut hcross.2 hcut_right3 hj_tail with
            ⟨a, prev, _hj1_lt_prev, hprev_succ, ha_le_cut, hprev_right2, ha_right3⟩
          have ha_eq_cut : a = cut := by
            by_contra hneq
            have ha_lt_cut : a.val < cut.val := by
              have hneqv : a.val ≠ cut.val := by
                intro hval
                exact hneq (Fin.ext hval)
              omega
            have hprop :
                a.val ≤ k_out.val ∧
                gc.moverAt a = right (right (right t)) ∧
                (∀ k : Fin gc.configs.length,
                  a.val ≤ k.val →
                  gc.moverAt k = left (left t) ∨
                    gc.moverAt k = left t ∨
                    gc.moverAt k = t ∨
                    gc.moverAt k = right t ∨
                    gc.moverAt k = right (right t) ∨
                    gc.moverAt k = right (right (right t))) := by
              refine ⟨le_trans ha_le_cut hcut_le, ha_right3, ?_⟩
              intro k hk_ge
              have hj_lt_k : j.val < k.val := by
                have hj_lt_a : j.val < a.val := by
                  have hj1_lt_a : j1.val < a.val := by
                    rw [← hprev_succ]
                    omega
                  rw [show j1.val = j.val + 1 by rfl] at hj1_lt_a
                  omega
                omega
              exact hj_tail k hj_lt_k
            exact (hcut_min a ha_lt_cut) hprop
          refine ⟨cut, prev, ?_, hcut_le, ?_, hcut_right3, hcut_tail⟩
          · simpa [ha_eq_cut] using hprev_succ
          · left
            exact hprev_right2
        · have hj1_le_kout : j1.val ≤ k_out.val := by
            rw [show j1.val = j.val + 1 by rfl]
            omega
          have hj1_tail :
              ∀ k : Fin gc.configs.length,
                j1.val ≤ k.val →
                gc.moverAt k = left (left t) ∨
                  gc.moverAt k = left t ∨
                  gc.moverAt k = t ∨
                  gc.moverAt k = right t ∨
                  gc.moverAt k = right (right t) ∨
                  gc.moverAt k = right (right (right t)) := by
            intro k hk_ge
            have hj_lt_k : j.val < k.val := by
              rw [show j1.val = j.val + 1 by rfl] at hk_ge
              omega
            exact hj_tail k hj_lt_k
          have hnot_lt : ¬ j1.val < cut.val := by
            intro hj1_lt_cut
            exact (hcut_min j1 hj1_lt_cut) ⟨hj1_le_kout, hsame.2, hj1_tail⟩
          have hj1_eq_cut : j1 = cut := by
            apply Fin.ext
            have hj1_le_cut : j1.val ≤ cut.val := by
              rw [show j1.val = j.val + 1 by rfl]
              omega
            exact Nat.le_antisymm hj1_le_cut (Nat.le_of_not_gt hnot_lt)
          refine ⟨cut, j, ?_, hcut_le, ?_, hcut_right3, hcut_tail⟩
          · simpa [j1] using congrArg Fin.val hj1_eq_cut
          · right
            exact hsame.1
    let LeftPrevFromLeft4Residue : Prop :=
      ∃ cut prev : Fin gc.configs.length,
        prev.val + 1 = cut.val ∧
        cut.val ≤ k_out.val ∧
        gc.moverAt prev = left (left (left (left t))) ∧
        gc.moverAt cut = left (left (left t)) ∧
        (∀ k : Fin gc.configs.length,
          cut.val ≤ k.val →
          gc.moverAt k = left (left (left t)) ∨
            gc.moverAt k = left (left t) ∨
            gc.moverAt k = left t ∨
            gc.moverAt k = t ∨
            gc.moverAt k = right t ∨
            gc.moverAt k = right (right t))
    let LeftPrevFromLeft2Residue : Prop :=
      ∃ cut prev : Fin gc.configs.length,
        prev.val + 1 = cut.val ∧
        cut.val ≤ k_out.val ∧
        gc.moverAt prev = left (left t) ∧
        gc.moverAt cut = left (left (left t)) ∧
        (∀ k : Fin gc.configs.length,
          cut.val ≤ k.val →
          gc.moverAt k = left (left (left t)) ∨
            gc.moverAt k = left (left t) ∨
            gc.moverAt k = left t ∨
            gc.moverAt k = t ∨
            gc.moverAt k = right t ∨
            gc.moverAt k = right (right t))
    let RightPrevFromLeft2Residue : Prop :=
      ∃ cut prev : Fin gc.configs.length,
        prev.val + 1 = cut.val ∧
        cut.val ≤ k_out.val ∧
        gc.moverAt prev = right (right t) ∧
        gc.moverAt cut = right (right (right t)) ∧
        (∀ k : Fin gc.configs.length,
          cut.val ≤ k.val →
          gc.moverAt k = left (left t) ∨
            gc.moverAt k = left t ∨
            gc.moverAt k = t ∨
            gc.moverAt k = right t ∨
            gc.moverAt k = right (right t) ∨
            gc.moverAt k = right (right (right t)))
    let RightPrevFromRight4Residue : Prop :=
      ∃ cut prev : Fin gc.configs.length,
        prev.val + 1 = cut.val ∧
        cut.val ≤ k_out.val ∧
        gc.moverAt prev = right (right (right (right t))) ∧
        gc.moverAt cut = right (right (right t)) ∧
        (∀ k : Fin gc.configs.length,
          cut.val ≤ k.val →
          gc.moverAt k = left (left t) ∨
            gc.moverAt k = left t ∨
            gc.moverAt k = t ∨
            gc.moverAt k = right t ∨
            gc.moverAt k = right (right t) ∨
            gc.moverAt k = right (right (right t)))
    have hresidue_prev_split :
        (k_out.val + 1 = gc.configs.length) ∨
        LeftPrevFromLeft4Residue ∨
        LeftPrevFromLeft2Residue ∨
        RightPrevFromLeft2Residue ∨
        RightPrevFromRight4Residue := by
      rcases hresidue_tail with hk_last | hleft | hright
      · exact Or.inl hk_last
      · rcases hleft_tail_prev_shape hleft with ⟨cut, prev, hsucc, hle, hprev, hcut, htail⟩
        rcases hprev with hprev | hprev
        · exact Or.inr (Or.inl ⟨cut, prev, hsucc, hle, hprev, hcut, htail⟩)
        · exact Or.inr (Or.inr (Or.inl ⟨cut, prev, hsucc, hle, hprev, hcut, htail⟩))
      · rcases hright_tail_prev_shape hright with ⟨cut, prev, hsucc, hle, hprev, hcut, htail⟩
        rcases hprev with hprev | hprev
        · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨cut, prev, hsucc, hle, hprev, hcut, htail⟩)))
        · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨cut, prev, hsucc, hle, hprev, hcut, htail⟩)))
    let LeftOneSidedResidue : Prop :=
        ∃ cut : Fin gc.configs.length,
          cut.val ≤ k_out.val ∧
          gc.moverAt cut = left (left (left t)) ∧
          (∀ k : Fin gc.configs.length,
            cut.val ≤ k.val →
            gc.moverAt k = left (left (left t)) ∨
              gc.moverAt k = left (left t) ∨
              gc.moverAt k = left t ∨
              gc.moverAt k = t ∨
              gc.moverAt k = right t ∨
              gc.moverAt k = right (right t)) ∧
          ((∃ phase0 : TernaryPhase gc t,
              phase0.a = cut ∧
              ∀ k : Fin gc.configs.length,
                phase0.a.val ≤ k.val → k.val < phase0.s.val →
                gc.moverAt k = left (left (left t)) ∨
                  gc.moverAt k = left (left t) ∨
                  gc.moverAt k = left t) ∨
           (∀ k : Fin gc.configs.length,
              cut.val ≤ k.val →
              gc.moverAt k = left (left (left t)) ∨
                gc.moverAt k = left (left t) ∨
                gc.moverAt k = left t))
    let RightOneSidedResidue : Prop :=
        ∃ cut : Fin gc.configs.length,
          cut.val ≤ k_out.val ∧
          gc.moverAt cut = right (right (right t)) ∧
          (∀ k : Fin gc.configs.length,
            cut.val ≤ k.val →
            gc.moverAt k = left (left t) ∨
              gc.moverAt k = left t ∨
              gc.moverAt k = t ∨
              gc.moverAt k = right t ∨
              gc.moverAt k = right (right t) ∨
              gc.moverAt k = right (right (right t))) ∧
          ((∃ phase0 : TernaryPhase gc t,
              phase0.a = cut ∧
              ∀ k : Fin gc.configs.length,
                phase0.a.val ≤ k.val → k.val < phase0.s.val →
                gc.moverAt k = right t ∨
                  gc.moverAt k = right (right t) ∨
                  gc.moverAt k = right (right (right t))) ∨
           (∀ k : Fin gc.configs.length,
              cut.val ≤ k.val →
              gc.moverAt k = right t ∨
                gc.moverAt k = right (right t) ∨
                gc.moverAt k = right (right (right t))))
    have left_tail_one_sided_branch
        (cut : Fin gc.configs.length)
        (hcut_left3 : gc.moverAt cut = left (left (left t)))
        (hcut_tail :
          ∀ k : Fin gc.configs.length,
            cut.val ≤ k.val →
            gc.moverAt k = left (left (left t)) ∨
              gc.moverAt k = left (left t) ∨
              gc.moverAt k = left t ∨
              gc.moverAt k = t ∨
              gc.moverAt k = right t ∨
              gc.moverAt k = right (right t)) :
        ((∃ phase0 : TernaryPhase gc t,
            phase0.a = cut ∧
            ∀ k : Fin gc.configs.length,
              phase0.a.val ≤ k.val → k.val < phase0.s.val →
              gc.moverAt k = left (left (left t)) ∨
                gc.moverAt k = left (left t) ∨
                gc.moverAt k = left t) ∨
         (∀ k : Fin gc.configs.length,
            cut.val ≤ k.val →
            gc.moverAt k = left (left (left t)) ∨
              gc.moverAt k = left (left t) ∨
              gc.moverAt k = left t)) := by
      by_cases hafter : ∃ s : Fin gc.configs.length, cut.val < s.val ∧ gc.moverAt s = t
      · have hcut_nonmover : gc.moverAt cut ≠ t := by
          intro hcut_t
          exact left3_ne_self (by omega) t (by
            calc
              left (left (left t)) = gc.moverAt cut := hcut_left3.symm
              _ = t := hcut_t)
        obtain ⟨phase0, hphase0a⟩ :=
          exists_ternaryPhase_starting_at gc t cut hcut_nonmover hafter
        have htail6 :
            ∀ k : Fin gc.configs.length,
              cut.val < k.val → k.val < phase0.s.val →
              gc.moverAt k = left (left (left t)) ∨
                gc.moverAt k = left (left t) ∨
                gc.moverAt k = left t ∨
                gc.moverAt k = right t ∨
                gc.moverAt k = right (right t) ∨
                gc.moverAt k = right (right (right t)) := by
          intro k hk_gt hk_lt
          rcases hcut_tail k (le_of_lt hk_gt) with hk | hk | hk | hk | hk | hk
          · exact Or.inl hk
          · exact Or.inr (Or.inl hk)
          · exact Or.inr (Or.inr (Or.inl hk))
          · exfalso
            exact phase0.ht_nofire k (by simpa [hphase0a] using le_of_lt hk_gt) hk_lt hk
          · exact Or.inr (Or.inr (Or.inr (Or.inl hk)))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hk))))
        exact Or.inl ⟨phase0, hphase0a, by
          intro k hk_ge hk_lt
          exact phase_tail_from_left3_stays_left6 gc t phase0 (by omega) cut
            (by simpa [hphase0a])
            (by simpa [hphase0a] using phase0.ha_lt_s)
            hcut_left3 htail6 k (by simpa [hphase0a] using hk_ge) hk_lt⟩
      · have htail_no_t : ∀ k : Fin gc.configs.length, cut.val ≤ k.val → gc.moverAt k ≠ t := by
          intro k hk_ge
          by_cases hk_eq : k = cut
          · subst k
            intro hcut_t
            exact left3_ne_self (by omega) t (by
              calc
                left (left (left t)) = gc.moverAt cut := by simpa using hcut_left3.symm
                _ = t := hcut_t)
          · have hk_gt : cut.val < k.val := by
              have hneq : k.val ≠ cut.val := by
                intro hval
                exact hk_eq (Fin.ext hval)
              omega
            exact fun hkt => hafter ⟨k, hk_gt, hkt⟩
        have htail6 :
            ∀ k : Fin gc.configs.length,
              cut.val < k.val →
              gc.moverAt k = left (left (left t)) ∨
                gc.moverAt k = left (left t) ∨
                gc.moverAt k = left t ∨
                gc.moverAt k = right t ∨
                gc.moverAt k = right (right t) ∨
                gc.moverAt k = right (right (right t)) := by
          intro k hk_gt
          rcases hcut_tail k (le_of_lt hk_gt) with hk | hk | hk | hk | hk | hk
          · exact Or.inl hk
          · exact Or.inr (Or.inl hk)
          · exact Or.inr (Or.inr (Or.inl hk))
          · exfalso
            exact htail_no_t k (le_of_lt hk_gt) hk
          · exact Or.inr (Or.inr (Or.inr (Or.inl hk)))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hk))))
        refine (last_outside_terminal_tail_one_sided6 gc t (by omega) cut
          (Or.inl hcut_left3) htail_no_t htail6).elim Or.inr ?_
        intro hright
        exfalso
        rcases hright cut (le_rfl : cut.val ≤ cut.val) with h | h | h
        · apply left3_not_local5 (by omega) t
          exact Or.inr (Or.inr (Or.inl (Eq.trans hcut_left3.symm h)))
        · apply left3_not_local5 (by omega) t
          exact Or.inr (Or.inr (Or.inr (Eq.trans hcut_left3.symm h)))
        · apply left3_ne_right3 (by omega) t
          exact Eq.trans hcut_left3.symm h
    have left_tail_to_one_sided
        (cut : Fin gc.configs.length)
        (hcut_le : cut.val ≤ k_out.val)
        (hcut_left3 : gc.moverAt cut = left (left (left t)))
        (hcut_tail :
          ∀ k : Fin gc.configs.length,
            cut.val ≤ k.val →
            gc.moverAt k = left (left (left t)) ∨
              gc.moverAt k = left (left t) ∨
              gc.moverAt k = left t ∨
              gc.moverAt k = t ∨
              gc.moverAt k = right t ∨
              gc.moverAt k = right (right t)) :
        LeftOneSidedResidue := by
      exact ⟨cut, hcut_le, hcut_left3, hcut_tail,
        left_tail_one_sided_branch cut hcut_left3 hcut_tail⟩
    have right_tail_one_sided_branch
        (cut : Fin gc.configs.length)
        (hcut_right3 : gc.moverAt cut = right (right (right t)))
        (hcut_tail :
          ∀ k : Fin gc.configs.length,
            cut.val ≤ k.val →
            gc.moverAt k = left (left t) ∨
              gc.moverAt k = left t ∨
              gc.moverAt k = t ∨
              gc.moverAt k = right t ∨
              gc.moverAt k = right (right t) ∨
              gc.moverAt k = right (right (right t))) :
        ((∃ phase0 : TernaryPhase gc t,
            phase0.a = cut ∧
            ∀ k : Fin gc.configs.length,
              phase0.a.val ≤ k.val → k.val < phase0.s.val →
              gc.moverAt k = right t ∨
                gc.moverAt k = right (right t) ∨
                gc.moverAt k = right (right (right t))) ∨
         (∀ k : Fin gc.configs.length,
            cut.val ≤ k.val →
            gc.moverAt k = right t ∨
              gc.moverAt k = right (right t) ∨
              gc.moverAt k = right (right (right t)))) := by
      by_cases hafter : ∃ s : Fin gc.configs.length, cut.val < s.val ∧ gc.moverAt s = t
      · have hcut_nonmover : gc.moverAt cut ≠ t := by
          intro hcut_t
          exact right3_ne_self (by omega) t (by
            calc
              right (right (right t)) = gc.moverAt cut := hcut_right3.symm
              _ = t := hcut_t)
        obtain ⟨phase0, hphase0a⟩ :=
          exists_ternaryPhase_starting_at gc t cut hcut_nonmover hafter
        have htail6 :
            ∀ k : Fin gc.configs.length,
              cut.val < k.val → k.val < phase0.s.val →
              gc.moverAt k = left (left (left t)) ∨
                gc.moverAt k = left (left t) ∨
                gc.moverAt k = left t ∨
                gc.moverAt k = right t ∨
                gc.moverAt k = right (right t) ∨
                gc.moverAt k = right (right (right t)) := by
          intro k hk_gt hk_lt
          rcases hcut_tail k (le_of_lt hk_gt) with hk | hk | hk | hk | hk | hk
          · exact Or.inr (Or.inl hk)
          · exact Or.inr (Or.inr (Or.inl hk))
          · exfalso
            exact phase0.ht_nofire k (by simpa [hphase0a] using le_of_lt hk_gt) hk_lt hk
          · exact Or.inr (Or.inr (Or.inr (Or.inl hk)))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hk))))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hk))))
        exact Or.inl ⟨phase0, hphase0a, by
          intro k hk_ge hk_lt
          exact phase_tail_from_right3_stays_right6 gc t phase0 (by omega) cut
            (by simpa [hphase0a])
            (by simpa [hphase0a] using phase0.ha_lt_s)
            hcut_right3 htail6 k (by simpa [hphase0a] using hk_ge) hk_lt⟩
      · have htail_no_t : ∀ k : Fin gc.configs.length, cut.val ≤ k.val → gc.moverAt k ≠ t := by
          intro k hk_ge
          by_cases hk_eq : k = cut
          · subst k
            intro hcut_t
            exact right3_ne_self (by omega) t (by
              calc
                right (right (right t)) = gc.moverAt cut := by simpa using hcut_right3.symm
                _ = t := hcut_t)
          · have hk_gt : cut.val < k.val := by
              have hneq : k.val ≠ cut.val := by
                intro hval
                exact hk_eq (Fin.ext hval)
              omega
            exact fun hkt => hafter ⟨k, hk_gt, hkt⟩
        have htail6 :
            ∀ k : Fin gc.configs.length,
              cut.val < k.val →
              gc.moverAt k = left (left (left t)) ∨
                gc.moverAt k = left (left t) ∨
                gc.moverAt k = left t ∨
                gc.moverAt k = right t ∨
                gc.moverAt k = right (right t) ∨
                gc.moverAt k = right (right (right t)) := by
          intro k hk_gt
          rcases hcut_tail k (le_of_lt hk_gt) with hk | hk | hk | hk | hk | hk
          · exact Or.inr (Or.inl hk)
          · exact Or.inr (Or.inr (Or.inl hk))
          · exfalso
            exact htail_no_t k (le_of_lt hk_gt) hk
          · exact Or.inr (Or.inr (Or.inr (Or.inl hk)))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hk))))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hk))))
        refine (last_outside_terminal_tail_one_sided6 gc t (by omega) cut
          (Or.inr hcut_right3) htail_no_t htail6).elim ?_ Or.inr
        intro hleft
        exfalso
        rcases hleft cut (le_rfl : cut.val ≤ cut.val) with h | h | h
        · apply right3_ne_left3 (by omega) t
          exact Eq.trans hcut_right3.symm h
        · apply right3_not_local5 (by omega) t
          exact Or.inl (Eq.trans hcut_right3.symm h)
        · apply right3_not_local5 (by omega) t
          exact Or.inr (Or.inl (Eq.trans hcut_right3.symm h))
    have right_tail_to_one_sided
        (cut : Fin gc.configs.length)
        (hcut_le : cut.val ≤ k_out.val)
        (hcut_right3 : gc.moverAt cut = right (right (right t)))
        (hcut_tail :
          ∀ k : Fin gc.configs.length,
            cut.val ≤ k.val →
            gc.moverAt k = left (left t) ∨
              gc.moverAt k = left t ∨
              gc.moverAt k = t ∨
              gc.moverAt k = right t ∨
              gc.moverAt k = right (right t) ∨
              gc.moverAt k = right (right (right t))) :
        RightOneSidedResidue := by
      exact ⟨cut, hcut_le, hcut_right3, hcut_tail,
        right_tail_one_sided_branch cut hcut_right3 hcut_tail⟩
    have hleft_prev_to_one_sided :
        LeftPrevFromLeft4Residue ∨ LeftPrevFromLeft2Residue → LeftOneSidedResidue := by
      intro h
      rcases h with h | h <;> rcases h with ⟨cut, _prev, _hsucc, hcut_le, _hprev, hcut_left3, hcut_tail⟩
      · exact left_tail_to_one_sided cut hcut_le hcut_left3 hcut_tail
      · exact left_tail_to_one_sided cut hcut_le hcut_left3 hcut_tail
    have hright_prev_to_one_sided :
        RightPrevFromLeft2Residue ∨ RightPrevFromRight4Residue → RightOneSidedResidue := by
      intro h
      rcases h with h | h <;> rcases h with ⟨cut, _prev, _hsucc, hcut_le, _hprev, hcut_right3, hcut_tail⟩
      · exact right_tail_to_one_sided cut hcut_le hcut_right3 hcut_tail
      · exact right_tail_to_one_sided cut hcut_le hcut_right3 hcut_tail
    have hresidue_one_sided :
        (k_out.val + 1 = gc.configs.length) ∨ LeftOneSidedResidue ∨ RightOneSidedResidue := by
      rcases hresidue_prev_split with hk_last | hLL4 | hLL2 | hRL2 | hRR4
      · exact Or.inl hk_last
      · exact Or.inr (Or.inl (hleft_prev_to_one_sided (Or.inl hLL4)))
      · exact Or.inr (Or.inl (hleft_prev_to_one_sided (Or.inr hLL2)))
      · exact Or.inr (Or.inr (hright_prev_to_one_sided (Or.inl hRL2)))
      · exact Or.inr (Or.inr (hright_prev_to_one_sided (Or.inr hRR4)))
    let LeftKoutOneSidedResidue : Prop :=
      gc.moverAt k_out = left (left (left t)) ∧
      (∀ k : Fin gc.configs.length,
        k_out.val ≤ k.val →
        gc.moverAt k = left (left (left t)) ∨
          gc.moverAt k = left (left t) ∨
          gc.moverAt k = left t ∨
          gc.moverAt k = t ∨
          gc.moverAt k = right t ∨
          gc.moverAt k = right (right t)) ∧
      ((∃ phase0 : TernaryPhase gc t,
          phase0.a = k_out ∧
          ∀ k : Fin gc.configs.length,
            phase0.a.val ≤ k.val → k.val < phase0.s.val →
            gc.moverAt k = left (left (left t)) ∨
              gc.moverAt k = left (left t) ∨
              gc.moverAt k = left t) ∨
       (∀ k : Fin gc.configs.length,
          k_out.val ≤ k.val →
          gc.moverAt k = left (left (left t)) ∨
            gc.moverAt k = left (left t) ∨
            gc.moverAt k = left t))
    let RightKoutOneSidedResidue : Prop :=
      gc.moverAt k_out = right (right (right t)) ∧
      (∀ k : Fin gc.configs.length,
        k_out.val ≤ k.val →
        gc.moverAt k = left (left t) ∨
          gc.moverAt k = left t ∨
          gc.moverAt k = t ∨
          gc.moverAt k = right t ∨
          gc.moverAt k = right (right t) ∨
          gc.moverAt k = right (right (right t))) ∧
      ((∃ phase0 : TernaryPhase gc t,
          phase0.a = k_out ∧
          ∀ k : Fin gc.configs.length,
            phase0.a.val ≤ k.val → k.val < phase0.s.val →
            gc.moverAt k = right t ∨
              gc.moverAt k = right (right t) ∨
              gc.moverAt k = right (right (right t))) ∨
       (∀ k : Fin gc.configs.length,
          k_out.val ≤ k.val →
          gc.moverAt k = right t ∨
            gc.moverAt k = right (right t) ∨
            gc.moverAt k = right (right (right t))))
    have hleft_one_sided_to_kout :
        LeftOneSidedResidue → LeftKoutOneSidedResidue := by
      intro h
      rcases h with ⟨cut, hcut_le, hcut_left3, hcut_tail, _hcut_one_sided⟩
      have hkout_left3 : gc.moverAt k_out = left (left (left t)) := by
        by_cases hEq : cut = k_out
        · simpa [hEq] using hcut_left3
        · have hlt : cut.val < k_out.val := by
            have hneqv : cut.val ≠ k_out.val := by
              intro hval
              exact hEq (Fin.ext hval)
            omega
          exact outside_of_left_six_tail_eq_left3 gc t cut k_out hlt hk_outside
            (fun k hk_gt => hcut_tail k (le_of_lt hk_gt))
      have hkout_tail :
          ∀ k : Fin gc.configs.length,
            k_out.val ≤ k.val →
            gc.moverAt k = left (left (left t)) ∨
              gc.moverAt k = left (left t) ∨
              gc.moverAt k = left t ∨
              gc.moverAt k = t ∨
              gc.moverAt k = right t ∨
              gc.moverAt k = right (right t) := by
        intro k hk_ge
        exact hcut_tail k (le_trans hcut_le hk_ge)
      exact ⟨hkout_left3, hkout_tail,
        left_tail_one_sided_branch k_out hkout_left3 hkout_tail⟩
    have hright_one_sided_to_kout :
        RightOneSidedResidue → RightKoutOneSidedResidue := by
      intro h
      rcases h with ⟨cut, hcut_le, hcut_right3, hcut_tail, _hcut_one_sided⟩
      have hkout_right3 : gc.moverAt k_out = right (right (right t)) := by
        by_cases hEq : cut = k_out
        · simpa [hEq] using hcut_right3
        · have hlt : cut.val < k_out.val := by
            have hneqv : cut.val ≠ k_out.val := by
              intro hval
              exact hEq (Fin.ext hval)
            omega
          exact outside_of_right_six_tail_eq_right3 gc t cut k_out hlt hk_outside
            (fun k hk_gt => hcut_tail k (le_of_lt hk_gt))
      have hkout_tail :
          ∀ k : Fin gc.configs.length,
            k_out.val ≤ k.val →
            gc.moverAt k = left (left t) ∨
              gc.moverAt k = left t ∨
              gc.moverAt k = t ∨
              gc.moverAt k = right t ∨
              gc.moverAt k = right (right t) ∨
              gc.moverAt k = right (right (right t)) := by
        intro k hk_ge
        exact hcut_tail k (le_trans hcut_le hk_ge)
      exact ⟨hkout_right3, hkout_tail,
        right_tail_one_sided_branch k_out hkout_right3 hkout_tail⟩
    have hresidue_kout_one_sided :
        (k_out.val + 1 = gc.configs.length) ∨ LeftKoutOneSidedResidue ∨ RightKoutOneSidedResidue := by
      rcases hresidue_one_sided with hk_last | hleft | hright
      · exact Or.inl hk_last
      · exact Or.inr (Or.inl (hleft_one_sided_to_kout hleft))
      · exact Or.inr (Or.inr (hright_one_sided_to_kout hright))
    let LeftKoutPureResidue : Prop :=
      gc.moverAt k_out = left (left (left t)) ∧
      ((∃ phase0 : TernaryPhase gc t,
          phase0.a = k_out ∧
          ∀ k : Fin gc.configs.length,
            k_out.val < k.val → k.val < phase0.s.val →
            gc.moverAt k = left (left t) ∨
              gc.moverAt k = left t) ∨
       (∀ k : Fin gc.configs.length,
          k_out.val < k.val →
          gc.moverAt k = left (left t) ∨
            gc.moverAt k = left t))
    let RightKoutPureResidue : Prop :=
      gc.moverAt k_out = right (right (right t)) ∧
      ((∃ phase0 : TernaryPhase gc t,
          phase0.a = k_out ∧
          ∀ k : Fin gc.configs.length,
            k_out.val < k.val → k.val < phase0.s.val →
            gc.moverAt k = right t ∨
              gc.moverAt k = right (right t)) ∨
       (∀ k : Fin gc.configs.length,
          k_out.val < k.val →
          gc.moverAt k = right t ∨
            gc.moverAt k = right (right t)))
    have hleft_kout_one_sided_pure :
        LeftKoutOneSidedResidue → LeftKoutPureResidue := by
      intro h
      rcases h with ⟨hkout_left3, hleft_tail, hbranch⟩
      refine ⟨hkout_left3, ?_⟩
      rcases hbranch with ⟨phase0, hphase0a, hleft_branch⟩ | hleft_term
      · left
        refine ⟨phase0, hphase0a, ?_⟩
        intro k hk_gt hk_lt
        rcases hleft_branch k (by simpa [hphase0a] using le_of_lt hk_gt) hk_lt with hk | hk | hk
        · exfalso
          rcases hk_out_last k hk_gt with hkll | hkl | hkt | hkr | hkrr
          · apply left3_not_local5 (by omega) t
            exact Or.inl (Eq.trans hk.symm hkll)
          · apply left3_not_local5 (by omega) t
            exact Or.inr (Or.inl (Eq.trans hk.symm hkl))
          · exact left3_ne_self (by omega) t (Eq.trans hk.symm hkt)
          · apply left3_not_local5 (by omega) t
            exact Or.inr (Or.inr (Or.inl (Eq.trans hk.symm hkr)))
          · apply left3_not_local5 (by omega) t
            exact Or.inr (Or.inr (Or.inr (Eq.trans hk.symm hkrr)))
        · exact Or.inl hk
        · exact Or.inr hk
      · right
        intro k hk_gt
        rcases hleft_term k (le_of_lt hk_gt) with hk | hk | hk
        · exfalso
          rcases hk_out_last k hk_gt with hkll | hkl | hkt | hkr | hkrr
          · apply left3_not_local5 (by omega) t
            exact Or.inl (Eq.trans hk.symm hkll)
          · apply left3_not_local5 (by omega) t
            exact Or.inr (Or.inl (Eq.trans hk.symm hkl))
          · exact left3_ne_self (by omega) t (Eq.trans hk.symm hkt)
          · apply left3_not_local5 (by omega) t
            exact Or.inr (Or.inr (Or.inl (Eq.trans hk.symm hkr)))
          · apply left3_not_local5 (by omega) t
            exact Or.inr (Or.inr (Or.inr (Eq.trans hk.symm hkrr)))
        · exact Or.inl hk
        · exact Or.inr hk
    have hright_kout_one_sided_pure :
        RightKoutOneSidedResidue → RightKoutPureResidue := by
      intro h
      rcases h with ⟨hkout_right3, hright_tail, hbranch⟩
      refine ⟨hkout_right3, ?_⟩
      rcases hbranch with ⟨phase0, hphase0a, hright_branch⟩ | hright_term
      · left
        refine ⟨phase0, hphase0a, ?_⟩
        intro k hk_gt hk_lt
        rcases hright_branch k (by simpa [hphase0a] using le_of_lt hk_gt) hk_lt with hk | hk | hk
        · exact Or.inl hk
        · exact Or.inr hk
        · exfalso
          rcases hk_out_last k hk_gt with hkll | hkl | hkt | hkr | hkrr
          · apply right3_not_local5 (by omega) t
            exact Or.inl (Eq.trans hk.symm hkll)
          · apply right3_not_local5 (by omega) t
            exact Or.inr (Or.inl (Eq.trans hk.symm hkl))
          · exact right3_ne_self (by omega) t (Eq.trans hk.symm hkt)
          · apply right3_not_local5 (by omega) t
            exact Or.inr (Or.inr (Or.inl (Eq.trans hk.symm hkr)))
          · apply right3_not_local5 (by omega) t
            exact Or.inr (Or.inr (Or.inr (Eq.trans hk.symm hkrr)))
      · right
        intro k hk_gt
        rcases hright_term k (le_of_lt hk_gt) with hk | hk | hk
        · exact Or.inl hk
        · exact Or.inr hk
        · exfalso
          rcases hk_out_last k hk_gt with hkll | hkl | hkt | hkr | hkrr
          · apply right3_not_local5 (by omega) t
            exact Or.inl (Eq.trans hk.symm hkll)
          · apply right3_not_local5 (by omega) t
            exact Or.inr (Or.inl (Eq.trans hk.symm hkl))
          · exact right3_ne_self (by omega) t (Eq.trans hk.symm hkt)
          · apply right3_not_local5 (by omega) t
            exact Or.inr (Or.inr (Or.inl (Eq.trans hk.symm hkr)))
          · apply right3_not_local5 (by omega) t
            exact Or.inr (Or.inr (Or.inr (Eq.trans hk.symm hkrr)))
    have hresidue_kout_pure :
        (k_out.val + 1 = gc.configs.length) ∨ LeftKoutPureResidue ∨ RightKoutPureResidue := by
      rcases hresidue_kout_one_sided with hk_last | hleft | hright
      · exact Or.inl hk_last
      · exact Or.inr (Or.inl (hleft_kout_one_sided_pure hleft))
      · exact Or.inr (Or.inr (hright_kout_one_sided_pure hright))
    let LeftKoutStartedResidue : Prop :=
      gc.moverAt k_out = left (left (left t)) ∧
      ((∃ phase0 : TernaryPhase gc t,
          phase0.a = k_out ∧
          k_out.val + 2 < phase0.s.val ∧
          (∀ k : Fin gc.configs.length,
            k_out.val < k.val → k.val < phase0.s.val →
            gc.moverAt k = left (left t) ∨
              gc.moverAt k = left t) ∧
          ∃ k1 : Fin gc.configs.length,
            k1.val = k_out.val + 1 ∧
            gc.moverAt k1 = left (left t)) ∨
       (∀ k : Fin gc.configs.length,
          k_out.val < k.val →
          gc.moverAt k = left (left t) ∨
            gc.moverAt k = left t))
    let RightKoutStartedResidue : Prop :=
      gc.moverAt k_out = right (right (right t)) ∧
      ((∃ phase0 : TernaryPhase gc t,
          phase0.a = k_out ∧
          k_out.val + 2 < phase0.s.val ∧
          (∀ k : Fin gc.configs.length,
            k_out.val < k.val → k.val < phase0.s.val →
            gc.moverAt k = right t ∨
              gc.moverAt k = right (right t)) ∧
          ∃ k1 : Fin gc.configs.length,
            k1.val = k_out.val + 1 ∧
            gc.moverAt k1 = right (right t)) ∨
       (∀ k : Fin gc.configs.length,
          k_out.val < k.val →
          gc.moverAt k = right t ∨
            gc.moverAt k = right (right t)))
    have hleft_started_next2
        (hk1_lt_len : k_out.val + 1 < gc.configs.length) :
        LeftKoutStartedResidue →
        gc.moverAt ⟨k_out.val + 1, hk1_lt_len⟩ = left (left t) := by
      intro h
      rcases h with ⟨hkout_left3, hbranch⟩
      let k1 : Fin gc.configs.length := ⟨k_out.val + 1, hk1_lt_len⟩
      rcases hbranch with ⟨phase0, hphase0a, _hlong, _hphase_branch, k1', hk1'_eq, hk1'_left2⟩ | hleft_term
      · have hk1_eq : k1 = k1' := by
          apply Fin.ext
          simp [k1, hk1'_eq]
        cases hk1_eq
        simpa using hk1'_left2
      · have hk1_gt : k_out.val < k1.val := by
          dsimp [k1]
          omega
        have hk1_in : gc.moverAt k1 = left (left t) ∨ gc.moverAt k1 = left t := by
          exact hleft_term k1 hk1_gt
        have hk1_eq_next : nextIndex gc.configs k_out = k1 := by
          apply Fin.ext
          simp [nextIndex, k1]
          exact Nat.mod_eq_of_lt k1.isLt
        have hk1_not_left : gc.moverAt k1 ≠ left t := by
          intro hk1_left
          have hnext_local := gc.next_mover_is_local k_out
          rw [hk1_eq_next] at hnext_local
          rcases hnext_local with hleft | hself | hright
          · have hEq : left (left (left t)) = t := by
              calc left (left (left t)) = gc.moverAt k_out := hkout_left3.symm
              _ = t := by
                have htmp : t = gc.moverAt k_out := by
                  simpa [hk1_left, right_left_eq_self] using congrArg right hleft
                exact htmp.symm
            exact left3_ne_self (by omega) t hEq
          · have hEq : left (left (left t)) = left t := by
              calc left (left (left t)) = gc.moverAt k_out := hkout_left3.symm
              _ = left t := by simpa [hk1_left] using hself.symm
            exact (left3_not_local5 (by omega) t) (Or.inr (Or.inl hEq))
          · have hEq : left (left (left t)) = left (left t) := by
              calc left (left (left t)) = gc.moverAt k_out := hkout_left3.symm
              _ = left (left t) := by
                have htmp : left (left t) = gc.moverAt k_out := by
                  simpa [hk1_left, left_right_eq_self] using congrArg left hright
                exact htmp.symm
            exact (left3_not_local5 (by omega) t) (Or.inl hEq)
        rcases hk1_in with hk1_left2 | hk1_left
        · exact hk1_left2
        · exact False.elim (hk1_not_left hk1_left)
    have hright_started_next2
        (hk1_lt_len : k_out.val + 1 < gc.configs.length) :
        RightKoutStartedResidue →
        gc.moverAt ⟨k_out.val + 1, hk1_lt_len⟩ = right (right t) := by
      intro h
      rcases h with ⟨hkout_right3, hbranch⟩
      let k1 : Fin gc.configs.length := ⟨k_out.val + 1, hk1_lt_len⟩
      rcases hbranch with ⟨phase0, hphase0a, _hlong, _hphase_branch, k1', hk1'_eq, hk1'_right2⟩ | hright_term
      · have hk1_eq : k1 = k1' := by
          apply Fin.ext
          simp [k1, hk1'_eq]
        cases hk1_eq
        simpa using hk1'_right2
      · have hk1_gt : k_out.val < k1.val := by
          dsimp [k1]
          omega
        have hk1_in : gc.moverAt k1 = right t ∨ gc.moverAt k1 = right (right t) := by
          exact hright_term k1 hk1_gt
        have hk1_eq_next : nextIndex gc.configs k_out = k1 := by
          apply Fin.ext
          simp [nextIndex, k1]
          exact Nat.mod_eq_of_lt k1.isLt
        have hk1_not_right : gc.moverAt k1 ≠ right t := by
          intro hk1_right
          have hnext_local := gc.next_mover_is_local k_out
          rw [hk1_eq_next] at hnext_local
          rcases hnext_local with hleft | hself | hright
          · have hEq : right (right (right t)) = right (right t) := by
              calc right (right (right t)) = gc.moverAt k_out := hkout_right3.symm
              _ = right (right t) := by
                have htmp : right (right t) = gc.moverAt k_out := by
                  simpa [hk1_right, right_left_eq_self] using congrArg right hleft
                exact htmp.symm
            exact (right3_not_local5 (by omega) t) (Or.inr (Or.inr (Or.inr hEq)))
          · have hEq : right (right (right t)) = right t := by
              calc right (right (right t)) = gc.moverAt k_out := hkout_right3.symm
              _ = right t := by simpa [hk1_right] using hself.symm
            exact (right3_not_local5 (by omega) t) (Or.inr (Or.inr (Or.inl hEq)))
          · have hEq : right (right (right t)) = t := by
              calc right (right (right t)) = gc.moverAt k_out := hkout_right3.symm
              _ = t := by
                have htmp : t = gc.moverAt k_out := by
                  simpa [hk1_right, left_right_eq_self] using congrArg left hright
                exact htmp.symm
            exact right3_ne_self (by omega) t hEq
        rcases hk1_in with hk1_right | hk1_right2
        · exact False.elim (hk1_not_right hk1_right)
        · exact hk1_right2
    have hleft_kout_pure_started :
        LeftKoutPureResidue → LeftKoutStartedResidue := by
      intro h
      rcases h with ⟨hkout_left3, hbranch⟩
      refine ⟨hkout_left3, ?_⟩
      rcases hbranch with ⟨phase0, hphase0a, hleft_branch⟩ | hleft_term
      · left
        have hnorm0 : isNormalFormGap gc t phase0 := hall_normal phase0
        have hK0 : gc.intervalFireCount (right t) phase0.a.val phase0.s.val = 0 := by
          apply intervalFireCount_eq_zero_of_noFire gc (right t)
            (Nat.le_of_lt phase0.ha_lt_s) (Nat.le_of_lt phase0.s.isLt)
          intro k hk_ge hk_lt
          by_cases hk_eq : k = k_out
          · subst k
            intro hk
            have hEq : left (left (left t)) = right t := by
              calc left (left (left t)) = gc.moverAt k_out := hkout_left3.symm
              _ = right t := hk
            exact (left3_not_local5 (by omega) t) (Or.inr (Or.inr (Or.inl hEq)))
          · have hk_gt : k_out.val < k.val := by
              have hneqv : k.val ≠ k_out.val := by
                intro hval
                exact hk_eq (Fin.ext hval)
              omega
            rcases hleft_branch k (by simpa [hphase0a] using hk_gt) hk_lt with hk | hk
            · intro hkr
              exact left2_ne_right (by omega) t (Eq.trans hk.symm hkr)
            · intro hkr
              exact left_ne_right (by omega) t (Eq.trans hk.symm hkr)
        have hJ1 : gc.intervalFireCount (left t) phase0.a.val phase0.s.val = 1 := by
          exact (normalForm_gap_constraint gc t phase0 hnorm0).2.1 hK0
        have hlen1_ne : phase0.s.val ≠ k_out.val + 1 := by
          intro hlen1
          have hlen1' : phase0.s.val = phase0.a.val + 1 := by
            simpa [hphase0a] using hlen1
          rcases normal_len1_phase_starts_at_neighbor gc t phase0 hnorm0 hlen1' with hL | hR
          · have hEq : left (left (left t)) = left t := by
              calc left (left (left t)) = gc.moverAt k_out := hkout_left3.symm
              _ = left t := by simpa [hphase0a] using hL
            exact (left3_not_local5 (by omega) t) (Or.inr (Or.inl hEq))
          · have hEq : left (left (left t)) = right t := by
              calc left (left (left t)) = gc.moverAt k_out := hkout_left3.symm
              _ = right t := by simpa [hphase0a] using hR
            exact (left3_not_local5 (by omega) t) (Or.inr (Or.inr (Or.inl hEq)))
        have hlen2_ne : phase0.s.val ≠ k_out.val + 2 := by
          intro hlen2
          have hlen2' : phase0.s.val = phase0.a.val + 2 := by
            simpa [hphase0a] using hlen2
          rcases one_sided_left_len2_start_ll_or_ec gc t phase0 hnorm0 hJ1 hK0 hlen2' with hec | hll
          · exact False.elim (entryConflict_impossible gc hec)
          · have hEq : left (left (left t)) = left (left t) := by
              calc left (left (left t)) = gc.moverAt k_out := hkout_left3.symm
              _ = left (left t) := by simpa [hphase0a] using hll
            exact (left3_not_local5 (by omega) t) (Or.inl hEq)
        have hlong : k_out.val + 2 < phase0.s.val := by
          have hkout_lt_s : k_out.val < phase0.s.val := by
            simpa [hphase0a] using phase0.ha_lt_s
          omega
        have hk1_lt_len : k_out.val + 1 < gc.configs.length := by
          have hs_lt_len := phase0.s.isLt
          omega
        let k1 : Fin gc.configs.length := ⟨k_out.val + 1, hk1_lt_len⟩
        have hk1_lt_phase : k1.val < phase0.s.val := by
          dsimp [k1]
          omega
        have hk1_gt : k_out.val < k1.val := by
          dsimp [k1]
          omega
        have hk1_in : gc.moverAt k1 = left (left t) ∨ gc.moverAt k1 = left t := by
          exact hleft_branch k1 (by simpa [k1] using hk1_gt) hk1_lt_phase
        have hk1_eq_next : nextIndex gc.configs k_out = k1 := by
          apply Fin.ext
          simp [nextIndex, k1]
          exact Nat.mod_eq_of_lt k1.isLt
        have hk1_not_left : gc.moverAt k1 ≠ left t := by
          intro hk1_left
          have hnext_local := gc.next_mover_is_local k_out
          rw [hk1_eq_next] at hnext_local
          rcases hnext_local with hleft | hself | hright
          · have hEq : left (left (left t)) = t := by
              calc left (left (left t)) = gc.moverAt k_out := hkout_left3.symm
              _ = t := by
                have htmp : t = gc.moverAt k_out := by
                  simpa [hk1_left, right_left_eq_self] using congrArg right hleft
                exact htmp.symm
            exact left3_ne_self (by omega) t hEq
          · have hEq : left (left (left t)) = left t := by
              calc left (left (left t)) = gc.moverAt k_out := hkout_left3.symm
              _ = left t := by simpa [hk1_left] using hself.symm
            exact (left3_not_local5 (by omega) t) (Or.inr (Or.inl hEq))
          · have hEq : left (left (left t)) = left (left t) := by
              calc left (left (left t)) = gc.moverAt k_out := hkout_left3.symm
              _ = left (left t) := by
                have htmp : left (left t) = gc.moverAt k_out := by
                  simpa [hk1_left, left_right_eq_self] using congrArg left hright
                exact htmp.symm
            exact (left3_not_local5 (by omega) t) (Or.inl hEq)
        rcases hk1_in with hk1_left2 | hk1_left
        · refine ⟨phase0, hphase0a, hlong, hleft_branch, ?_⟩
          exact ⟨k1, rfl, hk1_left2⟩
        · exact False.elim (hk1_not_left hk1_left)
      · right
        intro k hk_gt
        exact hleft_term k hk_gt
    have hright_kout_pure_started :
        RightKoutPureResidue → RightKoutStartedResidue := by
      intro h
      rcases h with ⟨hkout_right3, hbranch⟩
      refine ⟨hkout_right3, ?_⟩
      rcases hbranch with ⟨phase0, hphase0a, hright_branch⟩ | hright_term
      · left
        have hnorm0 : isNormalFormGap gc t phase0 := hall_normal phase0
        have hJ0 : gc.intervalFireCount (left t) phase0.a.val phase0.s.val = 0 := by
          apply intervalFireCount_eq_zero_of_noFire gc (left t)
            (Nat.le_of_lt phase0.ha_lt_s) (Nat.le_of_lt phase0.s.isLt)
          intro k hk_ge hk_lt
          by_cases hk_eq : k = k_out
          · subst k
            intro hk
            have hEq : right (right (right t)) = left t := by
              calc right (right (right t)) = gc.moverAt k_out := hkout_right3.symm
              _ = left t := hk
            exact (right3_not_local5 (by omega) t) (Or.inr (Or.inl hEq))
          · have hk_gt : k_out.val < k.val := by
              have hneqv : k.val ≠ k_out.val := by
                intro hval
                exact hk_eq (Fin.ext hval)
              omega
            rcases hright_branch k (by simpa [hphase0a] using hk_gt) hk_lt with hk | hk
            · intro hkl
              exact right_ne_left (by omega) t (Eq.trans hk.symm hkl)
            · intro hkl
              exact right2_ne_left (by omega) t (Eq.trans hk.symm hkl)
        have hK1 : gc.intervalFireCount (right t) phase0.a.val phase0.s.val = 1 := by
          exact (normalForm_gap_constraint gc t phase0 hnorm0).1 hJ0
        have hlen1_ne : phase0.s.val ≠ k_out.val + 1 := by
          intro hlen1
          have hlen1' : phase0.s.val = phase0.a.val + 1 := by
            simpa [hphase0a] using hlen1
          rcases normal_len1_phase_starts_at_neighbor gc t phase0 hnorm0 hlen1' with hL | hR
          · have hEq : right (right (right t)) = left t := by
              calc right (right (right t)) = gc.moverAt k_out := hkout_right3.symm
              _ = left t := by simpa [hphase0a] using hL
            exact (right3_not_local5 (by omega) t) (Or.inr (Or.inl hEq))
          · have hEq : right (right (right t)) = right t := by
              calc right (right (right t)) = gc.moverAt k_out := hkout_right3.symm
              _ = right t := by simpa [hphase0a] using hR
            exact (right3_not_local5 (by omega) t) (Or.inr (Or.inr (Or.inl hEq)))
        have hlen2_ne : phase0.s.val ≠ k_out.val + 2 := by
          intro hlen2
          have hlen2' : phase0.s.val = phase0.a.val + 2 := by
            simpa [hphase0a] using hlen2
          rcases one_sided_right_len2_start_rr_or_ec gc t phase0 hnorm0 hJ0 hK1 hlen2' with hec | hrr
          · exact False.elim (entryConflict_impossible gc hec)
          · have hEq : right (right (right t)) = right (right t) := by
              calc right (right (right t)) = gc.moverAt k_out := hkout_right3.symm
              _ = right (right t) := by simpa [hphase0a] using hrr
            exact (right3_not_local5 (by omega) t) (Or.inr (Or.inr (Or.inr hEq)))
        have hlong : k_out.val + 2 < phase0.s.val := by
          have hkout_lt_s : k_out.val < phase0.s.val := by
            simpa [hphase0a] using phase0.ha_lt_s
          omega
        have hk1_lt_len : k_out.val + 1 < gc.configs.length := by
          have hs_lt_len := phase0.s.isLt
          omega
        let k1 : Fin gc.configs.length := ⟨k_out.val + 1, hk1_lt_len⟩
        have hk1_lt_phase : k1.val < phase0.s.val := by
          dsimp [k1]
          omega
        have hk1_gt : k_out.val < k1.val := by
          dsimp [k1]
          omega
        have hk1_in : gc.moverAt k1 = right t ∨ gc.moverAt k1 = right (right t) := by
          exact hright_branch k1 (by simpa [k1] using hk1_gt) hk1_lt_phase
        have hk1_eq_next : nextIndex gc.configs k_out = k1 := by
          apply Fin.ext
          simp [nextIndex, k1]
          exact Nat.mod_eq_of_lt k1.isLt
        have hk1_not_right : gc.moverAt k1 ≠ right t := by
          intro hk1_right
          have hnext_local := gc.next_mover_is_local k_out
          rw [hk1_eq_next] at hnext_local
          rcases hnext_local with hleft | hself | hright
          · have hEq : right (right (right t)) = right (right t) := by
              calc right (right (right t)) = gc.moverAt k_out := hkout_right3.symm
              _ = right (right t) := by
                have htmp : right (right t) = gc.moverAt k_out := by
                  simpa [hk1_right, right_left_eq_self] using congrArg right hleft
                exact htmp.symm
            exact (right3_not_local5 (by omega) t) (Or.inr (Or.inr (Or.inr hEq)))
          · have hEq : right (right (right t)) = right t := by
              calc right (right (right t)) = gc.moverAt k_out := hkout_right3.symm
              _ = right t := by simpa [hk1_right] using hself.symm
            exact (right3_not_local5 (by omega) t) (Or.inr (Or.inr (Or.inl hEq)))
          · have hEq : right (right (right t)) = t := by
              calc right (right (right t)) = gc.moverAt k_out := hkout_right3.symm
              _ = t := by
                have htmp : t = gc.moverAt k_out := by
                  simpa [hk1_right, left_right_eq_self] using congrArg left hright
                exact htmp.symm
            exact right3_ne_self (by omega) t hEq
        rcases hk1_in with hk1_right | hk1_right2
        · exact False.elim (hk1_not_right hk1_right)
        · refine ⟨phase0, hphase0a, hlong, hright_branch, ?_⟩
          exact ⟨k1, rfl, hk1_right2⟩
      · right
        intro k hk_gt
        exact hright_term k hk_gt
    have hresidue_kout_started :
        (k_out.val + 1 = gc.configs.length) ∨ LeftKoutStartedResidue ∨ RightKoutStartedResidue := by
      rcases hresidue_kout_pure with hk_last | hleft | hright
      · exact Or.inl hk_last
      · exact Or.inr (Or.inl (hleft_kout_pure_started hleft))
      · exact Or.inr (Or.inr (hright_kout_pure_started hright))
    let LeftStartedFromLeft4Residue : Prop :=
        LeftPrevFromLeft4Residue ∧ LeftKoutStartedResidue
    let LeftStartedFromLeft2Residue : Prop :=
        LeftPrevFromLeft2Residue ∧ LeftKoutStartedResidue
    let RightStartedFromLeft2Residue : Prop :=
        RightPrevFromLeft2Residue ∧ RightKoutStartedResidue
    let RightStartedFromRight4Residue : Prop :=
        RightPrevFromRight4Residue ∧ RightKoutStartedResidue
    have hresidue_started_split :
          (k_out.val + 1 = gc.configs.length) ∨
          LeftStartedFromLeft4Residue ∨
          LeftStartedFromLeft2Residue ∨
          RightStartedFromLeft2Residue ∨
          RightStartedFromRight4Residue := by
        rcases hresidue_prev_split with hk_last | hLL4 | hLL2 | hRL2 | hRR4
        · exact Or.inl hk_last
        · rcases hresidue_kout_started with hk_last | hleft | hright
          · exact Or.inl hk_last
          · exact Or.inr (Or.inl ⟨hLL4, hleft⟩)
          · rcases hLL4 with ⟨cut, _prev, _hsucc, hcut_le, _hprev, _hcut_left3, hcut_tail⟩
            rcases hright with ⟨hkout_right3, _⟩
            exact False.elim ((right3_not_leftsix (by omega) t) (by
              rcases hcut_tail k_out hcut_le with hk | hk | hk | hk | hk | hk
              · exact Or.inl (by
                  calc right (right (right t)) = gc.moverAt k_out := hkout_right3.symm
                  _ = left (left (left t)) := hk)
              · exact Or.inr (Or.inl (by
                  calc right (right (right t)) = gc.moverAt k_out := hkout_right3.symm
                  _ = left (left t) := hk))
              · exact Or.inr (Or.inr (Or.inl (by
                  calc right (right (right t)) = gc.moverAt k_out := hkout_right3.symm
                  _ = left t := hk)))
              · exact Or.inr (Or.inr (Or.inr (Or.inl (by
                  calc right (right (right t)) = gc.moverAt k_out := hkout_right3.symm
                  _ = t := hk))))
              · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by
                  calc right (right (right t)) = gc.moverAt k_out := hkout_right3.symm
                  _ = right t := hk)))))
              · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by
                  calc right (right (right t)) = gc.moverAt k_out := hkout_right3.symm
                  _ = right (right t) := hk)))))))
        · rcases hresidue_kout_started with hk_last | hleft | hright
          · exact Or.inl hk_last
          · exact Or.inr (Or.inr (Or.inl ⟨hLL2, hleft⟩))
          · rcases hLL2 with ⟨cut, _prev, _hsucc, hcut_le, _hprev, _hcut_left3, hcut_tail⟩
            rcases hright with ⟨hkout_right3, _⟩
            exact False.elim ((right3_not_leftsix (by omega) t) (by
              rcases hcut_tail k_out hcut_le with hk | hk | hk | hk | hk | hk
              · exact Or.inl (by
                  calc right (right (right t)) = gc.moverAt k_out := hkout_right3.symm
                  _ = left (left (left t)) := hk)
              · exact Or.inr (Or.inl (by
                  calc right (right (right t)) = gc.moverAt k_out := hkout_right3.symm
                  _ = left (left t) := hk))
              · exact Or.inr (Or.inr (Or.inl (by
                  calc right (right (right t)) = gc.moverAt k_out := hkout_right3.symm
                  _ = left t := hk)))
              · exact Or.inr (Or.inr (Or.inr (Or.inl (by
                  calc right (right (right t)) = gc.moverAt k_out := hkout_right3.symm
                  _ = t := hk))))
              · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by
                  calc right (right (right t)) = gc.moverAt k_out := hkout_right3.symm
                  _ = right t := hk)))))
              · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by
                  calc right (right (right t)) = gc.moverAt k_out := hkout_right3.symm
                  _ = right (right t) := hk)))))))
        · rcases hresidue_kout_started with hk_last | hleft | hright
          · exact Or.inl hk_last
          · rcases hRL2 with ⟨cut, _prev, _hsucc, hcut_le, _hprev, _hcut_right3, hcut_tail⟩
            rcases hleft with ⟨hkout_left3, _⟩
            exact False.elim ((left3_not_rightsix (by omega) t) (by
              rcases hcut_tail k_out hcut_le with hk | hk | hk | hk | hk | hk
              · exact Or.inl (by
                  calc left (left (left t)) = gc.moverAt k_out := hkout_left3.symm
                  _ = left (left t) := hk)
              · exact Or.inr (Or.inl (by
                  calc left (left (left t)) = gc.moverAt k_out := hkout_left3.symm
                  _ = left t := hk))
              · exact Or.inr (Or.inr (Or.inl (by
                  calc left (left (left t)) = gc.moverAt k_out := hkout_left3.symm
                  _ = t := hk)))
              · exact Or.inr (Or.inr (Or.inr (Or.inl (by
                  calc left (left (left t)) = gc.moverAt k_out := hkout_left3.symm
                  _ = right t := hk))))
              · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by
                  calc left (left (left t)) = gc.moverAt k_out := hkout_left3.symm
                  _ = right (right t) := hk)))))
              · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by
                  calc left (left (left t)) = gc.moverAt k_out := hkout_left3.symm
                  _ = right (right (right t)) := hk)))))))
          · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hRL2, hright⟩)))
        · rcases hresidue_kout_started with hk_last | hleft | hright
          · exact Or.inl hk_last
          · rcases hRR4 with ⟨cut, _prev, _hsucc, hcut_le, _hprev, _hcut_right3, hcut_tail⟩
            rcases hleft with ⟨hkout_left3, _⟩
            exact False.elim ((left3_not_rightsix (by omega) t) (by
              rcases hcut_tail k_out hcut_le with hk | hk | hk | hk | hk | hk
              · exact Or.inl (by
                  calc left (left (left t)) = gc.moverAt k_out := hkout_left3.symm
                  _ = left (left t) := hk)
              · exact Or.inr (Or.inl (by
                  calc left (left (left t)) = gc.moverAt k_out := hkout_left3.symm
                  _ = left t := hk))
              · exact Or.inr (Or.inr (Or.inl (by
                  calc left (left (left t)) = gc.moverAt k_out := hkout_left3.symm
                  _ = t := hk)))
              · exact Or.inr (Or.inr (Or.inr (Or.inl (by
                  calc left (left (left t)) = gc.moverAt k_out := hkout_left3.symm
                  _ = right t := hk))))
              · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by
                  calc left (left (left t)) = gc.moverAt k_out := hkout_left3.symm
                  _ = right (right t) := hk)))))
              · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by
                  calc left (left (left t)) = gc.moverAt k_out := hkout_left3.symm
                  _ = right (right (right t)) := hk)))))))
          · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hRR4, hright⟩)))
    let LeftStartedPrefixResidue : Prop :=
        ∃ j : Fin gc.configs.length,
          j.val < k_out.val ∧
          (gc.moverAt j = left (left (left (left t))) ∨
            gc.moverAt j = right (right (right t))) ∧
          (∀ k : Fin gc.configs.length,
            j.val < k.val →
            gc.moverAt k = left (left (left t)) ∨
              gc.moverAt k = left (left t) ∨
              gc.moverAt k = left t ∨
              gc.moverAt k = t ∨
              gc.moverAt k = right t ∨
              gc.moverAt k = right (right t))
    let RightStartedPrefixResidue : Prop :=
        ∃ j : Fin gc.configs.length,
          j.val < k_out.val ∧
          (gc.moverAt j = left (left (left t)) ∨
            gc.moverAt j = right (right (right (right t)))) ∧
          (∀ k : Fin gc.configs.length,
            j.val < k.val →
            gc.moverAt k = left (left t) ∨
              gc.moverAt k = left t ∨
              gc.moverAt k = t ∨
              gc.moverAt k = right t ∨
              gc.moverAt k = right (right t) ∨
              gc.moverAt k = right (right (right t)))
    have hleftsix_of_phase
        (hkout_left3 : gc.moverAt k_out = left (left (left t)))
        (phase0 : TernaryPhase gc t)
        (hphase_branch :
          ∀ k : Fin gc.configs.length,
            k_out.val < k.val → k.val < phase0.s.val →
            gc.moverAt k = left (left t) ∨ gc.moverAt k = left t) :
        ∀ k : Fin gc.configs.length,
          k_out.val ≤ k.val →
          gc.moverAt k = left (left (left t)) ∨
            gc.moverAt k = left (left t) ∨
            gc.moverAt k = left t ∨
            gc.moverAt k = t ∨
            gc.moverAt k = right t ∨
            gc.moverAt k = right (right t) := by
      intro k hk_ge
      by_cases hk_eq : k = k_out
      · subst hk_eq
        exact Or.inl hkout_left3
      · have hk_gt : k_out.val < k.val := by
          have hneqv : k.val ≠ k_out.val := by
            intro hval
            exact hk_eq (Fin.ext hval)
          omega
        by_cases hk_lt_s : k.val < phase0.s.val
        · rcases hphase_branch k hk_gt hk_lt_s with hk | hk
          · exact Or.inr (Or.inl hk)
          · exact Or.inr (Or.inr (Or.inl hk))
        · rcases hk_out_last k hk_gt with hk | hk | hk | hk | hk
          · exact Or.inr (Or.inl hk)
          · exact Or.inr (Or.inr (Or.inl hk))
          · exact Or.inr (Or.inr (Or.inr (Or.inl hk)))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hk))))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hk))))
    have hleftsix_of_terminal
        (hkout_left3 : gc.moverAt k_out = left (left (left t)))
        (hterm :
          ∀ k : Fin gc.configs.length,
            k_out.val < k.val →
            gc.moverAt k = left (left t) ∨ gc.moverAt k = left t) :
        ∀ k : Fin gc.configs.length,
          k_out.val ≤ k.val →
          gc.moverAt k = left (left (left t)) ∨
            gc.moverAt k = left (left t) ∨
            gc.moverAt k = left t ∨
            gc.moverAt k = t ∨
            gc.moverAt k = right t ∨
            gc.moverAt k = right (right t) := by
      intro k hk_ge
      by_cases hk_eq : k = k_out
      · subst hk_eq
        exact Or.inl hkout_left3
      · have hk_gt : k_out.val < k.val := by
          have hneqv : k.val ≠ k_out.val := by
            intro hval
            exact hk_eq (Fin.ext hval)
          omega
        rcases hterm k hk_gt with hk | hk
        · exact Or.inr (Or.inl hk)
        · exact Or.inr (Or.inr (Or.inl hk))
    have hrightsix_of_phase
        (hkout_right3 : gc.moverAt k_out = right (right (right t)))
        (phase0 : TernaryPhase gc t)
        (hphase_branch :
          ∀ k : Fin gc.configs.length,
            k_out.val < k.val → k.val < phase0.s.val →
            gc.moverAt k = right t ∨ gc.moverAt k = right (right t)) :
        ∀ k : Fin gc.configs.length,
          k_out.val ≤ k.val →
          gc.moverAt k = left (left t) ∨
            gc.moverAt k = left t ∨
            gc.moverAt k = t ∨
            gc.moverAt k = right t ∨
            gc.moverAt k = right (right t) ∨
            gc.moverAt k = right (right (right t)) := by
      intro k hk_ge
      by_cases hk_eq : k = k_out
      · subst hk_eq
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hkout_right3))))
      · have hk_gt : k_out.val < k.val := by
          have hneqv : k.val ≠ k_out.val := by
            intro hval
            exact hk_eq (Fin.ext hval)
          omega
        by_cases hk_lt_s : k.val < phase0.s.val
        · rcases hphase_branch k hk_gt hk_lt_s with hk | hk
          · exact Or.inr (Or.inr (Or.inr (Or.inl hk)))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hk))))
        · rcases hk_out_last k hk_gt with hk | hk | hk | hk | hk
          · exact Or.inl hk
          · exact Or.inr (Or.inl hk)
          · exact Or.inr (Or.inr (Or.inl hk))
          · exact Or.inr (Or.inr (Or.inr (Or.inl hk)))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hk))))
    have hrightsix_of_terminal
        (hkout_right3 : gc.moverAt k_out = right (right (right t)))
        (hterm :
          ∀ k : Fin gc.configs.length,
            k_out.val < k.val →
            gc.moverAt k = right t ∨ gc.moverAt k = right (right t)) :
        ∀ k : Fin gc.configs.length,
          k_out.val ≤ k.val →
          gc.moverAt k = left (left t) ∨
            gc.moverAt k = left t ∨
            gc.moverAt k = t ∨
            gc.moverAt k = right t ∨
            gc.moverAt k = right (right t) ∨
            gc.moverAt k = right (right (right t)) := by
      intro k hk_ge
      by_cases hk_eq : k = k_out
      · subst hk_eq
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hkout_right3))))
      · have hk_gt : k_out.val < k.val := by
          have hneqv : k.val ≠ k_out.val := by
            intro hval
            exact hk_eq (Fin.ext hval)
          omega
        rcases hterm k hk_gt with hk | hk
        · exact Or.inr (Or.inr (Or.inr (Or.inl hk)))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hk))))
    let LeftStartedFromLeft4EdgeResidue : Prop :=
        LeftPrevFromLeft4Residue ∧
        ∃ k1 : Fin gc.configs.length,
          k1.val = k_out.val + 1 ∧
          gc.moverAt k1 = left (left t)
    let LeftStartedFromLeft2EdgeResidue : Prop :=
        LeftPrevFromLeft2Residue ∧
        ∃ k1 : Fin gc.configs.length,
          k1.val = k_out.val + 1 ∧
          gc.moverAt k1 = left (left t)
    let RightStartedFromLeft2EdgeResidue : Prop :=
        RightPrevFromLeft2Residue ∧
        ∃ k1 : Fin gc.configs.length,
          k1.val = k_out.val + 1 ∧
          gc.moverAt k1 = right (right t)
    let RightStartedFromRight4EdgeResidue : Prop :=
        RightPrevFromRight4Residue ∧
        ∃ k1 : Fin gc.configs.length,
          k1.val = k_out.val + 1 ∧
          gc.moverAt k1 = right (right t)
    have hresidue_started_edge_split :
          (k_out.val + 1 = gc.configs.length) ∨
          LeftStartedFromLeft4EdgeResidue ∨
          LeftStartedFromLeft2EdgeResidue ∨
          RightStartedFromLeft2EdgeResidue ∨
          RightStartedFromRight4EdgeResidue := by
      by_cases hk_last : k_out.val + 1 = gc.configs.length
      · exact Or.inl hk_last
      · have hk1_lt_len : k_out.val + 1 < gc.configs.length := by omega
        let k1 : Fin gc.configs.length := ⟨k_out.val + 1, hk1_lt_len⟩
        rcases hresidue_started_split with hk_last' | hLL4 | hLL2 | hRL2 | hRR4
        · exact False.elim (hk_last hk_last')
        · exact Or.inr (Or.inl ⟨hLL4.1, k1, rfl, hleft_started_next2 hk1_lt_len hLL4.2⟩)
        · exact Or.inr (Or.inr (Or.inl ⟨hLL2.1, k1, rfl, hleft_started_next2 hk1_lt_len hLL2.2⟩))
        · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hRL2.1, k1, rfl, hright_started_next2 hk1_lt_len hRL2.2⟩)))
        · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hRR4.1, k1, rfl, hright_started_next2 hk1_lt_len hRR4.2⟩)))
    let LeftStartedFromLeft4PhaseEdgeResidue : Prop :=
        LeftPrevFromLeft4Residue ∧
        gc.moverAt k_out = left (left (left t)) ∧
        ∃ phase0 : TernaryPhase gc t,
          phase0.a = k_out ∧
          k_out.val + 2 < phase0.s.val ∧
          (∀ k : Fin gc.configs.length,
            k_out.val < k.val → k.val < phase0.s.val →
            gc.moverAt k = left (left t) ∨
              gc.moverAt k = left t) ∧
          ∃ k1 : Fin gc.configs.length,
            k1.val = k_out.val + 1 ∧
            gc.moverAt k1 = left (left t)
    let LeftStartedFromLeft4TerminalEdgeResidue : Prop :=
        LeftPrevFromLeft4Residue ∧
        gc.moverAt k_out = left (left (left t)) ∧
        ∃ k1 : Fin gc.configs.length,
          k1.val = k_out.val + 1 ∧
          gc.moverAt k1 = left (left t) ∧
        (∀ k : Fin gc.configs.length,
          k_out.val < k.val →
          gc.moverAt k = left (left t) ∨
            gc.moverAt k = left t)
    let LeftStartedFromLeft2PhaseEdgeResidue : Prop :=
        LeftPrevFromLeft2Residue ∧
        gc.moverAt k_out = left (left (left t)) ∧
        ∃ phase0 : TernaryPhase gc t,
          phase0.a = k_out ∧
          k_out.val + 2 < phase0.s.val ∧
          (∀ k : Fin gc.configs.length,
            k_out.val < k.val → k.val < phase0.s.val →
            gc.moverAt k = left (left t) ∨
              gc.moverAt k = left t) ∧
          ∃ k1 : Fin gc.configs.length,
            k1.val = k_out.val + 1 ∧
            gc.moverAt k1 = left (left t)
    let LeftStartedFromLeft2TerminalEdgeResidue : Prop :=
        LeftPrevFromLeft2Residue ∧
        gc.moverAt k_out = left (left (left t)) ∧
        ∃ k1 : Fin gc.configs.length,
          k1.val = k_out.val + 1 ∧
          gc.moverAt k1 = left (left t) ∧
        (∀ k : Fin gc.configs.length,
          k_out.val < k.val →
          gc.moverAt k = left (left t) ∨
            gc.moverAt k = left t)
    let RightStartedFromLeft2PhaseEdgeResidue : Prop :=
        RightPrevFromLeft2Residue ∧
        gc.moverAt k_out = right (right (right t)) ∧
        ∃ phase0 : TernaryPhase gc t,
          phase0.a = k_out ∧
          k_out.val + 2 < phase0.s.val ∧
          (∀ k : Fin gc.configs.length,
            k_out.val < k.val → k.val < phase0.s.val →
            gc.moverAt k = right t ∨
              gc.moverAt k = right (right t)) ∧
          ∃ k1 : Fin gc.configs.length,
            k1.val = k_out.val + 1 ∧
            gc.moverAt k1 = right (right t)
    let RightStartedFromLeft2TerminalEdgeResidue : Prop :=
        RightPrevFromLeft2Residue ∧
        gc.moverAt k_out = right (right (right t)) ∧
        ∃ k1 : Fin gc.configs.length,
          k1.val = k_out.val + 1 ∧
          gc.moverAt k1 = right (right t) ∧
        (∀ k : Fin gc.configs.length,
          k_out.val < k.val →
          gc.moverAt k = right t ∨
            gc.moverAt k = right (right t))
    let RightStartedFromRight4PhaseEdgeResidue : Prop :=
        RightPrevFromRight4Residue ∧
        gc.moverAt k_out = right (right (right t)) ∧
        ∃ phase0 : TernaryPhase gc t,
          phase0.a = k_out ∧
          k_out.val + 2 < phase0.s.val ∧
          (∀ k : Fin gc.configs.length,
            k_out.val < k.val → k.val < phase0.s.val →
            gc.moverAt k = right t ∨
              gc.moverAt k = right (right t)) ∧
          ∃ k1 : Fin gc.configs.length,
            k1.val = k_out.val + 1 ∧
            gc.moverAt k1 = right (right t)
    let RightStartedFromRight4TerminalEdgeResidue : Prop :=
        RightPrevFromRight4Residue ∧
        gc.moverAt k_out = right (right (right t)) ∧
        ∃ k1 : Fin gc.configs.length,
          k1.val = k_out.val + 1 ∧
          gc.moverAt k1 = right (right t) ∧
        (∀ k : Fin gc.configs.length,
          k_out.val < k.val →
          gc.moverAt k = right t ∨
            gc.moverAt k = right (right t))
    have hresidue_started_edge_phase_terminal_split :
          (k_out.val + 1 = gc.configs.length) ∨
          LeftStartedFromLeft4PhaseEdgeResidue ∨
          LeftStartedFromLeft4TerminalEdgeResidue ∨
          LeftStartedFromLeft2PhaseEdgeResidue ∨
          LeftStartedFromLeft2TerminalEdgeResidue ∨
          RightStartedFromLeft2PhaseEdgeResidue ∨
          RightStartedFromLeft2TerminalEdgeResidue ∨
          RightStartedFromRight4PhaseEdgeResidue ∨
          RightStartedFromRight4TerminalEdgeResidue := by
      by_cases hk_last : k_out.val + 1 = gc.configs.length
      · exact Or.inl hk_last
      · have hk1_lt_len : k_out.val + 1 < gc.configs.length := by omega
        let k1 : Fin gc.configs.length := ⟨k_out.val + 1, hk1_lt_len⟩
        rcases hresidue_started_split with hk_last' | hLL4 | hLL2 | hRL2 | hRR4
        · exact False.elim (hk_last hk_last')
        · rcases hLL4 with ⟨hprev, hstart⟩
          rcases hstart with ⟨hkout_left3, hbranch⟩
          rcases hbranch with hphase | hterm
          · rcases hphase with ⟨phase0, hphase0a, hlong, hphase_branch, _k1, _hk1, _hk1_left2⟩
            exact Or.inr (Or.inl
              ⟨hprev, hkout_left3, phase0, hphase0a, hlong,
                hphase_branch, k1, rfl,
                hleft_started_next2 hk1_lt_len
                  ⟨hkout_left3, Or.inl ⟨phase0, hphase0a, hlong, hphase_branch, ⟨_k1, _hk1, _hk1_left2⟩⟩⟩⟩)
          · exact Or.inr (Or.inr (Or.inl
              ⟨hprev, hkout_left3, k1, rfl,
                hleft_started_next2 hk1_lt_len ⟨hkout_left3, Or.inr hterm⟩,
                hterm⟩))
        · rcases hLL2 with ⟨hprev, hstart⟩
          rcases hstart with ⟨hkout_left3, hbranch⟩
          rcases hbranch with hphase | hterm
          · rcases hphase with ⟨phase0, hphase0a, hlong, hphase_branch, _k1, _hk1, _hk1_left2⟩
            exact Or.inr (Or.inr (Or.inr (Or.inl
              ⟨hprev, hkout_left3, phase0, hphase0a, hlong,
                hphase_branch, k1, rfl,
                hleft_started_next2 hk1_lt_len
                  ⟨hkout_left3, Or.inl ⟨phase0, hphase0a, hlong, hphase_branch, ⟨_k1, _hk1, _hk1_left2⟩⟩⟩⟩)))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
              ⟨hprev, hkout_left3, k1, rfl,
                hleft_started_next2 hk1_lt_len ⟨hkout_left3, Or.inr hterm⟩,
                hterm⟩))))
        · rcases hRL2 with ⟨hprev, hstart⟩
          rcases hstart with ⟨hkout_right3, hbranch⟩
          rcases hbranch with hphase | hterm
          · rcases hphase with ⟨phase0, hphase0a, hlong, hphase_branch, _k1, _hk1, _hk1_right2⟩
            exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
              ⟨hprev, hkout_right3, phase0, hphase0a, hlong,
                hphase_branch, k1, rfl,
                hright_started_next2 hk1_lt_len
                  ⟨hkout_right3, Or.inl ⟨phase0, hphase0a, hlong, hphase_branch, ⟨_k1, _hk1, _hk1_right2⟩⟩⟩⟩)))))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
              ⟨hprev, hkout_right3, k1, rfl,
                hright_started_next2 hk1_lt_len ⟨hkout_right3, Or.inr hterm⟩,
                hterm⟩))))))
        · rcases hRR4 with ⟨hprev, hstart⟩
          rcases hstart with ⟨hkout_right3, hbranch⟩
          rcases hbranch with hphase | hterm
          · rcases hphase with ⟨phase0, hphase0a, hlong, hphase_branch, _k1, _hk1, _hk1_right2⟩
            exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
              ⟨hprev, hkout_right3, phase0, hphase0a, hlong,
                hphase_branch, k1, rfl,
                hright_started_next2 hk1_lt_len
                  ⟨hkout_right3, Or.inl ⟨phase0, hphase0a, hlong, hphase_branch, ⟨_k1, _hk1, _hk1_right2⟩⟩⟩⟩)))))))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
              ⟨hprev, hkout_right3, k1, rfl,
                hright_started_next2 hk1_lt_len ⟨hkout_right3, Or.inr hterm⟩,
                hterm⟩)))))))
    have hresidue_started_prefix_split :
          (k_out.val + 1 = gc.configs.length) ∨
          LeftStartedPrefixResidue ∨
          RightStartedPrefixResidue := by
      rcases hresidue_started_edge_phase_terminal_split with
        hk_last | hLL4P | hLL4T | hLL2P | hLL2T | hRL2P | hRL2T | hRR4P | hRR4T
      · exact Or.inl hk_last
      · rcases hLL4P with ⟨_hprev, hkout_left3, phase0, _hphase0a, _hlong, hphase_branch, _k1, _hk1, _hk1_left2⟩
        have hleftsix := hleftsix_of_phase hkout_left3 phase0 hphase_branch
        rcases all_left_six_or_prefix_bad_left4_or_right3_strong gc t k_out hleftsix with hall | hprefix
        · exfalso
          exact movers_in_left_six_contradicts_hno_safe gc _hn _hno_safe t hall
        · exact Or.inr (Or.inl hprefix)
      · rcases hLL4T with ⟨_hprev, hkout_left3, _k1, _hk1, _hk1_left2, hterm⟩
        have hleftsix := hleftsix_of_terminal hkout_left3 hterm
        rcases all_left_six_or_prefix_bad_left4_or_right3_strong gc t k_out hleftsix with hall | hprefix
        · exfalso
          exact movers_in_left_six_contradicts_hno_safe gc _hn _hno_safe t hall
        · exact Or.inr (Or.inl hprefix)
      · rcases hLL2P with ⟨_hprev, hkout_left3, phase0, _hphase0a, _hlong, hphase_branch, _k1, _hk1, _hk1_left2⟩
        have hleftsix := hleftsix_of_phase hkout_left3 phase0 hphase_branch
        rcases all_left_six_or_prefix_bad_left4_or_right3_strong gc t k_out hleftsix with hall | hprefix
        · exfalso
          exact movers_in_left_six_contradicts_hno_safe gc _hn _hno_safe t hall
        · exact Or.inr (Or.inl hprefix)
      · rcases hLL2T with ⟨_hprev, hkout_left3, _k1, _hk1, _hk1_left2, hterm⟩
        have hleftsix := hleftsix_of_terminal hkout_left3 hterm
        rcases all_left_six_or_prefix_bad_left4_or_right3_strong gc t k_out hleftsix with hall | hprefix
        · exfalso
          exact movers_in_left_six_contradicts_hno_safe gc _hn _hno_safe t hall
        · exact Or.inr (Or.inl hprefix)
      · rcases hRL2P with ⟨_hprev, hkout_right3, phase0, _hphase0a, _hlong, hphase_branch, _k1, _hk1, _hk1_right2⟩
        have hrightsix := hrightsix_of_phase hkout_right3 phase0 hphase_branch
        rcases all_right_six_or_prefix_bad_left3_or_right4_strong gc t k_out hrightsix with hall | hprefix
        · exfalso
          exact movers_in_right_six_contradicts_hno_safe gc _hn _hno_safe t hall
        · exact Or.inr (Or.inr hprefix)
      · rcases hRL2T with ⟨_hprev, hkout_right3, _k1, _hk1, _hk1_right2, hterm⟩
        have hrightsix := hrightsix_of_terminal hkout_right3 hterm
        rcases all_right_six_or_prefix_bad_left3_or_right4_strong gc t k_out hrightsix with hall | hprefix
        · exfalso
          exact movers_in_right_six_contradicts_hno_safe gc _hn _hno_safe t hall
        · exact Or.inr (Or.inr hprefix)
      · rcases hRR4P with ⟨_hprev, hkout_right3, phase0, _hphase0a, _hlong, hphase_branch, _k1, _hk1, _hk1_right2⟩
        have hrightsix := hrightsix_of_phase hkout_right3 phase0 hphase_branch
        rcases all_right_six_or_prefix_bad_left3_or_right4_strong gc t k_out hrightsix with hall | hprefix
        · exfalso
          exact movers_in_right_six_contradicts_hno_safe gc _hn _hno_safe t hall
        · exact Or.inr (Or.inr hprefix)
      · rcases hRR4T with ⟨_hprev, hkout_right3, _k1, _hk1, _hk1_right2, hterm⟩
        have hrightsix := hrightsix_of_terminal hkout_right3 hterm
        rcases all_right_six_or_prefix_bad_left3_or_right4_strong gc t k_out hrightsix with hall | hprefix
        · exfalso
          exact movers_in_right_six_contradicts_hno_safe gc _hn _hno_safe t hall
        · exact Or.inr (Or.inr hprefix)
    let LeftStartedPrefixEdgeResidue : Prop :=
        gc.moverAt k_out = left (left (left t)) ∧
        ∃ k1 : Fin gc.configs.length,
          k1.val = k_out.val + 1 ∧
          gc.moverAt k1 = left (left t) ∧
          LeftStartedPrefixResidue
    let RightStartedPrefixEdgeResidue : Prop :=
        gc.moverAt k_out = right (right (right t)) ∧
        ∃ k1 : Fin gc.configs.length,
          k1.val = k_out.val + 1 ∧
          gc.moverAt k1 = right (right t) ∧
          RightStartedPrefixResidue
    have hresidue_started_prefix_edge_split :
          (k_out.val + 1 = gc.configs.length) ∨
          LeftStartedPrefixEdgeResidue ∨
          RightStartedPrefixEdgeResidue := by
      rcases hresidue_started_edge_phase_terminal_split with
        hk_last | hLL4P | hLL4T | hLL2P | hLL2T | hRL2P | hRL2T | hRR4P | hRR4T
      · exact Or.inl hk_last
      · rcases hLL4P with ⟨_hprev, hkout_left3, phase0, _hphase0a, _hlong, hphase_branch, k1, hk1, hk1_left2⟩
        have hleftsix := hleftsix_of_phase hkout_left3 phase0 hphase_branch
        rcases all_left_six_or_prefix_bad_left4_or_right3_strong gc t k_out hleftsix with hall | hprefix
        · exfalso
          exact movers_in_left_six_contradicts_hno_safe gc _hn _hno_safe t hall
        · exact Or.inr (Or.inl ⟨hkout_left3, k1, hk1, hk1_left2, hprefix⟩)
      · rcases hLL4T with ⟨_hprev, hkout_left3, k1, hk1, hk1_left2, hterm⟩
        have hleftsix := hleftsix_of_terminal hkout_left3 hterm
        rcases all_left_six_or_prefix_bad_left4_or_right3_strong gc t k_out hleftsix with hall | hprefix
        · exfalso
          exact movers_in_left_six_contradicts_hno_safe gc _hn _hno_safe t hall
        · exact Or.inr (Or.inl ⟨hkout_left3, k1, hk1, hk1_left2, hprefix⟩)
      · rcases hLL2P with ⟨_hprev, hkout_left3, phase0, _hphase0a, _hlong, hphase_branch, k1, hk1, hk1_left2⟩
        have hleftsix := hleftsix_of_phase hkout_left3 phase0 hphase_branch
        rcases all_left_six_or_prefix_bad_left4_or_right3_strong gc t k_out hleftsix with hall | hprefix
        · exfalso
          exact movers_in_left_six_contradicts_hno_safe gc _hn _hno_safe t hall
        · exact Or.inr (Or.inl ⟨hkout_left3, k1, hk1, hk1_left2, hprefix⟩)
      · rcases hLL2T with ⟨_hprev, hkout_left3, k1, hk1, hk1_left2, hterm⟩
        have hleftsix := hleftsix_of_terminal hkout_left3 hterm
        rcases all_left_six_or_prefix_bad_left4_or_right3_strong gc t k_out hleftsix with hall | hprefix
        · exfalso
          exact movers_in_left_six_contradicts_hno_safe gc _hn _hno_safe t hall
        · exact Or.inr (Or.inl ⟨hkout_left3, k1, hk1, hk1_left2, hprefix⟩)
      · rcases hRL2P with ⟨_hprev, hkout_right3, phase0, _hphase0a, _hlong, hphase_branch, k1, hk1, hk1_right2⟩
        have hrightsix := hrightsix_of_phase hkout_right3 phase0 hphase_branch
        rcases all_right_six_or_prefix_bad_left3_or_right4_strong gc t k_out hrightsix with hall | hprefix
        · exfalso
          exact movers_in_right_six_contradicts_hno_safe gc _hn _hno_safe t hall
        · exact Or.inr (Or.inr ⟨hkout_right3, k1, hk1, hk1_right2, hprefix⟩)
      · rcases hRL2T with ⟨_hprev, hkout_right3, k1, hk1, hk1_right2, hterm⟩
        have hrightsix := hrightsix_of_terminal hkout_right3 hterm
        rcases all_right_six_or_prefix_bad_left3_or_right4_strong gc t k_out hrightsix with hall | hprefix
        · exfalso
          exact movers_in_right_six_contradicts_hno_safe gc _hn _hno_safe t hall
        · exact Or.inr (Or.inr ⟨hkout_right3, k1, hk1, hk1_right2, hprefix⟩)
      · rcases hRR4P with ⟨_hprev, hkout_right3, phase0, _hphase0a, _hlong, hphase_branch, k1, hk1, hk1_right2⟩
        have hrightsix := hrightsix_of_phase hkout_right3 phase0 hphase_branch
        rcases all_right_six_or_prefix_bad_left3_or_right4_strong gc t k_out hrightsix with hall | hprefix
        · exfalso
          exact movers_in_right_six_contradicts_hno_safe gc _hn _hno_safe t hall
        · exact Or.inr (Or.inr ⟨hkout_right3, k1, hk1, hk1_right2, hprefix⟩)
      · rcases hRR4T with ⟨_hprev, hkout_right3, k1, hk1, hk1_right2, hterm⟩
        have hrightsix := hrightsix_of_terminal hkout_right3 hterm
        rcases all_right_six_or_prefix_bad_left3_or_right4_strong gc t k_out hrightsix with hall | hprefix
        · exfalso
          exact movers_in_right_six_contradicts_hno_safe gc _hn _hno_safe t hall
        · exact Or.inr (Or.inr ⟨hkout_right3, k1, hk1, hk1_right2, hprefix⟩)
    let LeftStartedFromLeft4PrefixEdgeResidue : Prop :=
        LeftPrevFromLeft4Residue ∧ LeftStartedPrefixEdgeResidue
    let LeftStartedFromLeft2PrefixEdgeResidue : Prop :=
        LeftPrevFromLeft2Residue ∧ LeftStartedPrefixEdgeResidue
    let RightStartedFromLeft2PrefixEdgeResidue : Prop :=
        RightPrevFromLeft2Residue ∧ RightStartedPrefixEdgeResidue
    let RightStartedFromRight4PrefixEdgeResidue : Prop :=
        RightPrevFromRight4Residue ∧ RightStartedPrefixEdgeResidue
    have hresidue_started_prefix_case_split :
          (k_out.val + 1 = gc.configs.length) ∨
          LeftStartedFromLeft4PrefixEdgeResidue ∨
          LeftStartedFromLeft2PrefixEdgeResidue ∨
          RightStartedFromLeft2PrefixEdgeResidue ∨
          RightStartedFromRight4PrefixEdgeResidue := by
      rcases hresidue_started_edge_phase_terminal_split with
        hk_last | hLL4P | hLL4T | hLL2P | hLL2T | hRL2P | hRL2T | hRR4P | hRR4T
      · exact Or.inl hk_last
      · rcases hLL4P with ⟨hprev, hkout_left3, phase0, _hphase0a, _hlong, hphase_branch, k1, hk1, hk1_left2⟩
        have hleftsix := hleftsix_of_phase hkout_left3 phase0 hphase_branch
        rcases all_left_six_or_prefix_bad_left4_or_right3_strong gc t k_out hleftsix with hall | hprefix
        · exfalso
          exact movers_in_left_six_contradicts_hno_safe gc _hn _hno_safe t hall
        · exact Or.inr (Or.inl ⟨hprev, ⟨hkout_left3, k1, hk1, hk1_left2, hprefix⟩⟩)
      · rcases hLL4T with ⟨hprev, hkout_left3, k1, hk1, hk1_left2, hterm⟩
        have hleftsix := hleftsix_of_terminal hkout_left3 hterm
        rcases all_left_six_or_prefix_bad_left4_or_right3_strong gc t k_out hleftsix with hall | hprefix
        · exfalso
          exact movers_in_left_six_contradicts_hno_safe gc _hn _hno_safe t hall
        · exact Or.inr (Or.inl ⟨hprev, ⟨hkout_left3, k1, hk1, hk1_left2, hprefix⟩⟩)
      · rcases hLL2P with ⟨hprev, hkout_left3, phase0, _hphase0a, _hlong, hphase_branch, k1, hk1, hk1_left2⟩
        have hleftsix := hleftsix_of_phase hkout_left3 phase0 hphase_branch
        rcases all_left_six_or_prefix_bad_left4_or_right3_strong gc t k_out hleftsix with hall | hprefix
        · exfalso
          exact movers_in_left_six_contradicts_hno_safe gc _hn _hno_safe t hall
        · exact Or.inr (Or.inr (Or.inl ⟨hprev, ⟨hkout_left3, k1, hk1, hk1_left2, hprefix⟩⟩))
      · rcases hLL2T with ⟨hprev, hkout_left3, k1, hk1, hk1_left2, hterm⟩
        have hleftsix := hleftsix_of_terminal hkout_left3 hterm
        rcases all_left_six_or_prefix_bad_left4_or_right3_strong gc t k_out hleftsix with hall | hprefix
        · exfalso
          exact movers_in_left_six_contradicts_hno_safe gc _hn _hno_safe t hall
        · exact Or.inr (Or.inr (Or.inl ⟨hprev, ⟨hkout_left3, k1, hk1, hk1_left2, hprefix⟩⟩))
      · rcases hRL2P with ⟨hprev, hkout_right3, phase0, _hphase0a, _hlong, hphase_branch, k1, hk1, hk1_right2⟩
        have hrightsix := hrightsix_of_phase hkout_right3 phase0 hphase_branch
        rcases all_right_six_or_prefix_bad_left3_or_right4_strong gc t k_out hrightsix with hall | hprefix
        · exfalso
          exact movers_in_right_six_contradicts_hno_safe gc _hn _hno_safe t hall
        · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hprev, ⟨hkout_right3, k1, hk1, hk1_right2, hprefix⟩⟩)))
      · rcases hRL2T with ⟨hprev, hkout_right3, k1, hk1, hk1_right2, hterm⟩
        have hrightsix := hrightsix_of_terminal hkout_right3 hterm
        rcases all_right_six_or_prefix_bad_left3_or_right4_strong gc t k_out hrightsix with hall | hprefix
        · exfalso
          exact movers_in_right_six_contradicts_hno_safe gc _hn _hno_safe t hall
        · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hprev, ⟨hkout_right3, k1, hk1, hk1_right2, hprefix⟩⟩)))
      · rcases hRR4P with ⟨hprev, hkout_right3, phase0, _hphase0a, _hlong, hphase_branch, k1, hk1, hk1_right2⟩
        have hrightsix := hrightsix_of_phase hkout_right3 phase0 hphase_branch
        rcases all_right_six_or_prefix_bad_left3_or_right4_strong gc t k_out hrightsix with hall | hprefix
        · exfalso
          exact movers_in_right_six_contradicts_hno_safe gc _hn _hno_safe t hall
        · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hprev, ⟨hkout_right3, k1, hk1, hk1_right2, hprefix⟩⟩)))
      · rcases hRR4T with ⟨hprev, hkout_right3, k1, hk1, hk1_right2, hterm⟩
        have hrightsix := hrightsix_of_terminal hkout_right3 hterm
        rcases all_right_six_or_prefix_bad_left3_or_right4_strong gc t k_out hrightsix with hall | hprefix
        · exfalso
          exact movers_in_right_six_contradicts_hno_safe gc _hn _hno_safe t hall
        · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hprev, ⟨hkout_right3, k1, hk1, hk1_right2, hprefix⟩⟩)))
    let LeftStartedPrefixSharpResidue : Prop :=
        gc.moverAt k_out = left (left (left t)) ∧
        ∃ k1 : Fin gc.configs.length,
          k1.val = k_out.val + 1 ∧
          gc.moverAt k1 = left (left t) ∧
          ((∃ j j1 : Fin gc.configs.length,
              j.val < k_out.val ∧
              j1.val = j.val + 1 ∧
              gc.moverAt j = left (left (left (left t))) ∧
              gc.moverAt j1 = left (left (left t)) ∧
              (∀ k : Fin gc.configs.length,
                j.val < k.val →
                gc.moverAt k = left (left (left t)) ∨
                  gc.moverAt k = left (left t) ∨
                  gc.moverAt k = left t ∨
                  gc.moverAt k = t ∨
                  gc.moverAt k = right t ∨
                  gc.moverAt k = right (right t))) ∨
           (∃ j j1 : Fin gc.configs.length,
              j.val < k_out.val ∧
              j1.val = j.val + 1 ∧
              gc.moverAt j = right (right (right t)) ∧
              gc.moverAt j1 = right (right t) ∧
              (∀ k : Fin gc.configs.length,
                j.val < k.val →
                gc.moverAt k = left (left (left t)) ∨
                  gc.moverAt k = left (left t) ∨
                  gc.moverAt k = left t ∨
                  gc.moverAt k = t ∨
                  gc.moverAt k = right t ∨
                  gc.moverAt k = right (right t))))
    let RightStartedPrefixSharpResidue : Prop :=
        gc.moverAt k_out = right (right (right t)) ∧
        ∃ k1 : Fin gc.configs.length,
          k1.val = k_out.val + 1 ∧
          gc.moverAt k1 = right (right t) ∧
          ((∃ j j1 : Fin gc.configs.length,
              j.val < k_out.val ∧
              j1.val = j.val + 1 ∧
              gc.moverAt j = left (left (left t)) ∧
              gc.moverAt j1 = left (left t) ∧
              (∀ k : Fin gc.configs.length,
                j.val < k.val →
                gc.moverAt k = left (left t) ∨
                  gc.moverAt k = left t ∨
                  gc.moverAt k = t ∨
                  gc.moverAt k = right t ∨
                  gc.moverAt k = right (right t) ∨
                  gc.moverAt k = right (right (right t)))) ∨
           (∃ j j1 : Fin gc.configs.length,
              j.val < k_out.val ∧
              j1.val = j.val + 1 ∧
              gc.moverAt j = right (right (right (right t))) ∧
              gc.moverAt j1 = right (right (right t)) ∧
              (∀ k : Fin gc.configs.length,
                j.val < k.val →
                gc.moverAt k = left (left t) ∨
                  gc.moverAt k = left t ∨
                  gc.moverAt k = t ∨
                  gc.moverAt k = right t ∨
                  gc.moverAt k = right (right t) ∨
                  gc.moverAt k = right (right (right t)))))
    have hleft_started_prefix_sharp :
        LeftStartedPrefixEdgeResidue → LeftStartedPrefixSharpResidue := by
      intro h
      rcases h with ⟨hkout_left3, k1, hk1, hk1_left2, hprefix⟩
      rcases hprefix with ⟨j, hj_lt, hj_edge, hj_tail⟩
      have hj1_lt_len : j.val + 1 < gc.configs.length := by
        have : j.val + 1 ≤ k_out.val := by omega
        exact lt_of_le_of_lt this k_out.isLt
      let j1 : Fin gc.configs.length := ⟨j.val + 1, hj1_lt_len⟩
      have hsucc := left_prefix_edge_successor_shape gc t (by omega) j hj1_lt_len hj_edge hj_tail
      refine ⟨hkout_left3, k1, hk1, hk1_left2, ?_⟩
      rcases hsucc with hsame | hcross
      · exact Or.inl ⟨j, j1, hj_lt, rfl, hsame.1, hsame.2, hj_tail⟩
      · exact Or.inr ⟨j, j1, hj_lt, rfl, hcross.1, hcross.2, hj_tail⟩
    have hright_started_prefix_sharp :
        RightStartedPrefixEdgeResidue → RightStartedPrefixSharpResidue := by
      intro h
      rcases h with ⟨hkout_right3, k1, hk1, hk1_right2, hprefix⟩
      rcases hprefix with ⟨j, hj_lt, hj_edge, hj_tail⟩
      have hj1_lt_len : j.val + 1 < gc.configs.length := by
        have : j.val + 1 ≤ k_out.val := by omega
        exact lt_of_le_of_lt this k_out.isLt
      let j1 : Fin gc.configs.length := ⟨j.val + 1, hj1_lt_len⟩
      have hsucc := right_prefix_edge_successor_shape gc t (by omega) j hj1_lt_len hj_edge hj_tail
      refine ⟨hkout_right3, k1, hk1, hk1_right2, ?_⟩
      rcases hsucc with hcross | hsame
      · exact Or.inl ⟨j, j1, hj_lt, rfl, hcross.1, hcross.2, hj_tail⟩
      · exact Or.inr ⟨j, j1, hj_lt, rfl, hsame.1, hsame.2, hj_tail⟩
    have hresidue_started_prefix_sharp_split :
          (k_out.val + 1 = gc.configs.length) ∨
          LeftStartedPrefixSharpResidue ∨
          RightStartedPrefixSharpResidue := by
      rcases hresidue_started_prefix_edge_split with hk_last | hleft | hright
      · exact Or.inl hk_last
      · exact Or.inr (Or.inl (hleft_started_prefix_sharp hleft))
      · exact Or.inr (Or.inr (hright_started_prefix_sharp hright))
    let LeftStartedFromLeft4PrefixSharpResidue : Prop :=
        LeftPrevFromLeft4Residue ∧ LeftStartedPrefixSharpResidue
    let LeftStartedFromLeft2PrefixSharpResidue : Prop :=
        LeftPrevFromLeft2Residue ∧ LeftStartedPrefixSharpResidue
    let RightStartedFromLeft2PrefixSharpResidue : Prop :=
        RightPrevFromLeft2Residue ∧ RightStartedPrefixSharpResidue
    let RightStartedFromRight4PrefixSharpResidue : Prop :=
        RightPrevFromRight4Residue ∧ RightStartedPrefixSharpResidue
    have hresidue_started_prefix_sharp_case_split :
          (k_out.val + 1 = gc.configs.length) ∨
          LeftStartedFromLeft4PrefixSharpResidue ∨
          LeftStartedFromLeft2PrefixSharpResidue ∨
          RightStartedFromLeft2PrefixSharpResidue ∨
          RightStartedFromRight4PrefixSharpResidue := by
      rcases hresidue_started_prefix_case_split with hk_last | hLL4 | hLL2 | hRL2 | hRR4
      · exact Or.inl hk_last
      · exact Or.inr (Or.inl ⟨hLL4.1, hleft_started_prefix_sharp hLL4.2⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨hLL2.1, hleft_started_prefix_sharp hLL2.2⟩))
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hRL2.1, hright_started_prefix_sharp hRL2.2⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hRR4.1, hright_started_prefix_sharp hRR4.2⟩)))
    let LeftStartedPrefixSameResidue : Prop :=
        gc.moverAt k_out = left (left (left t)) ∧
        ∃ k1 : Fin gc.configs.length,
          k1.val = k_out.val + 1 ∧
          gc.moverAt k1 = left (left t) ∧
          ∃ j j1 : Fin gc.configs.length,
            j.val < k_out.val ∧
            j1.val = j.val + 1 ∧
            gc.moverAt j = left (left (left (left t))) ∧
            gc.moverAt j1 = left (left (left t)) ∧
            (∀ k : Fin gc.configs.length,
              j.val < k.val →
              gc.moverAt k = left (left (left t)) ∨
                gc.moverAt k = left (left t) ∨
                gc.moverAt k = left t ∨
                gc.moverAt k = t ∨
                gc.moverAt k = right t ∨
                gc.moverAt k = right (right t))
    let LeftStartedPrefixCrossResidue : Prop :=
        gc.moverAt k_out = left (left (left t)) ∧
        ∃ k1 : Fin gc.configs.length,
          k1.val = k_out.val + 1 ∧
          gc.moverAt k1 = left (left t) ∧
          ∃ j j1 : Fin gc.configs.length,
            j.val < k_out.val ∧
            j1.val = j.val + 1 ∧
            gc.moverAt j = right (right (right t)) ∧
            gc.moverAt j1 = right (right t) ∧
            (∀ k : Fin gc.configs.length,
              j.val < k.val →
              gc.moverAt k = left (left (left t)) ∨
                gc.moverAt k = left (left t) ∨
                gc.moverAt k = left t ∨
                gc.moverAt k = t ∨
                gc.moverAt k = right t ∨
                gc.moverAt k = right (right t))
    let RightStartedPrefixCrossResidue : Prop :=
        gc.moverAt k_out = right (right (right t)) ∧
        ∃ k1 : Fin gc.configs.length,
          k1.val = k_out.val + 1 ∧
          gc.moverAt k1 = right (right t) ∧
          ∃ j j1 : Fin gc.configs.length,
            j.val < k_out.val ∧
            j1.val = j.val + 1 ∧
            gc.moverAt j = left (left (left t)) ∧
            gc.moverAt j1 = left (left t) ∧
            (∀ k : Fin gc.configs.length,
              j.val < k.val →
              gc.moverAt k = left (left t) ∨
                gc.moverAt k = left t ∨
                gc.moverAt k = t ∨
                gc.moverAt k = right t ∨
                gc.moverAt k = right (right t) ∨
                gc.moverAt k = right (right (right t)))
    let RightStartedPrefixSameResidue : Prop :=
        gc.moverAt k_out = right (right (right t)) ∧
        ∃ k1 : Fin gc.configs.length,
          k1.val = k_out.val + 1 ∧
          gc.moverAt k1 = right (right t) ∧
          ∃ j j1 : Fin gc.configs.length,
            j.val < k_out.val ∧
            j1.val = j.val + 1 ∧
            gc.moverAt j = right (right (right (right t))) ∧
            gc.moverAt j1 = right (right (right t)) ∧
            (∀ k : Fin gc.configs.length,
              j.val < k.val →
              gc.moverAt k = left (left t) ∨
                gc.moverAt k = left t ∨
                gc.moverAt k = t ∨
                gc.moverAt k = right t ∨
                gc.moverAt k = right (right t) ∨
                gc.moverAt k = right (right (right t)))
    have hleft_started_prefix_same_or_cross :
        LeftStartedPrefixSharpResidue →
          LeftStartedPrefixSameResidue ∨ LeftStartedPrefixCrossResidue := by
      intro h
      rcases h with ⟨hkout_left3, k1, hk1, hk1_left2, hprefix⟩
      rcases hprefix with hsame | hcross
      · rcases hsame with ⟨j, j1, hj_lt, hj1, hj_left4, hj1_left3, hj_tail⟩
        exact Or.inl ⟨hkout_left3, k1, hk1, hk1_left2, j, j1, hj_lt, hj1, hj_left4, hj1_left3, hj_tail⟩
      · rcases hcross with ⟨j, j1, hj_lt, hj1, hj_right3, hj1_right2, hj_tail⟩
        exact Or.inr ⟨hkout_left3, k1, hk1, hk1_left2, j, j1, hj_lt, hj1, hj_right3, hj1_right2, hj_tail⟩
    have hright_started_prefix_same_or_cross :
        RightStartedPrefixSharpResidue →
          RightStartedPrefixCrossResidue ∨ RightStartedPrefixSameResidue := by
      intro h
      rcases h with ⟨hkout_right3, k1, hk1, hk1_right2, hprefix⟩
      rcases hprefix with hcross | hsame
      · rcases hcross with ⟨j, j1, hj_lt, hj1, hj_left3, hj1_left2, hj_tail⟩
        exact Or.inl ⟨hkout_right3, k1, hk1, hk1_right2, j, j1, hj_lt, hj1, hj_left3, hj1_left2, hj_tail⟩
      · rcases hsame with ⟨j, j1, hj_lt, hj1, hj_right4, hj1_right3, hj_tail⟩
        exact Or.inr ⟨hkout_right3, k1, hk1, hk1_right2, j, j1, hj_lt, hj1, hj_right4, hj1_right3, hj_tail⟩
    let LeftStartedFromLeft4PrefixSameResidue : Prop :=
        LeftPrevFromLeft4Residue ∧ LeftStartedPrefixSameResidue
    let LeftStartedFromLeft4PrefixCrossResidue : Prop :=
        LeftPrevFromLeft4Residue ∧ LeftStartedPrefixCrossResidue
    let LeftStartedFromLeft2PrefixSameResidue : Prop :=
        LeftPrevFromLeft2Residue ∧ LeftStartedPrefixSameResidue
    let LeftStartedFromLeft2PrefixCrossResidue : Prop :=
        LeftPrevFromLeft2Residue ∧ LeftStartedPrefixCrossResidue
    let RightStartedFromLeft2PrefixCrossResidue : Prop :=
        RightPrevFromLeft2Residue ∧ RightStartedPrefixCrossResidue
    let RightStartedFromLeft2PrefixSameResidue : Prop :=
        RightPrevFromLeft2Residue ∧ RightStartedPrefixSameResidue
    let RightStartedFromRight4PrefixCrossResidue : Prop :=
        RightPrevFromRight4Residue ∧ RightStartedPrefixCrossResidue
    let RightStartedFromRight4PrefixSameResidue : Prop :=
        RightPrevFromRight4Residue ∧ RightStartedPrefixSameResidue
    have hresidue_started_prefix_exact_split :
          (k_out.val + 1 = gc.configs.length) ∨
          LeftStartedFromLeft4PrefixSameResidue ∨
          LeftStartedFromLeft4PrefixCrossResidue ∨
          LeftStartedFromLeft2PrefixSameResidue ∨
          LeftStartedFromLeft2PrefixCrossResidue ∨
          RightStartedFromLeft2PrefixCrossResidue ∨
          RightStartedFromLeft2PrefixSameResidue ∨
          RightStartedFromRight4PrefixCrossResidue ∨
          RightStartedFromRight4PrefixSameResidue := by
      rcases hresidue_started_prefix_sharp_case_split with hk_last | hLL4 | hLL2 | hRL2 | hRR4
      · exact Or.inl hk_last
      · rcases hleft_started_prefix_same_or_cross hLL4.2 with hsame | hcross
        · exact Or.inr <| Or.inl <| ⟨hLL4.1, hsame⟩
        · exact Or.inr <| Or.inr <| Or.inl <| ⟨hLL4.1, hcross⟩
      · rcases hleft_started_prefix_same_or_cross hLL2.2 with hsame | hcross
        · exact Or.inr <| Or.inr <| Or.inr <| Or.inl <| ⟨hLL2.1, hsame⟩
        · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl <| ⟨hLL2.1, hcross⟩
      · rcases hright_started_prefix_same_or_cross hRL2.2 with hcross | hsame
        · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl <| ⟨hRL2.1, hcross⟩
        · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl <| ⟨hRL2.1, hsame⟩
      · rcases hright_started_prefix_same_or_cross hRR4.2 with hcross | hsame
        · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl <| ⟨hRR4.1, hcross⟩
        · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| ⟨hRR4.1, hsame⟩
    have hleft_started_prefix_same_final :
        LeftStartedPrefixSameResidue → LeftFromLeft4Final := by
      intro h
      rcases h with ⟨hkout_left3, _k1, _hk1, _hk1_left2, j, j1, hj_lt, hj1, hj_left4, hj1_left3, hj_tail⟩
      exact ⟨hkout_left3, j, j1, hj_lt, hj1, hj_left4, hj1_left3, hj_tail⟩
    have hleft_started_prefix_cross_final :
        LeftStartedPrefixCrossResidue → LeftFromRight3Final := by
      intro h
      rcases h with ⟨hkout_left3, _k1, _hk1, _hk1_left2, j, j1, hj_lt, hj1, hj_right3, hj1_right2, hj_tail⟩
      exact ⟨hkout_left3, j, j1, hj_lt, hj1, hj_right3, hj1_right2, hj_tail⟩
    have hright_started_prefix_cross_final :
        RightStartedPrefixCrossResidue → RightFromLeft3Final := by
      intro h
      rcases h with ⟨hkout_right3, _k1, _hk1, _hk1_right2, j, j1, hj_lt, hj1, hj_left3, hj1_left2, hj_tail⟩
      exact ⟨hkout_right3, j, j1, hj_lt, hj1, hj_left3, hj1_left2, hj_tail⟩
    have hright_started_prefix_same_final :
        RightStartedPrefixSameResidue → RightFromRight4Final := by
      intro h
      rcases h with ⟨hkout_right3, _k1, _hk1, _hk1_right2, j, j1, hj_lt, hj1, hj_right4, hj1_right3, hj_tail⟩
      exact ⟨hkout_right3, j, j1, hj_lt, hj1, hj_right4, hj1_right3, hj_tail⟩
    have hresidue_started_prefix_tail :
          (k_out.val + 1 = gc.configs.length) ∨ LeftTailResidue ∨ RightTailResidue := by
      rcases hresidue_started_prefix_exact_split with
        hk_last | hLL4S | hLL4X | hLL2S | hLL2X | hRL2X | hRL2S | hRR4X | hRR4S
      · exact Or.inl hk_last
      · exact Or.inr (Or.inl (hleft_same_tail (hleft_started_prefix_same_final hLL4S.2)))
      · exact Or.inr (Or.inl (hleft_cross_tail (hleft_started_prefix_cross_final hLL4X.2)))
      · exact Or.inr (Or.inl (hleft_same_tail (hleft_started_prefix_same_final hLL2S.2)))
      · exact Or.inr (Or.inl (hleft_cross_tail (hleft_started_prefix_cross_final hLL2X.2)))
      · exact Or.inr (Or.inr (hright_cross_tail (hright_started_prefix_cross_final hRL2X.2)))
      · exact Or.inr (Or.inr (hright_same_tail (hright_started_prefix_same_final hRL2S.2)))
      · exact Or.inr (Or.inr (hright_cross_tail (hright_started_prefix_cross_final hRR4X.2)))
      · exact Or.inr (Or.inr (hright_same_tail (hright_started_prefix_same_final hRR4S.2)))
    have hresidue_started_prefix_prev_split :
          (k_out.val + 1 = gc.configs.length) ∨
          LeftPrevFromLeft4Residue ∨
          LeftPrevFromLeft2Residue ∨
          RightPrevFromLeft2Residue ∨
          RightPrevFromRight4Residue := by
      rcases hresidue_started_prefix_tail with hk_last | hleft | hright
      · exact Or.inl hk_last
      · rcases hleft_tail_prev_shape hleft with
          ⟨cut, prev, hsucc, hle, hprev, hcut, htail⟩
        rcases hprev with hprev | hprev
        · exact Or.inr (Or.inl ⟨cut, prev, hsucc, hle, hprev, hcut, htail⟩)
        · exact Or.inr (Or.inr (Or.inl ⟨cut, prev, hsucc, hle, hprev, hcut, htail⟩))
      · rcases hright_tail_prev_shape hright with
          ⟨cut, prev, hsucc, hle, hprev, hcut, htail⟩
        rcases hprev with hprev | hprev
        · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨cut, prev, hsucc, hle, hprev, hcut, htail⟩)))
        · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨cut, prev, hsucc, hle, hprev, hcut, htail⟩)))
    have hresidue_started_prefix_one_sided :
          (k_out.val + 1 = gc.configs.length) ∨ LeftOneSidedResidue ∨ RightOneSidedResidue := by
      rcases hresidue_started_prefix_prev_split with hk_last | hLL4 | hLL2 | hRL2 | hRR4
      · exact Or.inl hk_last
      · exact Or.inr (Or.inl (hleft_prev_to_one_sided (Or.inl hLL4)))
      · exact Or.inr (Or.inl (hleft_prev_to_one_sided (Or.inr hLL2)))
      · exact Or.inr (Or.inr (hright_prev_to_one_sided (Or.inl hRL2)))
      · exact Or.inr (Or.inr (hright_prev_to_one_sided (Or.inr hRR4)))
    have hresidue_started_prefix_kout_one_sided :
          (k_out.val + 1 = gc.configs.length) ∨ LeftKoutOneSidedResidue ∨ RightKoutOneSidedResidue := by
      rcases hresidue_started_prefix_one_sided with hk_last | hleft | hright
      · exact Or.inl hk_last
      · exact Or.inr (Or.inl (hleft_one_sided_to_kout hleft))
      · exact Or.inr (Or.inr (hright_one_sided_to_kout hright))
    have hresidue_started_prefix_kout_pure :
          (k_out.val + 1 = gc.configs.length) ∨ LeftKoutPureResidue ∨ RightKoutPureResidue := by
      rcases hresidue_started_prefix_kout_one_sided with hk_last | hleft | hright
      · exact Or.inl hk_last
      · exact Or.inr (Or.inl (hleft_kout_one_sided_pure hleft))
      · exact Or.inr (Or.inr (hright_kout_one_sided_pure hright))
    have hresidue_started_prefix_kout_started :
          (k_out.val + 1 = gc.configs.length) ∨ LeftKoutStartedResidue ∨ RightKoutStartedResidue := by
      rcases hresidue_started_prefix_kout_pure with hk_last | hleft | hright
      · exact Or.inl hk_last
      · exact Or.inr (Or.inl (hleft_kout_pure_started hleft))
      · exact Or.inr (Or.inr (hright_kout_pure_started hright))
    let LeftStartedPrefixExactResidue : Prop :=
        LeftStartedFromLeft4PrefixSameResidue ∨
        LeftStartedFromLeft4PrefixCrossResidue ∨
        LeftStartedFromLeft2PrefixSameResidue ∨
        LeftStartedFromLeft2PrefixCrossResidue
    let RightStartedPrefixExactResidue : Prop :=
        RightStartedFromLeft2PrefixCrossResidue ∨
        RightStartedFromLeft2PrefixSameResidue ∨
        RightStartedFromRight4PrefixCrossResidue ∨
        RightStartedFromRight4PrefixSameResidue
    let LeftTailRestartResidue : Prop :=
        LeftTailResidue ∧ LeftKoutStartedResidue
    let RightTailRestartResidue : Prop :=
        RightTailResidue ∧ RightKoutStartedResidue
    let LeftStartedFromLeft4PrefixRestartResidue : Prop :=
        LeftStartedFromLeft4PrefixEdgeResidue ∧ LeftKoutStartedResidue
    let LeftStartedFromLeft2PrefixRestartResidue : Prop :=
        LeftStartedFromLeft2PrefixEdgeResidue ∧ LeftKoutStartedResidue
    let RightStartedFromLeft2PrefixRestartResidue : Prop :=
        RightStartedFromLeft2PrefixEdgeResidue ∧ RightKoutStartedResidue
    let RightStartedFromRight4PrefixRestartResidue : Prop :=
        RightStartedFromRight4PrefixEdgeResidue ∧ RightKoutStartedResidue
    have hresidue_started_prefix_restart_split :
          (k_out.val + 1 = gc.configs.length) ∨
          LeftStartedFromLeft4PrefixRestartResidue ∨
          LeftStartedFromLeft2PrefixRestartResidue ∨
          RightStartedFromLeft2PrefixRestartResidue ∨
          RightStartedFromRight4PrefixRestartResidue := by
      rcases hresidue_started_prefix_case_split with hk_last | hLL4 | hLL2 | hRL2 | hRR4
      · exact Or.inl hk_last
      · rcases hresidue_started_prefix_kout_started with hk_last' | hleft | hright
        · exact Or.inl hk_last'
        · exact Or.inr (Or.inl ⟨hLL4, hleft⟩)
        · rcases hLL4 with ⟨_hprev, hkout_left3, _k1, _hk1, _hk1_left2, _hprefix⟩
          rcases hright with ⟨hkout_right3, _⟩
          exact False.elim (right3_ne_left3 (by omega) t (by
            calc
              right (right (right t)) = gc.moverAt k_out := hkout_right3.symm
              _ = left (left (left t)) := hkout_left3))
      · rcases hresidue_started_prefix_kout_started with hk_last' | hleft | hright
        · exact Or.inl hk_last'
        · exact Or.inr (Or.inr (Or.inl ⟨hLL2, hleft⟩))
        · rcases hLL2 with ⟨_hprev, hkout_left3, _k1, _hk1, _hk1_left2, _hprefix⟩
          rcases hright with ⟨hkout_right3, _⟩
          exact False.elim (right3_ne_left3 (by omega) t (by
            calc
              right (right (right t)) = gc.moverAt k_out := hkout_right3.symm
              _ = left (left (left t)) := hkout_left3))
      · rcases hresidue_started_prefix_kout_started with hk_last' | hleft | hright
        · exact Or.inl hk_last'
        · rcases hRL2 with ⟨_hprev, hkout_right3, _k1, _hk1, _hk1_right2, _hprefix⟩
          rcases hleft with ⟨hkout_left3, _⟩
          exact False.elim (left3_ne_right3 (by omega) t (by
            calc
              left (left (left t)) = gc.moverAt k_out := hkout_left3.symm
              _ = right (right (right t)) := hkout_right3))
        · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hRL2, hright⟩)))
      · rcases hresidue_started_prefix_kout_started with hk_last' | hleft | hright
        · exact Or.inl hk_last'
        · rcases hRR4 with ⟨_hprev, hkout_right3, _k1, _hk1, _hk1_right2, _hprefix⟩
          rcases hleft with ⟨hkout_left3, _⟩
          exact False.elim (left3_ne_right3 (by omega) t (by
            calc
              left (left (left t)) = gc.moverAt k_out := hkout_left3.symm
              _ = right (right (right t)) := hkout_right3))
        · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hRR4, hright⟩)))
    let LeftStartedFromLeft4PrefixRestartPhaseEdgeResidue : Prop :=
        LeftStartedFromLeft4PrefixEdgeResidue ∧ LeftStartedFromLeft4PhaseEdgeResidue
    let LeftStartedFromLeft4PrefixRestartTerminalEdgeResidue : Prop :=
        LeftStartedFromLeft4PrefixEdgeResidue ∧ LeftStartedFromLeft4TerminalEdgeResidue
    let LeftStartedFromLeft2PrefixRestartPhaseEdgeResidue : Prop :=
        LeftStartedFromLeft2PrefixEdgeResidue ∧ LeftStartedFromLeft2PhaseEdgeResidue
    let LeftStartedFromLeft2PrefixRestartTerminalEdgeResidue : Prop :=
        LeftStartedFromLeft2PrefixEdgeResidue ∧ LeftStartedFromLeft2TerminalEdgeResidue
    let RightStartedFromLeft2PrefixRestartPhaseEdgeResidue : Prop :=
        RightStartedFromLeft2PrefixEdgeResidue ∧ RightStartedFromLeft2PhaseEdgeResidue
    let RightStartedFromLeft2PrefixRestartTerminalEdgeResidue : Prop :=
        RightStartedFromLeft2PrefixEdgeResidue ∧ RightStartedFromLeft2TerminalEdgeResidue
    let RightStartedFromRight4PrefixRestartPhaseEdgeResidue : Prop :=
        RightStartedFromRight4PrefixEdgeResidue ∧ RightStartedFromRight4PhaseEdgeResidue
    let RightStartedFromRight4PrefixRestartTerminalEdgeResidue : Prop :=
        RightStartedFromRight4PrefixEdgeResidue ∧ RightStartedFromRight4TerminalEdgeResidue
    have hresidue_started_prefix_restart_edge_phase_terminal_split :
          (k_out.val + 1 = gc.configs.length) ∨
          LeftStartedFromLeft4PrefixRestartPhaseEdgeResidue ∨
          LeftStartedFromLeft4PrefixRestartTerminalEdgeResidue ∨
          LeftStartedFromLeft2PrefixRestartPhaseEdgeResidue ∨
          LeftStartedFromLeft2PrefixRestartTerminalEdgeResidue ∨
          RightStartedFromLeft2PrefixRestartPhaseEdgeResidue ∨
          RightStartedFromLeft2PrefixRestartTerminalEdgeResidue ∨
          RightStartedFromRight4PrefixRestartPhaseEdgeResidue ∨
          RightStartedFromRight4PrefixRestartTerminalEdgeResidue := by
      by_cases hk_last : k_out.val + 1 = gc.configs.length
      · exact Or.inl hk_last
      · have hk1_lt_len : k_out.val + 1 < gc.configs.length := by omega
        let k1 : Fin gc.configs.length := ⟨k_out.val + 1, hk1_lt_len⟩
        rcases hresidue_started_prefix_restart_split with hk_last' | hLL4 | hLL2 | hRL2 | hRR4
        · exact False.elim (hk_last hk_last')
        · rcases hLL4 with ⟨hprefix, hstart⟩
          rcases hstart with ⟨hkout_left3, hbranch⟩
          rcases hbranch with hphase | hterm
          · rcases hphase with ⟨phase0, hphase0a, hlong, hphase_branch, _k1, _hk1, _hk1_left2⟩
            exact Or.inr (Or.inl
              ⟨hprefix,
                ⟨hprefix.1, hkout_left3, phase0, hphase0a, hlong,
                  hphase_branch, k1, rfl,
                  hleft_started_next2 hk1_lt_len
                    ⟨hkout_left3, Or.inl ⟨phase0, hphase0a, hlong, hphase_branch, ⟨_k1, _hk1, _hk1_left2⟩⟩⟩⟩⟩)
          · exact Or.inr (Or.inr (Or.inl
              ⟨hprefix,
                ⟨hprefix.1, hkout_left3, k1, rfl,
                  hleft_started_next2 hk1_lt_len ⟨hkout_left3, Or.inr hterm⟩,
                  hterm⟩⟩))
        · rcases hLL2 with ⟨hprefix, hstart⟩
          rcases hstart with ⟨hkout_left3, hbranch⟩
          rcases hbranch with hphase | hterm
          · rcases hphase with ⟨phase0, hphase0a, hlong, hphase_branch, _k1, _hk1, _hk1_left2⟩
            exact Or.inr (Or.inr (Or.inr (Or.inl
              ⟨hprefix,
                ⟨hprefix.1, hkout_left3, phase0, hphase0a, hlong,
                  hphase_branch, k1, rfl,
                  hleft_started_next2 hk1_lt_len
                    ⟨hkout_left3, Or.inl ⟨phase0, hphase0a, hlong, hphase_branch, ⟨_k1, _hk1, _hk1_left2⟩⟩⟩⟩⟩)))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
              ⟨hprefix,
                ⟨hprefix.1, hkout_left3, k1, rfl,
                  hleft_started_next2 hk1_lt_len ⟨hkout_left3, Or.inr hterm⟩,
                  hterm⟩⟩))))
        · rcases hRL2 with ⟨hprefix, hstart⟩
          rcases hstart with ⟨hkout_right3, hbranch⟩
          rcases hbranch with hphase | hterm
          · rcases hphase with ⟨phase0, hphase0a, hlong, hphase_branch, _k1, _hk1, _hk1_right2⟩
            exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
              ⟨hprefix,
                ⟨hprefix.1, hkout_right3, phase0, hphase0a, hlong,
                  hphase_branch, k1, rfl,
                  hright_started_next2 hk1_lt_len
                    ⟨hkout_right3, Or.inl ⟨phase0, hphase0a, hlong, hphase_branch, ⟨_k1, _hk1, _hk1_right2⟩⟩⟩⟩⟩)))))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
              ⟨hprefix,
                ⟨hprefix.1, hkout_right3, k1, rfl,
                  hright_started_next2 hk1_lt_len ⟨hkout_right3, Or.inr hterm⟩,
                  hterm⟩⟩))))))
        · rcases hRR4 with ⟨hprefix, hstart⟩
          rcases hstart with ⟨hkout_right3, hbranch⟩
          rcases hbranch with hphase | hterm
          · rcases hphase with ⟨phase0, hphase0a, hlong, hphase_branch, _k1, _hk1, _hk1_right2⟩
            exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
              ⟨hprefix,
                ⟨hprefix.1, hkout_right3, phase0, hphase0a, hlong,
                  hphase_branch, k1, rfl,
                  hright_started_next2 hk1_lt_len
                    ⟨hkout_right3, Or.inl ⟨phase0, hphase0a, hlong, hphase_branch, ⟨_k1, _hk1, _hk1_right2⟩⟩⟩⟩⟩)))))))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
              ⟨hprefix,
                ⟨hprefix.1, hkout_right3, k1, rfl,
                  hright_started_next2 hk1_lt_len ⟨hkout_right3, Or.inr hterm⟩,
                  hterm⟩⟩)))))))
    let LeftStartedPrefixRestartPhaseCommonResidue : Prop :=
        LeftStartedPrefixEdgeResidue ∧
        ∃ phase0 : TernaryPhase gc t,
          phase0.a = k_out ∧
          k_out.val + 2 < phase0.s.val ∧
          (∀ k : Fin gc.configs.length,
            k_out.val < k.val → k.val < phase0.s.val →
            gc.moverAt k = left (left t) ∨
              gc.moverAt k = left t)
    let LeftStartedPrefixRestartTerminalTailResidue : Prop :=
        LeftStartedPrefixEdgeResidue ∧
        (∀ k : Fin gc.configs.length,
          k_out.val < k.val →
          gc.moverAt k = left (left t) ∨
            gc.moverAt k = left t)
    let RightStartedPrefixRestartPhaseCommonResidue : Prop :=
        RightStartedPrefixEdgeResidue ∧
        ∃ phase0 : TernaryPhase gc t,
          phase0.a = k_out ∧
          k_out.val + 2 < phase0.s.val ∧
          (∀ k : Fin gc.configs.length,
            k_out.val < k.val → k.val < phase0.s.val →
            gc.moverAt k = right t ∨
              gc.moverAt k = right (right t))
    let RightStartedPrefixRestartTerminalTailResidue : Prop :=
        RightStartedPrefixEdgeResidue ∧
        (∀ k : Fin gc.configs.length,
          k_out.val < k.val →
          gc.moverAt k = right t ∨
            gc.moverAt k = right (right t))
    have hresidue_started_prefix_restart_phase_or_terminal_tail_split :
          (k_out.val + 1 = gc.configs.length) ∨
          LeftStartedPrefixRestartPhaseCommonResidue ∨
          LeftStartedPrefixRestartTerminalTailResidue ∨
          RightStartedPrefixRestartPhaseCommonResidue ∨
          RightStartedPrefixRestartTerminalTailResidue := by
      rcases hresidue_started_prefix_restart_edge_phase_terminal_split with
        hk_last | hLL4P | hLL4T | hLL2P | hLL2T | hRL2P | hRL2T | hRR4P | hRR4T
      · exact Or.inl hk_last
      · rcases hLL4P with ⟨hprefix, hphase⟩
        rcases hphase with
          ⟨_hprev, _hkout_left3, phase0, hphase0a, hlong, hphase_branch, _k1, _hk1, _hk1_left2⟩
        exact Or.inr (Or.inl ⟨hprefix.2, phase0, hphase0a, hlong, hphase_branch⟩)
      · rcases hLL4T with ⟨hprefix, htermEdge⟩
        rcases htermEdge with
          ⟨_hprev, _hkout_left3, _k1, _hk1, _hk1_left2, hterm⟩
        exact Or.inr (Or.inr (Or.inl ⟨hprefix.2, hterm⟩))
      · rcases hLL2P with ⟨hprefix, hphase⟩
        rcases hphase with
          ⟨_hprev, _hkout_left3, phase0, hphase0a, hlong, hphase_branch, _k1, _hk1, _hk1_left2⟩
        exact Or.inr (Or.inl ⟨hprefix.2, phase0, hphase0a, hlong, hphase_branch⟩)
      · rcases hLL2T with ⟨hprefix, htermEdge⟩
        rcases htermEdge with
          ⟨_hprev, _hkout_left3, _k1, _hk1, _hk1_left2, hterm⟩
        exact Or.inr (Or.inr (Or.inl ⟨hprefix.2, hterm⟩))
      · rcases hRL2P with ⟨hprefix, hphase⟩
        rcases hphase with
          ⟨_hprev, _hkout_right3, phase0, hphase0a, hlong, hphase_branch, _k1, _hk1, _hk1_right2⟩
        exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hprefix.2, phase0, hphase0a, hlong, hphase_branch⟩)))
      · rcases hRL2T with ⟨hprefix, htermEdge⟩
        rcases htermEdge with
          ⟨_hprev, _hkout_right3, _k1, _hk1, _hk1_right2, hterm⟩
        exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hprefix.2, hterm⟩)))
      · rcases hRR4P with ⟨hprefix, hphase⟩
        rcases hphase with
          ⟨_hprev, _hkout_right3, phase0, hphase0a, hlong, hphase_branch, _k1, _hk1, _hk1_right2⟩
        exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hprefix.2, phase0, hphase0a, hlong, hphase_branch⟩)))
      · rcases hRR4T with ⟨hprefix, htermEdge⟩
        rcases htermEdge with
          ⟨_hprev, _hkout_right3, _k1, _hk1, _hk1_right2, hterm⟩
        exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hprefix.2, hterm⟩)))
    let LeftStartedPrefixRestartTerminalPrefixResidue : Prop :=
        ∃ j : Fin gc.configs.length,
          j.val < k_out.val ∧
          (gc.moverAt j = left (left (left (left t))) ∨
            gc.moverAt j = right (right (right t))) ∧
          (∀ k : Fin gc.configs.length,
            j.val < k.val →
            gc.moverAt k = left (left (left t)) ∨
              gc.moverAt k = left (left t) ∨
              gc.moverAt k = left t ∨
              gc.moverAt k = t ∨
              gc.moverAt k = right t ∨
              gc.moverAt k = right (right t)) ∧
          gc.moverAt k_out = left (left (left t)) ∧
          ∃ k1 : Fin gc.configs.length,
            k1.val = k_out.val + 1 ∧
            gc.moverAt k1 = left (left t) ∧
            (∀ k : Fin gc.configs.length,
              k_out.val < k.val →
              gc.moverAt k = left (left t) ∨
                gc.moverAt k = left t)
    let RightStartedPrefixRestartTerminalPrefixResidue : Prop :=
        ∃ j : Fin gc.configs.length,
          j.val < k_out.val ∧
          (gc.moverAt j = left (left (left t)) ∨
            gc.moverAt j = right (right (right (right t)))) ∧
          (∀ k : Fin gc.configs.length,
            j.val < k.val →
            gc.moverAt k = left (left t) ∨
              gc.moverAt k = left t ∨
              gc.moverAt k = t ∨
              gc.moverAt k = right t ∨
              gc.moverAt k = right (right t) ∨
              gc.moverAt k = right (right (right t))) ∧
          gc.moverAt k_out = right (right (right t)) ∧
          ∃ k1 : Fin gc.configs.length,
            k1.val = k_out.val + 1 ∧
            gc.moverAt k1 = right (right t) ∧
            (∀ k : Fin gc.configs.length,
              k_out.val < k.val →
              gc.moverAt k = right t ∨
                gc.moverAt k = right (right t))
    have hresidue_started_prefix_restart_phase_or_terminal_prefix_split :
          (k_out.val + 1 = gc.configs.length) ∨
          LeftStartedPrefixRestartPhaseCommonResidue ∨
          LeftStartedPrefixRestartTerminalPrefixResidue ∨
          RightStartedPrefixRestartPhaseCommonResidue ∨
          RightStartedPrefixRestartTerminalPrefixResidue := by
      rcases hresidue_started_prefix_restart_phase_or_terminal_tail_split with
        hk_last | hLP | hLT | hRP | hRT
      · exact Or.inl hk_last
      · exact Or.inr (Or.inl hLP)
      · rcases hLT with ⟨hprefix, hterm⟩
        rcases hprefix with ⟨hkout_left3, k1, hk1, hk1_left2, hprefix⟩
        rcases hprefix with ⟨j, hj_lt, hj_edge, hj_tail⟩
        exact Or.inr (Or.inr (Or.inl
          ⟨j, hj_lt, hj_edge, hj_tail, hkout_left3, k1, hk1, hk1_left2, hterm⟩))
      · exact Or.inr (Or.inr (Or.inr (Or.inl hRP)))
      · rcases hRT with ⟨hprefix, hterm⟩
        rcases hprefix with ⟨hkout_right3, k1, hk1, hk1_right2, hprefix⟩
        rcases hprefix with ⟨j, hj_lt, hj_edge, hj_tail⟩
        exact Or.inr (Or.inr (Or.inr (Or.inr
          ⟨j, hj_lt, hj_edge, hj_tail, hkout_right3, k1, hk1, hk1_right2, hterm⟩)))
    let LeftStartedPrefixRestartTerminalSameResidue : Prop :=
        ∃ j : Fin gc.configs.length,
          j.val < k_out.val ∧
          gc.moverAt j = left (left (left (left t))) ∧
          (∀ k : Fin gc.configs.length,
            j.val < k.val →
            gc.moverAt k = left (left (left t)) ∨
              gc.moverAt k = left (left t) ∨
              gc.moverAt k = left t ∨
              gc.moverAt k = t ∨
              gc.moverAt k = right t ∨
              gc.moverAt k = right (right t)) ∧
          gc.moverAt k_out = left (left (left t)) ∧
          ∃ k1 : Fin gc.configs.length,
            k1.val = k_out.val + 1 ∧
            gc.moverAt k1 = left (left t) ∧
            (∀ k : Fin gc.configs.length,
              k_out.val < k.val →
              gc.moverAt k = left (left t) ∨
                gc.moverAt k = left t)
    let LeftStartedPrefixRestartTerminalCrossResidue : Prop :=
        ∃ j : Fin gc.configs.length,
          j.val < k_out.val ∧
          gc.moverAt j = right (right (right t)) ∧
          (∀ k : Fin gc.configs.length,
            j.val < k.val →
            gc.moverAt k = left (left (left t)) ∨
              gc.moverAt k = left (left t) ∨
              gc.moverAt k = left t ∨
              gc.moverAt k = t ∨
              gc.moverAt k = right t ∨
              gc.moverAt k = right (right t)) ∧
          gc.moverAt k_out = left (left (left t)) ∧
          ∃ k1 : Fin gc.configs.length,
            k1.val = k_out.val + 1 ∧
            gc.moverAt k1 = left (left t) ∧
            (∀ k : Fin gc.configs.length,
              k_out.val < k.val →
              gc.moverAt k = left (left t) ∨
                gc.moverAt k = left t)
    let RightStartedPrefixRestartTerminalCrossResidue : Prop :=
        ∃ j : Fin gc.configs.length,
          j.val < k_out.val ∧
          gc.moverAt j = left (left (left t)) ∧
          (∀ k : Fin gc.configs.length,
            j.val < k.val →
            gc.moverAt k = left (left t) ∨
              gc.moverAt k = left t ∨
              gc.moverAt k = t ∨
              gc.moverAt k = right t ∨
              gc.moverAt k = right (right t) ∨
              gc.moverAt k = right (right (right t))) ∧
          gc.moverAt k_out = right (right (right t)) ∧
          ∃ k1 : Fin gc.configs.length,
            k1.val = k_out.val + 1 ∧
            gc.moverAt k1 = right (right t) ∧
            (∀ k : Fin gc.configs.length,
              k_out.val < k.val →
              gc.moverAt k = right t ∨
                gc.moverAt k = right (right t))
    let RightStartedPrefixRestartTerminalSameResidue : Prop :=
        ∃ j : Fin gc.configs.length,
          j.val < k_out.val ∧
          gc.moverAt j = right (right (right (right t))) ∧
          (∀ k : Fin gc.configs.length,
            j.val < k.val →
            gc.moverAt k = left (left t) ∨
              gc.moverAt k = left t ∨
              gc.moverAt k = t ∨
              gc.moverAt k = right t ∨
              gc.moverAt k = right (right t) ∨
              gc.moverAt k = right (right (right t))) ∧
          gc.moverAt k_out = right (right (right t)) ∧
          ∃ k1 : Fin gc.configs.length,
            k1.val = k_out.val + 1 ∧
            gc.moverAt k1 = right (right t) ∧
            (∀ k : Fin gc.configs.length,
              k_out.val < k.val →
              gc.moverAt k = right t ∨
                gc.moverAt k = right (right t))
    have hresidue_started_prefix_restart_phase_or_terminal_prefix_exact_split :
          (k_out.val + 1 = gc.configs.length) ∨
          LeftStartedPrefixRestartPhaseCommonResidue ∨
          LeftStartedPrefixRestartTerminalSameResidue ∨
          LeftStartedPrefixRestartTerminalCrossResidue ∨
          RightStartedPrefixRestartPhaseCommonResidue ∨
          RightStartedPrefixRestartTerminalCrossResidue ∨
          RightStartedPrefixRestartTerminalSameResidue := by
      rcases hresidue_started_prefix_restart_phase_or_terminal_prefix_split with
        hk_last | hLP | hLT | hRP | hRT
      · exact Or.inl hk_last
      · exact Or.inr (Or.inl hLP)
      · rcases hLT with ⟨j, hj_lt, hj_edge, hj_tail, hkout_left3, k1, hk1, hk1_left2, hterm⟩
        rcases hj_edge with hj_left4 | hj_right3
        · exact Or.inr (Or.inr (Or.inl
            ⟨j, hj_lt, hj_left4, hj_tail, hkout_left3, k1, hk1, hk1_left2, hterm⟩))
        · exact Or.inr (Or.inr (Or.inr (Or.inl
            ⟨j, hj_lt, hj_right3, hj_tail, hkout_left3, k1, hk1, hk1_left2, hterm⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hRP))))
      · rcases hRT with ⟨j, hj_lt, hj_edge, hj_tail, hkout_right3, k1, hk1, hk1_right2, hterm⟩
        rcases hj_edge with hj_left3 | hj_right4
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
            ⟨j, hj_lt, hj_left3, hj_tail, hkout_right3, k1, hk1, hk1_right2, hterm⟩)))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
            ⟨j, hj_lt, hj_right4, hj_tail, hkout_right3, k1, hk1, hk1_right2, hterm⟩)))))
    let LeftStartedPrefixRestartPhaseSameResidue : Prop :=
        LeftStartedPrefixSameResidue ∧
        ∃ phase0 : TernaryPhase gc t,
          phase0.a = k_out ∧
          k_out.val + 2 < phase0.s.val ∧
          (∀ k : Fin gc.configs.length,
            k_out.val < k.val → k.val < phase0.s.val →
            gc.moverAt k = left (left t) ∨
              gc.moverAt k = left t)
    let LeftStartedPrefixRestartPhaseCrossResidue : Prop :=
        LeftStartedPrefixCrossResidue ∧
        ∃ phase0 : TernaryPhase gc t,
          phase0.a = k_out ∧
          k_out.val + 2 < phase0.s.val ∧
          (∀ k : Fin gc.configs.length,
            k_out.val < k.val → k.val < phase0.s.val →
            gc.moverAt k = left (left t) ∨
              gc.moverAt k = left t)
    let RightStartedPrefixRestartPhaseCrossResidue : Prop :=
        RightStartedPrefixCrossResidue ∧
        ∃ phase0 : TernaryPhase gc t,
          phase0.a = k_out ∧
          k_out.val + 2 < phase0.s.val ∧
          (∀ k : Fin gc.configs.length,
            k_out.val < k.val → k.val < phase0.s.val →
            gc.moverAt k = right t ∨
              gc.moverAt k = right (right t))
    let RightStartedPrefixRestartPhaseSameResidue : Prop :=
        RightStartedPrefixSameResidue ∧
        ∃ phase0 : TernaryPhase gc t,
          phase0.a = k_out ∧
          k_out.val + 2 < phase0.s.val ∧
          (∀ k : Fin gc.configs.length,
            k_out.val < k.val → k.val < phase0.s.val →
            gc.moverAt k = right t ∨
              gc.moverAt k = right (right t))
    have hleft_started_prefix_restart_phase_same_or_cross :
        LeftStartedPrefixRestartPhaseCommonResidue →
          LeftStartedPrefixRestartPhaseSameResidue ∨
            LeftStartedPrefixRestartPhaseCrossResidue := by
      intro h
      rcases h with ⟨hprefix, phase0, hphase0a, hlong, hphase_branch⟩
      rcases hleft_started_prefix_same_or_cross (hleft_started_prefix_sharp hprefix) with hsame | hcross
      · exact Or.inl ⟨hsame, phase0, hphase0a, hlong, hphase_branch⟩
      · exact Or.inr ⟨hcross, phase0, hphase0a, hlong, hphase_branch⟩
    have hright_started_prefix_restart_phase_same_or_cross :
        RightStartedPrefixRestartPhaseCommonResidue →
          RightStartedPrefixRestartPhaseCrossResidue ∨
            RightStartedPrefixRestartPhaseSameResidue := by
      intro h
      rcases h with ⟨hprefix, phase0, hphase0a, hlong, hphase_branch⟩
      rcases hright_started_prefix_same_or_cross (hright_started_prefix_sharp hprefix) with hcross | hsame
      · exact Or.inl ⟨hcross, phase0, hphase0a, hlong, hphase_branch⟩
      · exact Or.inr ⟨hsame, phase0, hphase0a, hlong, hphase_branch⟩
    have hresidue_started_prefix_restart_phase_or_terminal_prefix_sharp_split :
          (k_out.val + 1 = gc.configs.length) ∨
          LeftStartedPrefixRestartPhaseSameResidue ∨
          LeftStartedPrefixRestartPhaseCrossResidue ∨
          LeftStartedPrefixRestartTerminalSameResidue ∨
          LeftStartedPrefixRestartTerminalCrossResidue ∨
          RightStartedPrefixRestartPhaseCrossResidue ∨
          RightStartedPrefixRestartPhaseSameResidue ∨
          RightStartedPrefixRestartTerminalCrossResidue ∨
          RightStartedPrefixRestartTerminalSameResidue := by
      rcases hresidue_started_prefix_restart_phase_or_terminal_prefix_exact_split with
        hk_last | hLP | hLTS | hLTX | hRP | hRTX | hRTS
      · exact Or.inl hk_last
      · rcases hleft_started_prefix_restart_phase_same_or_cross hLP with hLPS | hLPX
        · exact Or.inr (Or.inl hLPS)
        · exact Or.inr (Or.inr (Or.inl hLPX))
      · exact Or.inr (Or.inr (Or.inr (Or.inl hLTS)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hLTX))))
      · rcases hright_started_prefix_restart_phase_same_or_cross hRP with hRPX | hRPS
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hRPX)))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hRPS))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hRTX)))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hRTS)))))))
    let LeftStartedFromLeft4PrefixSameRestartResidue : Prop :=
        LeftStartedFromLeft4PrefixSameResidue ∧ LeftKoutStartedResidue
    let LeftStartedFromLeft4PrefixCrossRestartResidue : Prop :=
        LeftStartedFromLeft4PrefixCrossResidue ∧ LeftKoutStartedResidue
    let LeftStartedFromLeft2PrefixSameRestartResidue : Prop :=
        LeftStartedFromLeft2PrefixSameResidue ∧ LeftKoutStartedResidue
    let LeftStartedFromLeft2PrefixCrossRestartResidue : Prop :=
        LeftStartedFromLeft2PrefixCrossResidue ∧ LeftKoutStartedResidue
    let RightStartedFromLeft2PrefixCrossRestartResidue : Prop :=
        RightStartedFromLeft2PrefixCrossResidue ∧ RightKoutStartedResidue
    let RightStartedFromLeft2PrefixSameRestartResidue : Prop :=
        RightStartedFromLeft2PrefixSameResidue ∧ RightKoutStartedResidue
    let RightStartedFromRight4PrefixCrossRestartResidue : Prop :=
        RightStartedFromRight4PrefixCrossResidue ∧ RightKoutStartedResidue
    let RightStartedFromRight4PrefixSameRestartResidue : Prop :=
        RightStartedFromRight4PrefixSameResidue ∧ RightKoutStartedResidue
    have hresidue_started_prefix_restart_exact_split :
          (k_out.val + 1 = gc.configs.length) ∨
          LeftStartedFromLeft4PrefixSameRestartResidue ∨
          LeftStartedFromLeft4PrefixCrossRestartResidue ∨
          LeftStartedFromLeft2PrefixSameRestartResidue ∨
          LeftStartedFromLeft2PrefixCrossRestartResidue ∨
          RightStartedFromLeft2PrefixCrossRestartResidue ∨
          RightStartedFromLeft2PrefixSameRestartResidue ∨
          RightStartedFromRight4PrefixCrossRestartResidue ∨
          RightStartedFromRight4PrefixSameRestartResidue := by
      rcases hresidue_started_prefix_exact_split with
        hk_last | hLL4S | hLL4X | hLL2S | hLL2X | hRL2X | hRL2S | hRR4X | hRR4S
      · exact Or.inl hk_last
      · rcases hresidue_started_prefix_kout_started with hk_last' | hleft | hright
        · exact Or.inl hk_last'
        · exact Or.inr <| Or.inl <| ⟨hLL4S, hleft⟩
        · rcases hLL4S with ⟨_hprev, hkout_left3, _k1, _hk1, _hk1_left2, _j, _j1, _hj_lt, _hj1, _hj_left4, _hj1_left3, _hj_tail⟩
          rcases hright with ⟨hkout_right3, _⟩
          exact False.elim (right3_ne_left3 (by omega) t (by
            calc
              right (right (right t)) = gc.moverAt k_out := hkout_right3.symm
              _ = left (left (left t)) := hkout_left3))
      · rcases hresidue_started_prefix_kout_started with hk_last' | hleft | hright
        · exact Or.inl hk_last'
        · exact Or.inr <| Or.inr <| Or.inl <| ⟨hLL4X, hleft⟩
        · rcases hLL4X with ⟨_hprev, hkout_left3, _k1, _hk1, _hk1_left2, _j, _j1, _hj_lt, _hj1, _hj_right3, _hj1_right2, _hj_tail⟩
          rcases hright with ⟨hkout_right3, _⟩
          exact False.elim (right3_ne_left3 (by omega) t (by
            calc
              right (right (right t)) = gc.moverAt k_out := hkout_right3.symm
              _ = left (left (left t)) := hkout_left3))
      · rcases hresidue_started_prefix_kout_started with hk_last' | hleft | hright
        · exact Or.inl hk_last'
        · exact Or.inr <| Or.inr <| Or.inr <| Or.inl <| ⟨hLL2S, hleft⟩
        · rcases hLL2S with ⟨_hprev, hkout_left3, _k1, _hk1, _hk1_left2, _j, _j1, _hj_lt, _hj1, _hj_left4, _hj1_left3, _hj_tail⟩
          rcases hright with ⟨hkout_right3, _⟩
          exact False.elim (right3_ne_left3 (by omega) t (by
            calc
              right (right (right t)) = gc.moverAt k_out := hkout_right3.symm
              _ = left (left (left t)) := hkout_left3))
      · rcases hresidue_started_prefix_kout_started with hk_last' | hleft | hright
        · exact Or.inl hk_last'
        · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl <| ⟨hLL2X, hleft⟩
        · rcases hLL2X with ⟨_hprev, hkout_left3, _k1, _hk1, _hk1_left2, _j, _j1, _hj_lt, _hj1, _hj_right3, _hj1_right2, _hj_tail⟩
          rcases hright with ⟨hkout_right3, _⟩
          exact False.elim (right3_ne_left3 (by omega) t (by
            calc
              right (right (right t)) = gc.moverAt k_out := hkout_right3.symm
              _ = left (left (left t)) := hkout_left3))
      · rcases hresidue_started_prefix_kout_started with hk_last' | hleft | hright
        · exact Or.inl hk_last'
        · rcases hRL2X with ⟨_hprev, hkout_right3, _k1, _hk1, _hk1_right2, _j, _j1, _hj_lt, _hj1, _hj_left3, _hj1_left2, _hj_tail⟩
          rcases hleft with ⟨hkout_left3, _⟩
          exact False.elim (left3_ne_right3 (by omega) t (by
            calc
              left (left (left t)) = gc.moverAt k_out := hkout_left3.symm
              _ = right (right (right t)) := hkout_right3))
        · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl <| ⟨hRL2X, hright⟩
      · rcases hresidue_started_prefix_kout_started with hk_last' | hleft | hright
        · exact Or.inl hk_last'
        · rcases hRL2S with ⟨_hprev, hkout_right3, _k1, _hk1, _hk1_right2, _j, _j1, _hj_lt, _hj1, _hj_right4, _hj1_right3, _hj_tail⟩
          rcases hleft with ⟨hkout_left3, _⟩
          exact False.elim (left3_ne_right3 (by omega) t (by
            calc
              left (left (left t)) = gc.moverAt k_out := hkout_left3.symm
              _ = right (right (right t)) := hkout_right3))
        · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl <| ⟨hRL2S, hright⟩
      · rcases hresidue_started_prefix_kout_started with hk_last' | hleft | hright
        · exact Or.inl hk_last'
        · rcases hRR4X with ⟨_hprev, hkout_right3, _k1, _hk1, _hk1_right2, _j, _j1, _hj_lt, _hj1, _hj_left3, _hj1_left2, _hj_tail⟩
          rcases hleft with ⟨hkout_left3, _⟩
          exact False.elim (left3_ne_right3 (by omega) t (by
            calc
              left (left (left t)) = gc.moverAt k_out := hkout_left3.symm
              _ = right (right (right t)) := hkout_right3))
        · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl <| ⟨hRR4X, hright⟩
      · rcases hresidue_started_prefix_kout_started with hk_last' | hleft | hright
        · exact Or.inl hk_last'
        · rcases hRR4S with ⟨_hprev, hkout_right3, _k1, _hk1, _hk1_right2, _j, _j1, _hj_lt, _hj1, _hj_right4, _hj1_right3, _hj_tail⟩
          rcases hleft with ⟨hkout_left3, _⟩
          exact False.elim (left3_ne_right3 (by omega) t (by
            calc
              left (left (left t)) = gc.moverAt k_out := hkout_left3.symm
              _ = right (right (right t)) := hkout_right3))
        · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| ⟨hRR4S, hright⟩
    let LeftStartedFromLeft4PrefixSameTailRestartResidue : Prop :=
        LeftStartedFromLeft4PrefixSameResidue ∧ (LeftTailResidue ∧ LeftKoutStartedResidue)
    let LeftStartedFromLeft4PrefixCrossTailRestartResidue : Prop :=
        LeftStartedFromLeft4PrefixCrossResidue ∧ (LeftTailResidue ∧ LeftKoutStartedResidue)
    let LeftStartedFromLeft2PrefixSameTailRestartResidue : Prop :=
        LeftStartedFromLeft2PrefixSameResidue ∧ (LeftTailResidue ∧ LeftKoutStartedResidue)
    let LeftStartedFromLeft2PrefixCrossTailRestartResidue : Prop :=
        LeftStartedFromLeft2PrefixCrossResidue ∧ (LeftTailResidue ∧ LeftKoutStartedResidue)
    let RightStartedFromLeft2PrefixCrossTailRestartResidue : Prop :=
        RightStartedFromLeft2PrefixCrossResidue ∧ (RightTailResidue ∧ RightKoutStartedResidue)
    let RightStartedFromLeft2PrefixSameTailRestartResidue : Prop :=
        RightStartedFromLeft2PrefixSameResidue ∧ (RightTailResidue ∧ RightKoutStartedResidue)
    let RightStartedFromRight4PrefixCrossTailRestartResidue : Prop :=
        RightStartedFromRight4PrefixCrossResidue ∧ (RightTailResidue ∧ RightKoutStartedResidue)
    let RightStartedFromRight4PrefixSameTailRestartResidue : Prop :=
        RightStartedFromRight4PrefixSameResidue ∧ (RightTailResidue ∧ RightKoutStartedResidue)
    have hresidue_started_prefix_restart_tail_exact_split :
          (k_out.val + 1 = gc.configs.length) ∨
          LeftStartedFromLeft4PrefixSameTailRestartResidue ∨
          LeftStartedFromLeft4PrefixCrossTailRestartResidue ∨
          LeftStartedFromLeft2PrefixSameTailRestartResidue ∨
          LeftStartedFromLeft2PrefixCrossTailRestartResidue ∨
          RightStartedFromLeft2PrefixCrossTailRestartResidue ∨
          RightStartedFromLeft2PrefixSameTailRestartResidue ∨
          RightStartedFromRight4PrefixCrossTailRestartResidue ∨
          RightStartedFromRight4PrefixSameTailRestartResidue := by
      rcases hresidue_started_prefix_restart_exact_split with
        hk_last | hLL4S | hLL4X | hLL2S | hLL2X | hRL2X | hRL2S | hRR4X | hRR4S
      · exact Or.inl hk_last
      · exact Or.inr <| Or.inl <|
          ⟨hLL4S.1, ⟨hleft_same_tail (hleft_started_prefix_same_final hLL4S.1.2), hLL4S.2⟩⟩
      · exact Or.inr <| Or.inr <| Or.inl <|
          ⟨hLL4X.1, ⟨hleft_cross_tail (hleft_started_prefix_cross_final hLL4X.1.2), hLL4X.2⟩⟩
      · exact Or.inr <| Or.inr <| Or.inr <| Or.inl <|
          ⟨hLL2S.1, ⟨hleft_same_tail (hleft_started_prefix_same_final hLL2S.1.2), hLL2S.2⟩⟩
      · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl <|
          ⟨hLL2X.1, ⟨hleft_cross_tail (hleft_started_prefix_cross_final hLL2X.1.2), hLL2X.2⟩⟩
      · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl <|
          ⟨hRL2X.1, ⟨hright_cross_tail (hright_started_prefix_cross_final hRL2X.1.2), hRL2X.2⟩⟩
      · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl <|
          ⟨hRL2S.1, ⟨hright_same_tail (hright_started_prefix_same_final hRL2S.1.2), hRL2S.2⟩⟩
      · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl <|
          ⟨hRR4X.1, ⟨hright_cross_tail (hright_started_prefix_cross_final hRR4X.1.2), hRR4X.2⟩⟩
      · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
          ⟨hRR4S.1, ⟨hright_same_tail (hright_started_prefix_same_final hRR4S.1.2), hRR4S.2⟩⟩
    have hresidue_started_prefix_restart_tail :
          (k_out.val + 1 = gc.configs.length) ∨ LeftTailRestartResidue ∨ RightTailRestartResidue := by
      rcases hresidue_started_prefix_restart_tail_exact_split with
        hk_last | hLL4S | hLL4X | hLL2S | hLL2X | hRL2X | hRL2S | hRR4X | hRR4S
      · exact Or.inl hk_last
      · exact Or.inr (Or.inl hLL4S.2)
      · exact Or.inr (Or.inl hLL4X.2)
      · exact Or.inr (Or.inl hLL2S.2)
      · exact Or.inr (Or.inl hLL2X.2)
      · exact Or.inr (Or.inr hRL2X.2)
      · exact Or.inr (Or.inr hRL2S.2)
      · exact Or.inr (Or.inr hRR4X.2)
      · exact Or.inr (Or.inr hRR4S.2)
    have hleft_tail_restart_prev_shape0 :
        LeftTailRestartResidue →
        LeftStartedFromLeft4Residue ∨ LeftStartedFromLeft2Residue := by
      intro h
      rcases h with ⟨htail, hstart⟩
      rcases hleft_tail_prev_shape htail with
        ⟨cut, prev, hsucc, hle, hprev, hcut, htail'⟩
      rcases hprev with hprev | hprev
      · exact Or.inl ⟨⟨cut, prev, hsucc, hle, hprev, hcut, htail'⟩, hstart⟩
      · exact Or.inr ⟨⟨cut, prev, hsucc, hle, hprev, hcut, htail'⟩, hstart⟩
    have hright_tail_restart_prev_shape0 :
        RightTailRestartResidue →
        RightStartedFromLeft2Residue ∨ RightStartedFromRight4Residue := by
      intro h
      rcases h with ⟨htail, hstart⟩
      rcases hright_tail_prev_shape htail with
        ⟨cut, prev, hsucc, hle, hprev, hcut, htail'⟩
      rcases hprev with hprev | hprev
      · exact Or.inl ⟨⟨cut, prev, hsucc, hle, hprev, hcut, htail'⟩, hstart⟩
      · exact Or.inr ⟨⟨cut, prev, hsucc, hle, hprev, hcut, htail'⟩, hstart⟩
    let LeftStartedFromLeft4MinRestartResidue : Prop :=
        ∃ cut prev : Fin gc.configs.length,
          prev.val + 1 = cut.val ∧
          cut.val ≤ k_out.val ∧
          gc.moverAt prev = left (left (left (left t))) ∧
          gc.moverAt cut = left (left (left t)) ∧
          (∀ k : Fin gc.configs.length,
            cut.val ≤ k.val →
            gc.moverAt k = left (left (left t)) ∨
              gc.moverAt k = left (left t) ∨
              gc.moverAt k = left t ∨
              gc.moverAt k = t ∨
              gc.moverAt k = right t ∨
              gc.moverAt k = right (right t)) ∧
          (∀ cut' : Fin gc.configs.length,
            cut'.val < cut.val →
            ¬(cut'.val ≤ k_out.val ∧
              gc.moverAt cut' = left (left (left t)) ∧
              (∀ k : Fin gc.configs.length,
                cut'.val ≤ k.val →
                gc.moverAt k = left (left (left t)) ∨
                  gc.moverAt k = left (left t) ∨
                  gc.moverAt k = left t ∨
                  gc.moverAt k = t ∨
                  gc.moverAt k = right t ∨
                  gc.moverAt k = right (right t)))) ∧
          LeftKoutStartedResidue
    let LeftStartedFromLeft2MinRestartResidue : Prop :=
        ∃ cut prev : Fin gc.configs.length,
          prev.val + 1 = cut.val ∧
          cut.val ≤ k_out.val ∧
          gc.moverAt prev = left (left t) ∧
          gc.moverAt cut = left (left (left t)) ∧
          (∀ k : Fin gc.configs.length,
            cut.val ≤ k.val →
            gc.moverAt k = left (left (left t)) ∨
              gc.moverAt k = left (left t) ∨
              gc.moverAt k = left t ∨
              gc.moverAt k = t ∨
              gc.moverAt k = right t ∨
              gc.moverAt k = right (right t)) ∧
          (∀ cut' : Fin gc.configs.length,
            cut'.val < cut.val →
            ¬(cut'.val ≤ k_out.val ∧
              gc.moverAt cut' = left (left (left t)) ∧
              (∀ k : Fin gc.configs.length,
                cut'.val ≤ k.val →
                gc.moverAt k = left (left (left t)) ∨
                  gc.moverAt k = left (left t) ∨
                  gc.moverAt k = left t ∨
                  gc.moverAt k = t ∨
                  gc.moverAt k = right t ∨
                  gc.moverAt k = right (right t)))) ∧
          LeftKoutStartedResidue
    let RightStartedFromLeft2MinRestartResidue : Prop :=
        ∃ cut prev : Fin gc.configs.length,
          prev.val + 1 = cut.val ∧
          cut.val ≤ k_out.val ∧
          gc.moverAt prev = right (right t) ∧
          gc.moverAt cut = right (right (right t)) ∧
          (∀ k : Fin gc.configs.length,
            cut.val ≤ k.val →
            gc.moverAt k = left (left t) ∨
              gc.moverAt k = left t ∨
              gc.moverAt k = t ∨
              gc.moverAt k = right t ∨
              gc.moverAt k = right (right t) ∨
              gc.moverAt k = right (right (right t))) ∧
          (∀ cut' : Fin gc.configs.length,
            cut'.val < cut.val →
            ¬(cut'.val ≤ k_out.val ∧
              gc.moverAt cut' = right (right (right t)) ∧
              (∀ k : Fin gc.configs.length,
                cut'.val ≤ k.val →
                gc.moverAt k = left (left t) ∨
                  gc.moverAt k = left t ∨
                  gc.moverAt k = t ∨
                  gc.moverAt k = right t ∨
                  gc.moverAt k = right (right t) ∨
                  gc.moverAt k = right (right (right t))))) ∧
          RightKoutStartedResidue
    let RightStartedFromRight4MinRestartResidue : Prop :=
        ∃ cut prev : Fin gc.configs.length,
          prev.val + 1 = cut.val ∧
          cut.val ≤ k_out.val ∧
          gc.moverAt prev = right (right (right (right t))) ∧
          gc.moverAt cut = right (right (right t)) ∧
          (∀ k : Fin gc.configs.length,
            cut.val ≤ k.val →
            gc.moverAt k = left (left t) ∨
              gc.moverAt k = left t ∨
              gc.moverAt k = t ∨
              gc.moverAt k = right t ∨
              gc.moverAt k = right (right t) ∨
              gc.moverAt k = right (right (right t))) ∧
          (∀ cut' : Fin gc.configs.length,
            cut'.val < cut.val →
            ¬(cut'.val ≤ k_out.val ∧
              gc.moverAt cut' = right (right (right t)) ∧
              (∀ k : Fin gc.configs.length,
                cut'.val ≤ k.val →
                gc.moverAt k = left (left t) ∨
                  gc.moverAt k = left t ∨
                  gc.moverAt k = t ∨
                  gc.moverAt k = right t ∨
                  gc.moverAt k = right (right t) ∨
                  gc.moverAt k = right (right (right t))))) ∧
          RightKoutStartedResidue
    have hleft_tail_restart_prev_shape_min :
        LeftTailRestartResidue →
        LeftStartedFromLeft4MinRestartResidue ∨ LeftStartedFromLeft2MinRestartResidue := by
      intro h
      rcases h with ⟨htail, hstart⟩
      rcases hleft_tail_min htail with
        ⟨cut, hcut_le, hcut_left3, hcut_tail, hcut_min⟩
      rcases all_left_six_or_prefix_bad_left4_or_right3_strong gc t cut hcut_tail with hall | hprefix
      · exact False.elim (movers_in_left_six_contradicts_hno_safe gc _hn _hno_safe t hall)
      · rcases hprefix with ⟨j, hj_lt, hj_edge, hj_tail⟩
        have hj1_lt_len : j.val + 1 < gc.configs.length := by
          exact lt_of_le_of_lt (Nat.succ_le_of_lt hj_lt) cut.isLt
        let j1 : Fin gc.configs.length := ⟨j.val + 1, hj1_lt_len⟩
        have hsucc :=
          left_prefix_edge_successor_shape gc t (by omega) j hj1_lt_len hj_edge hj_tail
        rcases hsucc with hsame | hcross
        · have hj1_le_kout : j1.val ≤ k_out.val := by
            rw [show j1.val = j.val + 1 by rfl]
            omega
          have hj1_tail :
              ∀ k : Fin gc.configs.length,
                j1.val ≤ k.val →
                gc.moverAt k = left (left (left t)) ∨
                  gc.moverAt k = left (left t) ∨
                  gc.moverAt k = left t ∨
                  gc.moverAt k = t ∨
                  gc.moverAt k = right t ∨
                  gc.moverAt k = right (right t) := by
            intro k hk_ge
            have hj_lt_k : j.val < k.val := by
              rw [show j1.val = j.val + 1 by rfl] at hk_ge
              omega
            exact hj_tail k hj_lt_k
          have hnot_lt : ¬ j1.val < cut.val := by
            intro hj1_lt_cut
            exact (hcut_min j1 hj1_lt_cut) ⟨hj1_le_kout, hsame.2, hj1_tail⟩
          have hj1_le_cut : j1.val ≤ cut.val := by
            rw [show j1.val = j.val + 1 by rfl]
            omega
          have hj1_eq_cut : j1 = cut := by
            apply Fin.ext
            exact Nat.le_antisymm hj1_le_cut (Nat.le_of_not_gt hnot_lt)
          exact Or.inl ⟨cut, j,
            by simpa [j1] using congrArg Fin.val hj1_eq_cut,
            hcut_le, hsame.1, hcut_left3, hcut_tail, hcut_min, hstart⟩
        · have hj1_ne_cut : j1 ≠ cut := by
            intro hEq
            apply right2_ne_left3 (by omega) t
            calc
              right (right t) = gc.moverAt j1 := hcross.2.symm
              _ = gc.moverAt cut := by rw [hEq]
              _ = left (left (left t)) := hcut_left3
          have hj1_lt_cut : j1.val < cut.val := by
            have hj1_le_cut : j1.val ≤ cut.val := by
              rw [show j1.val = j.val + 1 by rfl]
              omega
            have hneq : j1.val ≠ cut.val := by
              intro hval
              exact hj1_ne_cut (Fin.ext hval)
            omega
          rcases first_left3_after_right2_in_leftsix_tail gc t (by omega) j j1 cut
            (by
              rw [show j1.val = j.val + 1 by rfl]
              omega) hj1_lt_cut hcross.2 hcut_left3 hj_tail with
            ⟨a, prev, _hj1_lt_prev, hprev_succ, ha_le_cut, hprev_left2, ha_left3⟩
          have ha_eq_cut : a = cut := by
            by_contra hneq
            have ha_lt_cut : a.val < cut.val := by
              have hneqv : a.val ≠ cut.val := by
                intro hval
                exact hneq (Fin.ext hval)
              omega
            have hprop :
                a.val ≤ k_out.val ∧
                gc.moverAt a = left (left (left t)) ∧
                (∀ k : Fin gc.configs.length,
                  a.val ≤ k.val →
                  gc.moverAt k = left (left (left t)) ∨
                    gc.moverAt k = left (left t) ∨
                    gc.moverAt k = left t ∨
                    gc.moverAt k = t ∨
                    gc.moverAt k = right t ∨
                    gc.moverAt k = right (right t)) := by
              refine ⟨le_trans ha_le_cut hcut_le, ha_left3, ?_⟩
              intro k hk_ge
              have hj_lt_k : j.val < k.val := by
                have hj_lt_a : j.val < a.val := by
                  have hj1_lt_a : j1.val < a.val := by
                    rw [← hprev_succ]
                    omega
                  rw [show j1.val = j.val + 1 by rfl] at hj1_lt_a
                  omega
                omega
              exact hj_tail k hj_lt_k
            exact (hcut_min a ha_lt_cut) hprop
          exact Or.inr ⟨cut, prev,
            by simpa [ha_eq_cut] using hprev_succ,
            hcut_le, hprev_left2, hcut_left3, hcut_tail, hcut_min, hstart⟩
    have hright_tail_restart_prev_shape_min :
        RightTailRestartResidue →
        RightStartedFromLeft2MinRestartResidue ∨ RightStartedFromRight4MinRestartResidue := by
      intro h
      rcases h with ⟨htail, hstart⟩
      rcases hright_tail_min htail with
        ⟨cut, hcut_le, hcut_right3, hcut_tail, hcut_min⟩
      rcases all_right_six_or_prefix_bad_left3_or_right4_strong gc t cut hcut_tail with hall | hprefix
      · exact False.elim (movers_in_right_six_contradicts_hno_safe gc _hn _hno_safe t hall)
      · rcases hprefix with ⟨j, hj_lt, hj_edge, hj_tail⟩
        have hj1_lt_len : j.val + 1 < gc.configs.length := by
          exact lt_of_le_of_lt (Nat.succ_le_of_lt hj_lt) cut.isLt
        let j1 : Fin gc.configs.length := ⟨j.val + 1, hj1_lt_len⟩
        have hsucc :=
          right_prefix_edge_successor_shape gc t (by omega) j hj1_lt_len hj_edge hj_tail
        rcases hsucc with hcross | hsame
        · have hj1_ne_cut : j1 ≠ cut := by
            intro hEq
            apply left2_ne_right3 (by omega) t
            calc
              left (left t) = gc.moverAt j1 := hcross.2.symm
              _ = gc.moverAt cut := by rw [hEq]
              _ = right (right (right t)) := hcut_right3
          have hj1_lt_cut : j1.val < cut.val := by
            have hj1_le_cut : j1.val ≤ cut.val := by
              rw [show j1.val = j.val + 1 by rfl]
              omega
            have hneq : j1.val ≠ cut.val := by
              intro hval
              exact hj1_ne_cut (Fin.ext hval)
            omega
          rcases first_right3_after_left2_in_rightsix_tail gc t (by omega) j j1 cut
            (by
              rw [show j1.val = j.val + 1 by rfl]
              omega) hj1_lt_cut hcross.2 hcut_right3 hj_tail with
            ⟨a, prev, _hj1_lt_prev, hprev_succ, ha_le_cut, hprev_right2, ha_right3⟩
          have ha_eq_cut : a = cut := by
            by_contra hneq
            have ha_lt_cut : a.val < cut.val := by
              have hneqv : a.val ≠ cut.val := by
                intro hval
                exact hneq (Fin.ext hval)
              omega
            have hprop :
                a.val ≤ k_out.val ∧
                gc.moverAt a = right (right (right t)) ∧
                (∀ k : Fin gc.configs.length,
                  a.val ≤ k.val →
                  gc.moverAt k = left (left t) ∨
                    gc.moverAt k = left t ∨
                    gc.moverAt k = t ∨
                    gc.moverAt k = right t ∨
                    gc.moverAt k = right (right t) ∨
                    gc.moverAt k = right (right (right t))) := by
              refine ⟨le_trans ha_le_cut hcut_le, ha_right3, ?_⟩
              intro k hk_ge
              have hj_lt_k : j.val < k.val := by
                have hj_lt_a : j.val < a.val := by
                  have hj1_lt_a : j1.val < a.val := by
                    rw [← hprev_succ]
                    omega
                  rw [show j1.val = j.val + 1 by rfl] at hj1_lt_a
                  omega
                omega
              exact hj_tail k hj_lt_k
            exact (hcut_min a ha_lt_cut) hprop
          exact Or.inl ⟨cut, prev,
            by simpa [ha_eq_cut] using hprev_succ,
            hcut_le, hprev_right2, hcut_right3, hcut_tail, hcut_min, hstart⟩
        · have hj1_le_kout : j1.val ≤ k_out.val := by
            rw [show j1.val = j.val + 1 by rfl]
            omega
          have hj1_tail :
              ∀ k : Fin gc.configs.length,
                j1.val ≤ k.val →
                gc.moverAt k = left (left t) ∨
                  gc.moverAt k = left t ∨
                  gc.moverAt k = t ∨
                  gc.moverAt k = right t ∨
                  gc.moverAt k = right (right t) ∨
                  gc.moverAt k = right (right (right t)) := by
            intro k hk_ge
            have hj_lt_k : j.val < k.val := by
              rw [show j1.val = j.val + 1 by rfl] at hk_ge
              omega
            exact hj_tail k hj_lt_k
          have hnot_lt : ¬ j1.val < cut.val := by
            intro hj1_lt_cut
            exact (hcut_min j1 hj1_lt_cut) ⟨hj1_le_kout, hsame.2, hj1_tail⟩
          have hj1_eq_cut : j1 = cut := by
            apply Fin.ext
            have hj1_le_cut : j1.val ≤ cut.val := by
              rw [show j1.val = j.val + 1 by rfl]
              omega
            exact Nat.le_antisymm hj1_le_cut (Nat.le_of_not_gt hnot_lt)
          exact Or.inr ⟨cut, j,
            by simpa [j1] using congrArg Fin.val hj1_eq_cut,
            hcut_le, hsame.1, hcut_right3, hcut_tail, hcut_min, hstart⟩
    have hresidue_started_prefix_restart_prev_grouped_split :
          (k_out.val + 1 = gc.configs.length) ∨
          (LeftStartedPrefixExactResidue ∧ LeftStartedFromLeft4Residue) ∨
          (LeftStartedPrefixExactResidue ∧ LeftStartedFromLeft2Residue) ∨
          (RightStartedPrefixExactResidue ∧ RightStartedFromLeft2Residue) ∨
          (RightStartedPrefixExactResidue ∧ RightStartedFromRight4Residue) := by
      rcases hresidue_started_prefix_restart_tail_exact_split with
        hk_last | hLL4S | hLL4X | hLL2S | hLL2X | hRL2X | hRL2S | hRR4X | hRR4S
      · exact Or.inl hk_last
      · rcases hleft_tail_restart_prev_shape0 hLL4S.2 with hLL4 | hLL2
        · exact Or.inr (Or.inl ⟨Or.inl hLL4S.1, hLL4⟩)
        · exact Or.inr (Or.inr (Or.inl ⟨Or.inl hLL4S.1, hLL2⟩))
      · rcases hleft_tail_restart_prev_shape0 hLL4X.2 with hLL4 | hLL2
        · exact Or.inr (Or.inl ⟨Or.inr (Or.inl hLL4X.1), hLL4⟩)
        · exact Or.inr (Or.inr (Or.inl ⟨Or.inr (Or.inl hLL4X.1), hLL2⟩))
      · rcases hleft_tail_restart_prev_shape0 hLL2S.2 with hLL4 | hLL2
        · exact Or.inr (Or.inl ⟨Or.inr (Or.inr (Or.inl hLL2S.1)), hLL4⟩)
        · exact Or.inr (Or.inr (Or.inl ⟨Or.inr (Or.inr (Or.inl hLL2S.1)), hLL2⟩))
      · rcases hleft_tail_restart_prev_shape0 hLL2X.2 with hLL4 | hLL2
        · exact Or.inr (Or.inl ⟨Or.inr (Or.inr (Or.inr hLL2X.1)), hLL4⟩)
        · exact Or.inr (Or.inr (Or.inl ⟨Or.inr (Or.inr (Or.inr hLL2X.1)), hLL2⟩))
      · rcases hright_tail_restart_prev_shape0 hRL2X.2 with hRL2 | hRR4
        · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨Or.inl hRL2X.1, hRL2⟩)))
        · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨Or.inl hRL2X.1, hRR4⟩)))
      · rcases hright_tail_restart_prev_shape0 hRL2S.2 with hRL2 | hRR4
        · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨Or.inr (Or.inl hRL2S.1), hRL2⟩)))
        · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨Or.inr (Or.inl hRL2S.1), hRR4⟩)))
      · rcases hright_tail_restart_prev_shape0 hRR4X.2 with hRL2 | hRR4
        · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨Or.inr (Or.inr (Or.inl hRR4X.1)), hRL2⟩)))
        · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨Or.inr (Or.inr (Or.inl hRR4X.1)), hRR4⟩)))
      · rcases hright_tail_restart_prev_shape0 hRR4S.2 with hRL2 | hRR4
        · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨Or.inr (Or.inr (Or.inr hRR4S.1)), hRL2⟩)))
        · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨Or.inr (Or.inr (Or.inr hRR4S.1)), hRR4⟩)))
    have hresidue_started_prefix_restart_prev_split :
          (k_out.val + 1 = gc.configs.length) ∨
          LeftStartedFromLeft4Residue ∨
          LeftStartedFromLeft2Residue ∨
          RightStartedFromLeft2Residue ∨
          RightStartedFromRight4Residue := by
      rcases hresidue_started_prefix_restart_prev_grouped_split with hk_last | hLL4 | hLL2 | hRL2 | hRR4
      · exact Or.inl hk_last
      · exact Or.inr (Or.inl hLL4.2)
      · exact Or.inr (Or.inr (Or.inl hLL2.2))
      · exact Or.inr (Or.inr (Or.inr (Or.inl hRL2.2)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr hRR4.2)))
    let LeftOneSidedRestartResidue : Prop :=
        LeftOneSidedResidue ∧ LeftKoutStartedResidue
    let RightOneSidedRestartResidue : Prop :=
        RightOneSidedResidue ∧ RightKoutStartedResidue
    have hresidue_started_prefix_restart_one_sided :
          (k_out.val + 1 = gc.configs.length) ∨
          LeftOneSidedRestartResidue ∨
          RightOneSidedRestartResidue := by
      rcases hresidue_started_prefix_restart_prev_split with hk_last | hLL4 | hLL2 | hRL2 | hRR4
      · exact Or.inl hk_last
      · exact Or.inr (Or.inl ⟨hleft_prev_to_one_sided (Or.inl hLL4.1), hLL4.2⟩)
      · exact Or.inr (Or.inl ⟨hleft_prev_to_one_sided (Or.inr hLL2.1), hLL2.2⟩)
      · exact Or.inr (Or.inr ⟨hright_prev_to_one_sided (Or.inl hRL2.1), hRL2.2⟩)
      · exact Or.inr (Or.inr ⟨hright_prev_to_one_sided (Or.inr hRR4.1), hRR4.2⟩)
    let LeftKoutOneSidedRestartResidue : Prop :=
        LeftKoutOneSidedResidue ∧ LeftKoutStartedResidue
    let RightKoutOneSidedRestartResidue : Prop :=
        RightKoutOneSidedResidue ∧ RightKoutStartedResidue
    have hresidue_started_prefix_restart_kout_one_sided :
          (k_out.val + 1 = gc.configs.length) ∨
          LeftKoutOneSidedRestartResidue ∨
          RightKoutOneSidedRestartResidue := by
      rcases hresidue_started_prefix_restart_one_sided with hk_last | hleft | hright
      · exact Or.inl hk_last
      · exact Or.inr (Or.inl ⟨hleft_one_sided_to_kout hleft.1, hleft.2⟩)
      · exact Or.inr (Or.inr ⟨hright_one_sided_to_kout hright.1, hright.2⟩)
    let LeftKoutPureRestartResidue : Prop :=
        LeftKoutPureResidue ∧ LeftKoutStartedResidue
    let RightKoutPureRestartResidue : Prop :=
        RightKoutPureResidue ∧ RightKoutStartedResidue
    have hresidue_started_prefix_restart_kout_pure :
          (k_out.val + 1 = gc.configs.length) ∨
          LeftKoutPureRestartResidue ∨
          RightKoutPureRestartResidue := by
      rcases hresidue_started_prefix_restart_kout_one_sided with hk_last | hleft | hright
      · exact Or.inl hk_last
      · exact Or.inr (Or.inl ⟨hleft_kout_one_sided_pure hleft.1, hleft.2⟩)
      · exact Or.inr (Or.inr ⟨hright_kout_one_sided_pure hright.1, hright.2⟩)
    have hresidue_started_prefix_restart_kout_started :
          (k_out.val + 1 = gc.configs.length) ∨ LeftKoutStartedResidue ∨ RightKoutStartedResidue := by
      rcases hresidue_started_prefix_restart_kout_pure with hk_last | hleft | hright
      · exact Or.inl hk_last
      · exact Or.inr (Or.inl hleft.2)
      · exact Or.inr (Or.inr hright.2)
    let LeftStartedPrefixExactOneSidedRestartResidue : Prop :=
        LeftStartedPrefixExactResidue ∧ LeftOneSidedResidue
    let RightStartedPrefixExactOneSidedRestartResidue : Prop :=
        RightStartedPrefixExactResidue ∧ RightOneSidedResidue
    have hresidue_started_prefix_restart_one_sided_grouped :
          (k_out.val + 1 = gc.configs.length) ∨
          LeftStartedPrefixExactOneSidedRestartResidue ∨
          RightStartedPrefixExactOneSidedRestartResidue := by
      rcases hresidue_started_prefix_restart_prev_grouped_split with hk_last | hLL4 | hLL2 | hRL2 | hRR4
      · exact Or.inl hk_last
      · exact Or.inr (Or.inl ⟨hLL4.1, hleft_prev_to_one_sided (Or.inl hLL4.2.1)⟩)
      · exact Or.inr (Or.inl ⟨hLL2.1, hleft_prev_to_one_sided (Or.inr hLL2.2.1)⟩)
      · exact Or.inr (Or.inr ⟨hRL2.1, hright_prev_to_one_sided (Or.inl hRL2.2.1)⟩)
      · exact Or.inr (Or.inr ⟨hRR4.1, hright_prev_to_one_sided (Or.inr hRR4.2.1)⟩)
    let LeftStartedPrefixExactKoutOneSidedRestartResidue : Prop :=
        LeftStartedPrefixExactResidue ∧ LeftKoutOneSidedResidue
    let RightStartedPrefixExactKoutOneSidedRestartResidue : Prop :=
        RightStartedPrefixExactResidue ∧ RightKoutOneSidedResidue
    have hresidue_started_prefix_restart_kout_one_sided_grouped :
          (k_out.val + 1 = gc.configs.length) ∨
          LeftStartedPrefixExactKoutOneSidedRestartResidue ∨
          RightStartedPrefixExactKoutOneSidedRestartResidue := by
      rcases hresidue_started_prefix_restart_one_sided_grouped with hk_last | hleft | hright
      · exact Or.inl hk_last
      · exact Or.inr (Or.inl ⟨hleft.1, hleft_one_sided_to_kout hleft.2⟩)
      · exact Or.inr (Or.inr ⟨hright.1, hright_one_sided_to_kout hright.2⟩)
    let LeftStartedPrefixExactKoutPureRestartResidue : Prop :=
        LeftStartedPrefixExactResidue ∧ LeftKoutPureResidue
    let RightStartedPrefixExactKoutPureRestartResidue : Prop :=
        RightStartedPrefixExactResidue ∧ RightKoutPureResidue
    have hresidue_started_prefix_restart_kout_pure_grouped :
          (k_out.val + 1 = gc.configs.length) ∨
          LeftStartedPrefixExactKoutPureRestartResidue ∨
          RightStartedPrefixExactKoutPureRestartResidue := by
      rcases hresidue_started_prefix_restart_kout_one_sided_grouped with hk_last | hleft | hright
      · exact Or.inl hk_last
      · exact Or.inr (Or.inl ⟨hleft.1, hleft_kout_one_sided_pure hleft.2⟩)
      · exact Or.inr (Or.inr ⟨hright.1, hright_kout_one_sided_pure hright.2⟩)
    let LeftStartedPrefixExactKoutStartedRestartResidue : Prop :=
        LeftStartedPrefixExactResidue ∧ LeftKoutStartedResidue
    let RightStartedPrefixExactKoutStartedRestartResidue : Prop :=
        RightStartedPrefixExactResidue ∧ RightKoutStartedResidue
    have hresidue_started_prefix_restart_kout_started_grouped :
          (k_out.val + 1 = gc.configs.length) ∨
          LeftStartedPrefixExactKoutStartedRestartResidue ∨
          RightStartedPrefixExactKoutStartedRestartResidue := by
      rcases hresidue_started_prefix_restart_kout_pure_grouped with hk_last | hleft | hright
      · exact Or.inl hk_last
      · exact Or.inr (Or.inl ⟨hleft.1, hleft_kout_pure_started hleft.2⟩)
      · exact Or.inr (Or.inr ⟨hright.1, hright_kout_pure_started hright.2⟩)
    have hresidue_started_prefix_restart_exact_split_grouped :
          (k_out.val + 1 = gc.configs.length) ∨
          LeftStartedFromLeft4PrefixSameRestartResidue ∨
          LeftStartedFromLeft4PrefixCrossRestartResidue ∨
          LeftStartedFromLeft2PrefixSameRestartResidue ∨
          LeftStartedFromLeft2PrefixCrossRestartResidue ∨
          RightStartedFromLeft2PrefixCrossRestartResidue ∨
          RightStartedFromLeft2PrefixSameRestartResidue ∨
          RightStartedFromRight4PrefixCrossRestartResidue ∨
          RightStartedFromRight4PrefixSameRestartResidue := by
      rcases hresidue_started_prefix_restart_kout_started_grouped with hk_last | hleft | hright
      · exact Or.inl hk_last
      · rcases hleft with ⟨hprefix, hstart⟩
        rcases hprefix with hLL4S | hLL4X | hLL2S | hLL2X
        · exact Or.inr <| Or.inl <| ⟨hLL4S, hstart⟩
        · exact Or.inr <| Or.inr <| Or.inl <| ⟨hLL4X, hstart⟩
        · exact Or.inr <| Or.inr <| Or.inr <| Or.inl <| ⟨hLL2S, hstart⟩
        · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl <| ⟨hLL2X, hstart⟩
      · rcases hright with ⟨hprefix, hstart⟩
        rcases hprefix with hRL2X | hRL2S | hRR4X | hRR4S
        · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl <| ⟨hRL2X, hstart⟩
        · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl <| ⟨hRL2S, hstart⟩
        · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl <| ⟨hRR4X, hstart⟩
        · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| ⟨hRR4S, hstart⟩
    have hresidue_started_prefix_restart_tail_exact_split_grouped3 :
          (k_out.val + 1 = gc.configs.length) ∨
          LeftStartedFromLeft4PrefixSameTailRestartResidue ∨
          LeftStartedFromLeft4PrefixCrossTailRestartResidue ∨
          LeftStartedFromLeft2PrefixSameTailRestartResidue ∨
          LeftStartedFromLeft2PrefixCrossTailRestartResidue ∨
          RightStartedFromLeft2PrefixCrossTailRestartResidue ∨
          RightStartedFromLeft2PrefixSameTailRestartResidue ∨
          RightStartedFromRight4PrefixCrossTailRestartResidue ∨
          RightStartedFromRight4PrefixSameTailRestartResidue := by
      exact nine_way_transport
        hresidue_started_prefix_restart_exact_split_grouped
        (fun hLL4S => by
          exact ⟨hLL4S.1, ⟨hleft_same_tail (hleft_started_prefix_same_final hLL4S.1.2), hLL4S.2⟩⟩)
        (fun hLL4X => by
          exact ⟨hLL4X.1, ⟨hleft_cross_tail (hleft_started_prefix_cross_final hLL4X.1.2), hLL4X.2⟩⟩)
        (fun hLL2S => by
          exact ⟨hLL2S.1, ⟨hleft_same_tail (hleft_started_prefix_same_final hLL2S.1.2), hLL2S.2⟩⟩)
        (fun hLL2X => by
          exact ⟨hLL2X.1, ⟨hleft_cross_tail (hleft_started_prefix_cross_final hLL2X.1.2), hLL2X.2⟩⟩)
        (fun hRL2X => by
          exact ⟨hRL2X.1, ⟨hright_cross_tail (hright_started_prefix_cross_final hRL2X.1.2), hRL2X.2⟩⟩)
        (fun hRL2S => by
          exact ⟨hRL2S.1, ⟨hright_same_tail (hright_started_prefix_same_final hRL2S.1.2), hRL2S.2⟩⟩)
        (fun hRR4X => by
          exact ⟨hRR4X.1, ⟨hright_cross_tail (hright_started_prefix_cross_final hRR4X.1.2), hRR4X.2⟩⟩)
        (fun hRR4S => by
          exact ⟨hRR4S.1, ⟨hright_same_tail (hright_started_prefix_same_final hRR4S.1.2), hRR4S.2⟩⟩)
    have hresidue_started_prefix_restart_prev_grouped_split3 :
          (k_out.val + 1 = gc.configs.length) ∨
          (LeftStartedPrefixExactResidue ∧ LeftStartedFromLeft4Residue) ∨
          (LeftStartedPrefixExactResidue ∧ LeftStartedFromLeft2Residue) ∨
          (RightStartedPrefixExactResidue ∧ RightStartedFromLeft2Residue) ∨
          (RightStartedPrefixExactResidue ∧ RightStartedFromRight4Residue) := by
      rcases hresidue_started_prefix_restart_tail_exact_split_grouped3 with
        hk_last | hLL4S | hLL4X | hLL2S | hLL2X | hRL2X | hRL2S | hRR4X | hRR4S
      · exact Or.inl hk_last
      · rcases hleft_tail_restart_prev_shape0 hLL4S.2 with hLL4 | hLL2
        · exact Or.inr (Or.inl ⟨Or.inl hLL4S.1, hLL4⟩)
        · exact Or.inr (Or.inr (Or.inl ⟨Or.inl hLL4S.1, hLL2⟩))
      · rcases hleft_tail_restart_prev_shape0 hLL4X.2 with hLL4 | hLL2
        · exact Or.inr (Or.inl ⟨Or.inr (Or.inl hLL4X.1), hLL4⟩)
        · exact Or.inr (Or.inr (Or.inl ⟨Or.inr (Or.inl hLL4X.1), hLL2⟩))
      · rcases hleft_tail_restart_prev_shape0 hLL2S.2 with hLL4 | hLL2
        · exact Or.inr (Or.inl ⟨Or.inr (Or.inr (Or.inl hLL2S.1)), hLL4⟩)
        · exact Or.inr (Or.inr (Or.inl ⟨Or.inr (Or.inr (Or.inl hLL2S.1)), hLL2⟩))
      · rcases hleft_tail_restart_prev_shape0 hLL2X.2 with hLL4 | hLL2
        · exact Or.inr (Or.inl ⟨Or.inr (Or.inr (Or.inr hLL2X.1)), hLL4⟩)
        · exact Or.inr (Or.inr (Or.inl ⟨Or.inr (Or.inr (Or.inr hLL2X.1)), hLL2⟩))
      · rcases hright_tail_restart_prev_shape0 hRL2X.2 with hRL2 | hRR4
        · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨Or.inl hRL2X.1, hRL2⟩)))
        · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨Or.inl hRL2X.1, hRR4⟩)))
      · rcases hright_tail_restart_prev_shape0 hRL2S.2 with hRL2 | hRR4
        · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨Or.inr (Or.inl hRL2S.1), hRL2⟩)))
        · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨Or.inr (Or.inl hRL2S.1), hRR4⟩)))
      · rcases hright_tail_restart_prev_shape0 hRR4X.2 with hRL2 | hRR4
        · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨Or.inr (Or.inr (Or.inl hRR4X.1)), hRL2⟩)))
        · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨Or.inr (Or.inr (Or.inl hRR4X.1)), hRR4⟩)))
      · rcases hright_tail_restart_prev_shape0 hRR4S.2 with hRL2 | hRR4
        · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨Or.inr (Or.inr (Or.inr hRR4S.1)), hRL2⟩)))
        · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨Or.inr (Or.inr (Or.inr hRR4S.1)), hRR4⟩)))
    have hleft_LL4_grouped3_to_one_sided :
          (LeftStartedPrefixExactResidue ∧ LeftStartedFromLeft4Residue) →
          LeftStartedPrefixExactOneSidedRestartResidue := by
      intro hLL4
      exact ⟨hLL4.1, hleft_prev_to_one_sided (Or.inl hLL4.2.1)⟩
    have hleft_LL2_grouped3_to_one_sided :
          (LeftStartedPrefixExactResidue ∧ LeftStartedFromLeft2Residue) →
          LeftStartedPrefixExactOneSidedRestartResidue := by
      intro hLL2
      exact ⟨hLL2.1, hleft_prev_to_one_sided (Or.inr hLL2.2.1)⟩
    have hright_RL2_grouped3_to_one_sided :
          (RightStartedPrefixExactResidue ∧ RightStartedFromLeft2Residue) →
          RightStartedPrefixExactOneSidedRestartResidue := by
      intro hRL2
      exact ⟨hRL2.1, hright_prev_to_one_sided (Or.inl hRL2.2.1)⟩
    have hright_RR4_grouped3_to_one_sided :
          (RightStartedPrefixExactResidue ∧ RightStartedFromRight4Residue) →
          RightStartedPrefixExactOneSidedRestartResidue := by
      intro hRR4
      exact ⟨hRR4.1, hright_prev_to_one_sided (Or.inr hRR4.2.1)⟩
    have hleft_LL4_grouped3_to_kout_started :
          (LeftStartedPrefixExactResidue ∧ LeftStartedFromLeft4Residue) →
          LeftStartedPrefixExactKoutStartedRestartResidue := by
      intro hLL4
      have hone := hleft_LL4_grouped3_to_one_sided hLL4
      have hkout := hleft_one_sided_to_kout hone.2
      have hpure := hleft_kout_one_sided_pure hkout
      exact ⟨hone.1, hleft_kout_pure_started hpure⟩
    have hleft_LL2_grouped3_to_kout_started :
          (LeftStartedPrefixExactResidue ∧ LeftStartedFromLeft2Residue) →
          LeftStartedPrefixExactKoutStartedRestartResidue := by
      intro hLL2
      have hone := hleft_LL2_grouped3_to_one_sided hLL2
      have hkout := hleft_one_sided_to_kout hone.2
      have hpure := hleft_kout_one_sided_pure hkout
      exact ⟨hone.1, hleft_kout_pure_started hpure⟩
    have hright_RL2_grouped3_to_kout_started :
          (RightStartedPrefixExactResidue ∧ RightStartedFromLeft2Residue) →
          RightStartedPrefixExactKoutStartedRestartResidue := by
      intro hRL2
      have hone := hright_RL2_grouped3_to_one_sided hRL2
      have hkout := hright_one_sided_to_kout hone.2
      have hpure := hright_kout_one_sided_pure hkout
      exact ⟨hone.1, hright_kout_pure_started hpure⟩
    have hright_RR4_grouped3_to_kout_started :
          (RightStartedPrefixExactResidue ∧ RightStartedFromRight4Residue) →
          RightStartedPrefixExactKoutStartedRestartResidue := by
      intro hRR4
      have hone := hright_RR4_grouped3_to_one_sided hRR4
      have hkout := hright_one_sided_to_kout hone.2
      have hpure := hright_kout_one_sided_pure hkout
      exact ⟨hone.1, hright_kout_pure_started hpure⟩
    have hresidue_started_prefix_restart_kout_started_grouped3_simple :
          (k_out.val + 1 = gc.configs.length) ∨
          LeftStartedPrefixExactKoutStartedRestartResidue ∨
          RightStartedPrefixExactKoutStartedRestartResidue :=
      five_way_restart_transport
        hresidue_started_prefix_restart_prev_grouped_split3
        hleft_LL4_grouped3_to_kout_started
        hleft_LL2_grouped3_to_kout_started
        hright_RL2_grouped3_to_kout_started
        hright_RR4_grouped3_to_kout_started
    have hLL4S_grouped4_to_tail :
          LeftStartedFromLeft4PrefixSameRestartResidue →
          LeftStartedFromLeft4PrefixSameTailRestartResidue := by
      intro hLL4S
      exact ⟨hLL4S.1, ⟨hleft_same_tail (hleft_started_prefix_same_final hLL4S.1.2), hLL4S.2⟩⟩
    have hLL4X_grouped4_to_tail :
          LeftStartedFromLeft4PrefixCrossRestartResidue →
          LeftStartedFromLeft4PrefixCrossTailRestartResidue := by
      intro hLL4X
      exact ⟨hLL4X.1, ⟨hleft_cross_tail (hleft_started_prefix_cross_final hLL4X.1.2), hLL4X.2⟩⟩
    have hLL2S_grouped4_to_tail :
          LeftStartedFromLeft2PrefixSameRestartResidue →
          LeftStartedFromLeft2PrefixSameTailRestartResidue := by
      intro hLL2S
      exact ⟨hLL2S.1, ⟨hleft_same_tail (hleft_started_prefix_same_final hLL2S.1.2), hLL2S.2⟩⟩
    have hLL2X_grouped4_to_tail :
          LeftStartedFromLeft2PrefixCrossRestartResidue →
          LeftStartedFromLeft2PrefixCrossTailRestartResidue := by
      intro hLL2X
      exact ⟨hLL2X.1, ⟨hleft_cross_tail (hleft_started_prefix_cross_final hLL2X.1.2), hLL2X.2⟩⟩
    have hRL2X_grouped4_to_tail :
          RightStartedFromLeft2PrefixCrossRestartResidue →
          RightStartedFromLeft2PrefixCrossTailRestartResidue := by
      intro hRL2X
      exact ⟨hRL2X.1, ⟨hright_cross_tail (hright_started_prefix_cross_final hRL2X.1.2), hRL2X.2⟩⟩
    have hRL2S_grouped4_to_tail :
          RightStartedFromLeft2PrefixSameRestartResidue →
          RightStartedFromLeft2PrefixSameTailRestartResidue := by
      intro hRL2S
      exact ⟨hRL2S.1, ⟨hright_same_tail (hright_started_prefix_same_final hRL2S.1.2), hRL2S.2⟩⟩
    have hRR4X_grouped4_to_tail :
          RightStartedFromRight4PrefixCrossRestartResidue →
          RightStartedFromRight4PrefixCrossTailRestartResidue := by
      intro hRR4X
      exact ⟨hRR4X.1, ⟨hright_cross_tail (hright_started_prefix_cross_final hRR4X.1.2), hRR4X.2⟩⟩
    have hRR4S_grouped4_to_tail :
          RightStartedFromRight4PrefixSameRestartResidue →
          RightStartedFromRight4PrefixSameTailRestartResidue := by
      intro hRR4S
      exact ⟨hRR4S.1, ⟨hright_same_tail (hright_started_prefix_same_final hRR4S.1.2), hRR4S.2⟩⟩
    have hLL4S_grouped4_to_prev :
          LeftStartedFromLeft4PrefixSameTailRestartResidue →
          (LeftStartedPrefixExactResidue ∧ LeftStartedFromLeft4Residue) ∨
          (LeftStartedPrefixExactResidue ∧ LeftStartedFromLeft2Residue) := by
      exact tagged_two_way_transport Or.inl hleft_tail_restart_prev_shape0
    have hLL4X_grouped4_to_prev :
          LeftStartedFromLeft4PrefixCrossTailRestartResidue →
          (LeftStartedPrefixExactResidue ∧ LeftStartedFromLeft4Residue) ∨
          (LeftStartedPrefixExactResidue ∧ LeftStartedFromLeft2Residue) := by
      exact tagged_two_way_transport (fun h => Or.inr <| Or.inl h) hleft_tail_restart_prev_shape0
    have hLL2S_grouped4_to_prev :
          LeftStartedFromLeft2PrefixSameTailRestartResidue →
          (LeftStartedPrefixExactResidue ∧ LeftStartedFromLeft4Residue) ∨
          (LeftStartedPrefixExactResidue ∧ LeftStartedFromLeft2Residue) := by
      exact tagged_two_way_transport (fun h => Or.inr <| Or.inr <| Or.inl h) hleft_tail_restart_prev_shape0
    have hLL2X_grouped4_to_prev :
          LeftStartedFromLeft2PrefixCrossTailRestartResidue →
          (LeftStartedPrefixExactResidue ∧ LeftStartedFromLeft4Residue) ∨
          (LeftStartedPrefixExactResidue ∧ LeftStartedFromLeft2Residue) := by
      exact tagged_two_way_transport (fun h => Or.inr <| Or.inr <| Or.inr h) hleft_tail_restart_prev_shape0
    have hRL2X_grouped4_to_prev :
          RightStartedFromLeft2PrefixCrossTailRestartResidue →
          (RightStartedPrefixExactResidue ∧ RightStartedFromLeft2Residue) ∨
          (RightStartedPrefixExactResidue ∧ RightStartedFromRight4Residue) := by
      exact tagged_two_way_transport Or.inl hright_tail_restart_prev_shape0
    have hRL2S_grouped4_to_prev :
          RightStartedFromLeft2PrefixSameTailRestartResidue →
          (RightStartedPrefixExactResidue ∧ RightStartedFromLeft2Residue) ∨
          (RightStartedPrefixExactResidue ∧ RightStartedFromRight4Residue) := by
      exact tagged_two_way_transport (fun h => Or.inr <| Or.inl h) hright_tail_restart_prev_shape0
    have hRR4X_grouped4_to_prev :
          RightStartedFromRight4PrefixCrossTailRestartResidue →
          (RightStartedPrefixExactResidue ∧ RightStartedFromLeft2Residue) ∨
          (RightStartedPrefixExactResidue ∧ RightStartedFromRight4Residue) := by
      exact tagged_two_way_transport (fun h => Or.inr <| Or.inr <| Or.inl h) hright_tail_restart_prev_shape0
    have hRR4S_grouped4_to_prev :
          RightStartedFromRight4PrefixSameTailRestartResidue →
          (RightStartedPrefixExactResidue ∧ RightStartedFromLeft2Residue) ∨
          (RightStartedPrefixExactResidue ∧ RightStartedFromRight4Residue) := by
      exact tagged_two_way_transport (fun h => Or.inr <| Or.inr <| Or.inr h) hright_tail_restart_prev_shape0
    have hresidue_started_prefix_restart_kout_started_grouped4_simple :
          (k_out.val + 1 = gc.configs.length) ∨
          LeftStartedPrefixExactKoutStartedRestartResidue ∨
          RightStartedPrefixExactKoutStartedRestartResidue := by
      exact restart_kout_started_cycle_transport
        hresidue_started_prefix_restart_kout_started_grouped3_simple
        (fun hprefix => hprefix)
        (fun hprefix => hprefix)
        hLL4S_grouped4_to_tail
        hLL4X_grouped4_to_tail
        hLL2S_grouped4_to_tail
        hLL2X_grouped4_to_tail
        hRL2X_grouped4_to_tail
        hRL2S_grouped4_to_tail
        hRR4X_grouped4_to_tail
        hRR4S_grouped4_to_tail
        hLL4S_grouped4_to_prev
        hLL4X_grouped4_to_prev
        hLL2S_grouped4_to_prev
        hLL2X_grouped4_to_prev
        hRL2X_grouped4_to_prev
        hRL2S_grouped4_to_prev
        hRR4X_grouped4_to_prev
        hRR4S_grouped4_to_prev
        hleft_LL4_grouped3_to_kout_started
        hleft_LL2_grouped3_to_kout_started
        hright_RL2_grouped3_to_kout_started
        hright_RR4_grouped3_to_kout_started
    have hresidue_started_prefix_restart_kout_started_grouped14_simple :
          (k_out.val + 1 = gc.configs.length) ∨
          LeftStartedPrefixExactKoutStartedRestartResidue ∨
          RightStartedPrefixExactKoutStartedRestartResidue := by
      exact restart_kout_started_cycle_transport10
        hresidue_started_prefix_restart_kout_started_grouped4_simple
        (fun hprefix => hprefix)
        (fun hprefix => hprefix)
        hLL4S_grouped4_to_tail
        hLL4X_grouped4_to_tail
        hLL2S_grouped4_to_tail
        hLL2X_grouped4_to_tail
        hRL2X_grouped4_to_tail
        hRL2S_grouped4_to_tail
        hRR4X_grouped4_to_tail
        hRR4S_grouped4_to_tail
        hLL4S_grouped4_to_prev
        hLL4X_grouped4_to_prev
        hLL2S_grouped4_to_prev
        hLL2X_grouped4_to_prev
        hRL2X_grouped4_to_prev
        hRL2S_grouped4_to_prev
        hRR4X_grouped4_to_prev
        hRR4S_grouped4_to_prev
        hleft_LL4_grouped3_to_kout_started
        hleft_LL2_grouped3_to_kout_started
        hright_RL2_grouped3_to_kout_started
        hright_RR4_grouped3_to_kout_started
    have hresidue_started_prefix_restart_kout_started_grouped24_simple :
          (k_out.val + 1 = gc.configs.length) ∨
          LeftStartedPrefixExactKoutStartedRestartResidue ∨
          RightStartedPrefixExactKoutStartedRestartResidue := by
      exact restart_kout_started_cycle_transport10
        hresidue_started_prefix_restart_kout_started_grouped14_simple
        (fun hprefix => hprefix)
        (fun hprefix => hprefix)
        hLL4S_grouped4_to_tail
        hLL4X_grouped4_to_tail
        hLL2S_grouped4_to_tail
        hLL2X_grouped4_to_tail
        hRL2X_grouped4_to_tail
        hRL2S_grouped4_to_tail
        hRR4X_grouped4_to_tail
        hRR4S_grouped4_to_tail
        hLL4S_grouped4_to_prev
        hLL4X_grouped4_to_prev
        hLL2S_grouped4_to_prev
        hLL2X_grouped4_to_prev
        hRL2X_grouped4_to_prev
        hRL2S_grouped4_to_prev
        hRR4X_grouped4_to_prev
        hRR4S_grouped4_to_prev
        hleft_LL4_grouped3_to_kout_started
        hleft_LL2_grouped3_to_kout_started
        hright_RL2_grouped3_to_kout_started
        hright_RR4_grouped3_to_kout_started
    have hresidue_started_prefix_restart_kout_started_grouped34_simple :
          (k_out.val + 1 = gc.configs.length) ∨
          LeftStartedPrefixExactKoutStartedRestartResidue ∨
          RightStartedPrefixExactKoutStartedRestartResidue := by
      exact restart_kout_started_cycle_transport10
        hresidue_started_prefix_restart_kout_started_grouped24_simple
        (fun hprefix => hprefix)
        (fun hprefix => hprefix)
        hLL4S_grouped4_to_tail
        hLL4X_grouped4_to_tail
        hLL2S_grouped4_to_tail
        hLL2X_grouped4_to_tail
        hRL2X_grouped4_to_tail
        hRL2S_grouped4_to_tail
        hRR4X_grouped4_to_tail
        hRR4S_grouped4_to_tail
        hLL4S_grouped4_to_prev
        hLL4X_grouped4_to_prev
        hLL2S_grouped4_to_prev
        hLL2X_grouped4_to_prev
        hRL2X_grouped4_to_prev
        hRL2S_grouped4_to_prev
        hRR4X_grouped4_to_prev
        hRR4S_grouped4_to_prev
        hleft_LL4_grouped3_to_kout_started
        hleft_LL2_grouped3_to_kout_started
        hright_RL2_grouped3_to_kout_started
        hright_RR4_grouped3_to_kout_started
    have hresidue_started_prefix_restart_kout_started_grouped44_simple :
          (k_out.val + 1 = gc.configs.length) ∨
          LeftStartedPrefixExactKoutStartedRestartResidue ∨
          RightStartedPrefixExactKoutStartedRestartResidue := by
      exact restart_kout_started_cycle_transport10
        hresidue_started_prefix_restart_kout_started_grouped34_simple
        (fun hprefix => hprefix)
        (fun hprefix => hprefix)
        hLL4S_grouped4_to_tail
        hLL4X_grouped4_to_tail
        hLL2S_grouped4_to_tail
        hLL2X_grouped4_to_tail
        hRL2X_grouped4_to_tail
        hRL2S_grouped4_to_tail
        hRR4X_grouped4_to_tail
        hRR4S_grouped4_to_tail
        hLL4S_grouped4_to_prev
        hLL4X_grouped4_to_prev
        hLL2S_grouped4_to_prev
        hLL2X_grouped4_to_prev
        hRL2X_grouped4_to_prev
        hRL2S_grouped4_to_prev
        hRR4X_grouped4_to_prev
        hRR4S_grouped4_to_prev
        hleft_LL4_grouped3_to_kout_started
        hleft_LL2_grouped3_to_kout_started
        hright_RL2_grouped3_to_kout_started
        hright_RR4_grouped3_to_kout_started
    have left4_ne_left3 :
        left (left (left (left t))) ≠ left (left (left t)) := by
      intro hEq
      have hleft_eq_self : left t = t := by
        have hleft3_eq_left2 : left (left (left t)) = left (left t) := by
          simpa [right_left_eq_self] using congrArg right hEq
        have hleft2_eq_left : left (left t) = left t := by
          simpa [right_left_eq_self] using congrArg right hleft3_eq_left2
        simpa [right_left_eq_self] using congrArg right hleft2_eq_left
      have hself_eq_right : t = right t := by
        simpa [right_left_eq_self] using congrArg right hleft_eq_self
      exact left_ne_right (by omega) t (hleft_eq_self.trans hself_eq_right)
    have left4_ne_self :
        left (left (left (left t))) ≠ t := by
      intro hEq
      have hleft3_eq_right : left (left (left t)) = right t := by
        simpa [right_left_eq_self] using congrArg right hEq
      exact left3_not_local5 (by omega) t (Or.inr (Or.inr (Or.inl hleft3_eq_right)))
    have left4_ne_left2 :
        left (left (left (left t))) ≠ left (left t) := by
      intro hEq
      exact left4_not_local5 (by omega) t (Or.inl hEq)
    have right4_ne_left3 :
        right (right (right (right t))) ≠ left (left (left t)) := by
      set_option maxHeartbeats 1000000 in
      intro hEq
      let myShift : Fin sys.rs.n → Nat := fun q => (q.val + sys.rs.n - t.val) % sys.rs.n
      have hright4_shift : myShift (right (right (right (right t)))) = 4 := by
        simp [myShift, right]
        by_cases hwrap : t.val + 4 < sys.rs.n
        · rw [Nat.mod_eq_of_lt hwrap]
          have hEq' : t.val + 4 + sys.rs.n - t.val = sys.rs.n + 4 := by omega
          rw [hEq', show sys.rs.n + 4 = 4 + sys.rs.n by omega,
            Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
        · have hge : sys.rs.n ≤ t.val + 4 := by omega
          have hsublt : t.val + 4 - sys.rs.n < sys.rs.n := by omega
          have hsum : t.val + 1 + 1 + 1 + 1 = (t.val + 4 - sys.rs.n) + sys.rs.n := by
            calc
              t.val + 1 + 1 + 1 + 1 = t.val + 4 := by omega
              _ = (t.val + 4 - sys.rs.n) + sys.rs.n := by
                simpa using (Nat.sub_add_cancel hge).symm
          rw [hsum, Nat.add_mod_right, Nat.mod_eq_of_lt hsublt]
          have hEq' : (t.val + 4 - sys.rs.n) + sys.rs.n - t.val = 4 := by omega
          rw [hEq', Nat.mod_eq_of_lt (by omega)]
      have hleft3_shift : myShift (left (left (left t))) = sys.rs.n - 3 := by
        have hcases : t.val = 0 ∨ t.val = 1 ∨ t.val = 2 ∨ 3 ≤ t.val := by omega
        rcases hcases with h0 | h1 | h2 | h3
        · simp [myShift, left, h0]
          have hstep1 : (sys.rs.n - 1 + sys.rs.n - 1) % sys.rs.n = sys.rs.n - 2 := by
            rw [show sys.rs.n - 1 + sys.rs.n - 1 = (sys.rs.n - 2) + sys.rs.n by omega,
              Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
          rw [hstep1]
          rw [show sys.rs.n - 2 + sys.rs.n - 1 = (sys.rs.n - 3) + sys.rs.n by omega,
            Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
        · simp [myShift, left, h1]
          have hstep1 : (sys.rs.n - 1 + sys.rs.n - 1) % sys.rs.n = sys.rs.n - 2 := by
            rw [show sys.rs.n - 1 + sys.rs.n - 1 = (sys.rs.n - 2) + sys.rs.n by omega,
              Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
          rw [hstep1]
          rw [show sys.rs.n - 2 + sys.rs.n - 1 = (sys.rs.n - 3) + sys.rs.n by omega,
            Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
        · simp [myShift, left, h2]
          have h1mod : 1 % sys.rs.n = 1 := Nat.mod_eq_of_lt (by omega)
          rw [h1mod]
          have hstep1 : (1 + sys.rs.n - 1) % sys.rs.n = 0 := by
            rw [show 1 + sys.rs.n - 1 = sys.rs.n by omega, Nat.mod_self]
          rw [hstep1]
          have hstep2 : (0 + sys.rs.n - 1) % sys.rs.n = sys.rs.n - 1 := by
            rw [Nat.zero_add, Nat.mod_eq_of_lt (by omega)]
          rw [hstep2]
          rw [show sys.rs.n - 1 + sys.rs.n - 2 = (sys.rs.n - 3) + sys.rs.n by omega,
            Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
        · simp [myShift]
          rw [show (t.val + sys.rs.n - 1) % sys.rs.n = t.val - 1 by
                rw [show t.val + sys.rs.n - 1 = (t.val - 1) + sys.rs.n by omega,
                  Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]]
          rw [show (t.val - 1 + sys.rs.n - 1) % sys.rs.n = t.val - 2 by
                rw [show t.val - 1 + sys.rs.n - 1 = (t.val - 2) + sys.rs.n by omega,
                  Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]]
          rw [show (t.val - 2 + sys.rs.n - 1) % sys.rs.n = t.val - 3 by
                rw [show t.val - 2 + sys.rs.n - 1 = (t.val - 3) + sys.rs.n by omega,
                  Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]]
          have hEq' : (t.val - 3) + sys.rs.n - t.val = sys.rs.n - 3 := by omega
          rw [hEq', Nat.mod_eq_of_lt (by omega)]
      have hshift_eq :
          ((right (right (right (right t)))).val + sys.rs.n - t.val) % sys.rs.n =
            ((left (left (left t))).val + sys.rs.n - t.val) % sys.rs.n := by
        simpa [myShift] using congrArg (fun q : Fin sys.rs.n => myShift q) hEq
      have hright4_shift' :
          ((right (right (right (right t)))).val + sys.rs.n - t.val) % sys.rs.n = 4 := by
        simpa [myShift] using hright4_shift
      have hleft3_shift' :
          ((left (left (left t))).val + sys.rs.n - t.val) % sys.rs.n = sys.rs.n - 3 := by
        simpa [myShift] using hleft3_shift
      rw [hright4_shift', hleft3_shift'] at hshift_eq
      omega
    have right4_ne_self :
        right (right (right (right t))) ≠ t := by
      intro hEq
      have hright3_eq_left : right (right (right t)) = left t := by
        simpa [left_right_eq_self] using congrArg left hEq
      exact right3_not_local5 (by omega) t (Or.inr (Or.inl hright3_eq_left))
    have right4_ne_right3 :
        right (right (right (right t))) ≠ right (right (right t)) := by
      set_option maxHeartbeats 1000000 in
      intro hEq
      have hright_eq_self : right t = t := by
        have hright3_eq_right2 : right (right (right t)) = right (right t) := by
          simpa [left_right_eq_self] using congrArg left hEq
        have hright2_eq_right : right (right t) = right t := by
          simpa [left_right_eq_self] using congrArg left hright3_eq_right2
        simpa [left_right_eq_self] using congrArg left hright2_eq_right
      have hself_eq_left : t = left t := by
        simpa [left_right_eq_self] using congrArg left hright_eq_self
      exact right_ne_left (by omega) t (hright_eq_self.trans hself_eq_left)
    have right4_not_leftsix :
        ¬(right (right (right (right t))) = left (left (left t)) ∨
          right (right (right (right t))) = left (left t) ∨
          right (right (right (right t))) = left t ∨
          right (right (right (right t))) = t ∨
          right (right (right (right t))) = right t ∨
          right (right (right (right t))) = right (right t)) := by
      intro h
      rcases h with h | h | h | h | h | h
      · exact right4_ne_left3 h
      · exact right4_not_local5 (by omega) t (Or.inl h)
      · exact right4_not_local5 (by omega) t (Or.inr (Or.inl h))
      · exact right4_ne_self h
      · exact right4_not_local5 (by omega) t (Or.inr (Or.inr (Or.inl h)))
      · exact right4_not_local5 (by omega) t (Or.inr (Or.inr (Or.inr h)))
    have hsame_prefix_not_left2_min :
        (LeftStartedFromLeft4PrefixSameResidue ∨ LeftStartedFromLeft2PrefixSameResidue) →
        ¬ LeftStartedFromLeft2MinRestartResidue := by
      intro hsame hmin
      rcases hsame with hLL4S | hLL2S
      · rcases hLL4S with
          ⟨_hprev, _hkout_left3, _k1, _hk1, _hk1_left2,
            j, j1, hj_lt, hj1, hj_left4, hj1_left3, hj_tail⟩
        rcases hmin with
          ⟨cut, prev, hsucc, hcut_le, hprev_left2, hcut_left3, hcut_tail, hcut_min, _hstart⟩
        have hj_lt_cut : j.val < cut.val := by
          by_contra hnot
          push_neg at hnot
          have hj_in := hcut_tail j hnot
          rcases hj_in with hj | hj | hj | hj | hj | hj
          · exact left4_ne_left3 (Eq.trans hj_left4.symm hj)
          · exact left4_not_local5 (by omega) t (Or.inl (Eq.trans hj_left4.symm hj))
          · exact left4_not_local5 (by omega) t (Or.inr (Or.inl (Eq.trans hj_left4.symm hj)))
          · exact left4_ne_self (Eq.trans hj_left4.symm hj)
          · exact left4_not_local5 (by omega) t (Or.inr (Or.inr (Or.inl (Eq.trans hj_left4.symm hj))))
          · exact left4_not_local5 (by omega) t (Or.inr (Or.inr (Or.inr (Eq.trans hj_left4.symm hj))))
        have hj1_le_cut : j1.val ≤ cut.val := by
          rw [hj1]
          omega
        have hj1_le_kout : j1.val ≤ k_out.val := by
          rw [hj1]
          omega
        have hj1_tail :
            ∀ k : Fin gc.configs.length,
              j1.val ≤ k.val →
              gc.moverAt k = left (left (left t)) ∨
                gc.moverAt k = left (left t) ∨
                gc.moverAt k = left t ∨
                gc.moverAt k = t ∨
                gc.moverAt k = right t ∨
                gc.moverAt k = right (right t) := by
          intro k hk_ge
          have hj_lt_k : j.val < k.val := by
            rw [hj1] at hk_ge
            omega
          exact hj_tail k hj_lt_k
        have hnot_lt : ¬ j1.val < cut.val := by
          intro hj1_lt_cut
          exact (hcut_min j1 hj1_lt_cut) ⟨hj1_le_kout, hj1_left3, hj1_tail⟩
        have hj1_eq_cut : j1 = cut := by
          apply Fin.ext
          exact Nat.le_antisymm hj1_le_cut (Nat.le_of_not_gt hnot_lt)
        have hprev_eq_j : prev = j := by
          apply Fin.ext
          have hcut_eq_j1 : cut.val = j1.val := by
            simpa using (congrArg Fin.val hj1_eq_cut).symm
          rw [hj1, ← hsucc] at hcut_eq_j1
          omega
        exact left4_ne_left2 (by
          calc
            left (left (left (left t))) = gc.moverAt j := hj_left4.symm
            _ = gc.moverAt prev := by rw [hprev_eq_j]
            _ = left (left t) := hprev_left2)
      · rcases hLL2S with
          ⟨_hprev, _hkout_left3, _k1, _hk1, _hk1_left2,
            j, j1, hj_lt, hj1, hj_left4, hj1_left3, hj_tail⟩
        rcases hmin with
          ⟨cut, prev, hsucc, hcut_le, hprev_left2, hcut_left3, hcut_tail, hcut_min, _hstart⟩
        have hj_lt_cut : j.val < cut.val := by
          by_contra hnot
          push_neg at hnot
          have hj_in := hcut_tail j hnot
          rcases hj_in with hj | hj | hj | hj | hj | hj
          · exact left4_ne_left3 (Eq.trans hj_left4.symm hj)
          · exact left4_not_local5 (by omega) t (Or.inl (Eq.trans hj_left4.symm hj))
          · exact left4_not_local5 (by omega) t (Or.inr (Or.inl (Eq.trans hj_left4.symm hj)))
          · exact left4_ne_self (Eq.trans hj_left4.symm hj)
          · exact left4_not_local5 (by omega) t (Or.inr (Or.inr (Or.inl (Eq.trans hj_left4.symm hj))))
          · exact left4_not_local5 (by omega) t (Or.inr (Or.inr (Or.inr (Eq.trans hj_left4.symm hj))))
        have hj1_le_cut : j1.val ≤ cut.val := by
          rw [hj1]
          omega
        have hj1_le_kout : j1.val ≤ k_out.val := by
          rw [hj1]
          omega
        have hj1_tail :
            ∀ k : Fin gc.configs.length,
              j1.val ≤ k.val →
              gc.moverAt k = left (left (left t)) ∨
                gc.moverAt k = left (left t) ∨
                gc.moverAt k = left t ∨
                gc.moverAt k = t ∨
                gc.moverAt k = right t ∨
                gc.moverAt k = right (right t) := by
          intro k hk_ge
          have hj_lt_k : j.val < k.val := by
            rw [hj1] at hk_ge
            omega
          exact hj_tail k hj_lt_k
        have hnot_lt : ¬ j1.val < cut.val := by
          intro hj1_lt_cut
          exact (hcut_min j1 hj1_lt_cut) ⟨hj1_le_kout, hj1_left3, hj1_tail⟩
        have hj1_eq_cut : j1 = cut := by
          apply Fin.ext
          exact Nat.le_antisymm hj1_le_cut (Nat.le_of_not_gt hnot_lt)
        have hprev_eq_j : prev = j := by
          apply Fin.ext
          have hcut_eq_j1 : cut.val = j1.val := by
            simpa using (congrArg Fin.val hj1_eq_cut).symm
          rw [hj1, ← hsucc] at hcut_eq_j1
          omega
        exact left4_ne_left2 (by
          calc
            left (left (left (left t))) = gc.moverAt j := hj_left4.symm
            _ = gc.moverAt prev := by rw [hprev_eq_j]
            _ = left (left t) := hprev_left2)
    have hcross_prefix_not_left4_min :
        (LeftStartedFromLeft4PrefixCrossResidue ∨ LeftStartedFromLeft2PrefixCrossResidue) →
        ¬ LeftStartedFromLeft4MinRestartResidue := by
      intro hcross hmin
      rcases hcross with hLL4X | hLL2X
      · rcases hLL4X with
          ⟨_hprev, _hkout_left3, _k1, _hk1, _hk1_left2,
            j, j1, hj_lt, hj1, hj_right3, hj1_right2, hj_tail⟩
        rcases hmin with
          ⟨cut, prev, hsucc, _hcut_le, hprev_left4, hcut_left3, hcut_tail, _hcut_min, _hstart⟩
        have hj_lt_cut : j.val < cut.val := by
          by_contra hnot
          push_neg at hnot
          have hj_in := hcut_tail j hnot
          rcases hj_in with hj | hj | hj | hj | hj | hj
          · exact right3_ne_left3 (by omega) t (Eq.trans hj_right3.symm hj)
          · exact right3_not_local5 (by omega) t (Or.inl (Eq.trans hj_right3.symm hj))
          · exact right3_not_local5 (by omega) t (Or.inr (Or.inl (Eq.trans hj_right3.symm hj)))
          · exact right3_ne_self (by omega) t (Eq.trans hj_right3.symm hj)
          · exact right3_not_local5 (by omega) t (Or.inr (Or.inr (Or.inl (Eq.trans hj_right3.symm hj))))
          · exact right3_not_local5 (by omega) t (Or.inr (Or.inr (Or.inr (Eq.trans hj_right3.symm hj))))
        have hj1_ne_cut : j1 ≠ cut := by
          intro hEq
          exact right2_ne_left3 (by omega) t (by
            calc
              right (right t) = gc.moverAt j1 := hj1_right2.symm
              _ = gc.moverAt cut := by rw [← hEq]
              _ = left (left (left t)) := hcut_left3)
        have hj1_lt_cut : j1.val < cut.val := by
          have hj1_le_cut : j1.val ≤ cut.val := by
            rw [hj1]
            omega
          have hneqv : j1.val ≠ cut.val := by
            intro hval
            exact hj1_ne_cut (Fin.ext hval)
          omega
        have hprev_gt_j : j.val < prev.val := by
          rw [hj1, ← hsucc] at hj1_lt_cut
          omega
        have hprev_local := hj_tail prev hprev_gt_j
        rcases hprev_local with hp3 | hp2 | hp1 | hp0 | hpr1 | hpr2
        · exact left4_ne_left3 (Eq.trans hprev_left4.symm hp3)
        · exact left4_not_local5 (by omega) t (Or.inl (Eq.trans hprev_left4.symm hp2))
        · exact left4_not_local5 (by omega) t (Or.inr (Or.inl (Eq.trans hprev_left4.symm hp1)))
        · exact left4_ne_self (Eq.trans hprev_left4.symm hp0)
        · exact left4_not_local5 (by omega) t
            (Or.inr (Or.inr (Or.inl (Eq.trans hprev_left4.symm hpr1))))
        · exact left4_not_local5 (by omega) t
            (Or.inr (Or.inr (Or.inr (Eq.trans hprev_left4.symm hpr2))))
      · rcases hLL2X with
          ⟨_hprev, _hkout_left3, _k1, _hk1, _hk1_left2,
            j, j1, hj_lt, hj1, hj_right3, hj1_right2, hj_tail⟩
        rcases hmin with
          ⟨cut, prev, hsucc, _hcut_le, hprev_left4, hcut_left3, hcut_tail, _hcut_min, _hstart⟩
        have hj_lt_cut : j.val < cut.val := by
          by_contra hnot
          push_neg at hnot
          have hj_in := hcut_tail j hnot
          rcases hj_in with hj | hj | hj | hj | hj | hj
          · exact right3_ne_left3 (by omega) t (Eq.trans hj_right3.symm hj)
          · exact right3_not_local5 (by omega) t (Or.inl (Eq.trans hj_right3.symm hj))
          · exact right3_not_local5 (by omega) t (Or.inr (Or.inl (Eq.trans hj_right3.symm hj)))
          · exact right3_ne_self (by omega) t (Eq.trans hj_right3.symm hj)
          · exact right3_not_local5 (by omega) t (Or.inr (Or.inr (Or.inl (Eq.trans hj_right3.symm hj))))
          · exact right3_not_local5 (by omega) t (Or.inr (Or.inr (Or.inr (Eq.trans hj_right3.symm hj))))
        have hj1_ne_cut : j1 ≠ cut := by
          intro hEq
          exact right2_ne_left3 (by omega) t (by
            calc
              right (right t) = gc.moverAt j1 := hj1_right2.symm
              _ = gc.moverAt cut := by rw [← hEq]
              _ = left (left (left t)) := hcut_left3)
        have hj1_lt_cut : j1.val < cut.val := by
          have hj1_le_cut : j1.val ≤ cut.val := by
            rw [hj1]
            omega
          have hneqv : j1.val ≠ cut.val := by
            intro hval
            exact hj1_ne_cut (Fin.ext hval)
          omega
        have hprev_gt_j : j.val < prev.val := by
          rw [hj1, ← hsucc] at hj1_lt_cut
          omega
        have hprev_local := hj_tail prev hprev_gt_j
        rcases hprev_local with hp3 | hp2 | hp1 | hp0 | hpr1 | hpr2
        · exact left4_ne_left3 (Eq.trans hprev_left4.symm hp3)
        · exact left4_not_local5 (by omega) t (Or.inl (Eq.trans hprev_left4.symm hp2))
        · exact left4_not_local5 (by omega) t (Or.inr (Or.inl (Eq.trans hprev_left4.symm hp1)))
        · exact left4_ne_self (Eq.trans hprev_left4.symm hp0)
        · exact left4_not_local5 (by omega) t
            (Or.inr (Or.inr (Or.inl (Eq.trans hprev_left4.symm hpr1))))
        · exact left4_not_local5 (by omega) t
            (Or.inr (Or.inr (Or.inr (Eq.trans hprev_left4.symm hpr2))))
    have hcross_prefix_not_right4_min :
        (RightStartedFromLeft2PrefixCrossResidue ∨ RightStartedFromRight4PrefixCrossResidue) →
        ¬ RightStartedFromRight4MinRestartResidue := by
      intro hcross hmin
      rcases hcross with hRL2X | hRR4X
      · rcases hRL2X with
          ⟨_hprev, _hkout_right3, _k1, _hk1, _hk1_right2,
            j, j1, hj_lt, hj1, hj_left3, hj1_left2, hj_tail⟩
        rcases hmin with
          ⟨cut, prev, hsucc, _hcut_le, hprev_right4, hcut_right3, hcut_tail, _hcut_min, _hstart⟩
        have hj_lt_cut : j.val < cut.val := by
          by_contra hnot
          push_neg at hnot
          have hj_in := hcut_tail j hnot
          rcases hj_in with hj | hj | hj | hj | hj | hj
          · exact left3_not_local5 (by omega) t (Or.inl (Eq.trans hj_left3.symm hj))
          · exact left3_not_local5 (by omega) t (Or.inr (Or.inl (Eq.trans hj_left3.symm hj)))
          · exact left3_ne_self (by omega) t (Eq.trans hj_left3.symm hj)
          · exact left3_not_local5 (by omega) t (Or.inr (Or.inr (Or.inl (Eq.trans hj_left3.symm hj))))
          · exact left3_not_local5 (by omega) t (Or.inr (Or.inr (Or.inr (Eq.trans hj_left3.symm hj))))
          · exact left3_ne_right3 (by omega) t (Eq.trans hj_left3.symm hj)
        have hj1_ne_cut : j1 ≠ cut := by
          intro hEq
          exact left2_ne_right3 (by omega) t (by
            calc
              left (left t) = gc.moverAt j1 := hj1_left2.symm
              _ = gc.moverAt cut := by rw [← hEq]
              _ = right (right (right t)) := hcut_right3)
        have hj1_lt_cut : j1.val < cut.val := by
          have hj1_le_cut : j1.val ≤ cut.val := by
            rw [hj1]
            omega
          have hneqv : j1.val ≠ cut.val := by
            intro hval
            exact hj1_ne_cut (Fin.ext hval)
          omega
        have hprev_gt_j : j.val < prev.val := by
          rw [hj1, ← hsucc] at hj1_lt_cut
          omega
        have hprev_local := hj_tail prev hprev_gt_j
        rcases hprev_local with hll | hl | ht0 | hr | hrr | hr3
        · exact right4_not_leftsix (Or.inr (Or.inl (Eq.trans hprev_right4.symm hll)))
        · exact right4_not_leftsix (Or.inr (Or.inr (Or.inl (Eq.trans hprev_right4.symm hl))))
        · exact right4_ne_self (Eq.trans hprev_right4.symm ht0)
        · exact right4_not_leftsix
            (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Eq.trans hprev_right4.symm hr))))))
        · exact right4_not_leftsix
            (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Eq.trans hprev_right4.symm hrr))))))
        · exact right4_ne_right3 (Eq.trans hprev_right4.symm hr3)
      · rcases hRR4X with
          ⟨_hprev, _hkout_right3, _k1, _hk1, _hk1_right2,
            j, j1, hj_lt, hj1, hj_left3, hj1_left2, hj_tail⟩
        rcases hmin with
          ⟨cut, prev, hsucc, _hcut_le, hprev_right4, hcut_right3, hcut_tail, _hcut_min, _hstart⟩
        have hj_lt_cut : j.val < cut.val := by
          by_contra hnot
          push_neg at hnot
          have hj_in := hcut_tail j hnot
          rcases hj_in with hj | hj | hj | hj | hj | hj
          · exact left3_not_local5 (by omega) t (Or.inl (Eq.trans hj_left3.symm hj))
          · exact left3_not_local5 (by omega) t (Or.inr (Or.inl (Eq.trans hj_left3.symm hj)))
          · exact left3_ne_self (by omega) t (Eq.trans hj_left3.symm hj)
          · exact left3_not_local5 (by omega) t (Or.inr (Or.inr (Or.inl (Eq.trans hj_left3.symm hj))))
          · exact left3_not_local5 (by omega) t (Or.inr (Or.inr (Or.inr (Eq.trans hj_left3.symm hj))))
          · exact left3_ne_right3 (by omega) t (Eq.trans hj_left3.symm hj)
        have hj1_ne_cut : j1 ≠ cut := by
          intro hEq
          exact left2_ne_right3 (by omega) t (by
            calc
              left (left t) = gc.moverAt j1 := hj1_left2.symm
              _ = gc.moverAt cut := by rw [← hEq]
              _ = right (right (right t)) := hcut_right3)
        have hj1_lt_cut : j1.val < cut.val := by
          have hj1_le_cut : j1.val ≤ cut.val := by
            rw [hj1]
            omega
          have hneqv : j1.val ≠ cut.val := by
            intro hval
            exact hj1_ne_cut (Fin.ext hval)
          omega
        have hprev_gt_j : j.val < prev.val := by
          rw [hj1, ← hsucc] at hj1_lt_cut
          omega
        have hprev_local := hj_tail prev hprev_gt_j
        rcases hprev_local with hll | hl | ht0 | hr | hrr | hr3
        · exact right4_not_leftsix (Or.inr (Or.inl (Eq.trans hprev_right4.symm hll)))
        · exact right4_not_leftsix (Or.inr (Or.inr (Or.inl (Eq.trans hprev_right4.symm hl))))
        · exact right4_ne_self (Eq.trans hprev_right4.symm ht0)
        · exact right4_not_leftsix
            (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Eq.trans hprev_right4.symm hr))))))
        · exact right4_not_leftsix
            (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Eq.trans hprev_right4.symm hrr))))))
        · exact right4_ne_right3 (Eq.trans hprev_right4.symm hr3)
    have hsame_prefix_not_left2_right_min :
        (RightStartedFromLeft2PrefixSameResidue ∨ RightStartedFromRight4PrefixSameResidue) →
        ¬ RightStartedFromLeft2MinRestartResidue := by
      intro hsame hmin
      rcases hsame with hRL2S | hRR4S
      · rcases hRL2S with
          ⟨_hprev, _hkout_right3, _k1, _hk1, _hk1_right2,
            j, j1, hj_lt, hj1, hj_right4, hj1_right3, hj_tail⟩
        rcases hmin with
          ⟨cut, prev, hsucc, hcut_le, hprev_right2, hcut_right3, hcut_tail, hcut_min, _hstart⟩
        have hj_lt_cut : j.val < cut.val := by
          by_contra hnot
          push_neg at hnot
          have hj_in := hcut_tail j hnot
          rcases hj_in with hj | hj | hj | hj | hj | hj
          · exact right4_not_leftsix (Or.inr (Or.inl (Eq.trans hj_right4.symm hj)))
          · exact right4_not_leftsix (Or.inr (Or.inr (Or.inl (Eq.trans hj_right4.symm hj))))
          · exact right4_ne_self (Eq.trans hj_right4.symm hj)
          · exact right4_not_leftsix
              (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Eq.trans hj_right4.symm hj))))))
          · exact right4_not_leftsix
              (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Eq.trans hj_right4.symm hj))))))
          · exact right4_ne_right3 (Eq.trans hj_right4.symm hj)
        have hj1_le_cut : j1.val ≤ cut.val := by
          rw [hj1]
          omega
        have hj1_le_kout : j1.val ≤ k_out.val := by
          rw [hj1]
          omega
        have hj1_tail :
            ∀ k : Fin gc.configs.length,
              j1.val ≤ k.val →
              gc.moverAt k = left (left t) ∨
                gc.moverAt k = left t ∨
                gc.moverAt k = t ∨
                gc.moverAt k = right t ∨
                gc.moverAt k = right (right t) ∨
                gc.moverAt k = right (right (right t)) := by
          intro k hk_ge
          have hj_lt_k : j.val < k.val := by
            rw [hj1] at hk_ge
            omega
          exact hj_tail k hj_lt_k
        have hnot_lt : ¬ j1.val < cut.val := by
          intro hj1_lt_cut
          exact (hcut_min j1 hj1_lt_cut) ⟨hj1_le_kout, hj1_right3, hj1_tail⟩
        have hj1_eq_cut : j1 = cut := by
          apply Fin.ext
          exact Nat.le_antisymm hj1_le_cut (Nat.le_of_not_gt hnot_lt)
        have hprev_eq_j : prev = j := by
          apply Fin.ext
          have hcut_eq_j1 : cut.val = j1.val := by
            simpa using (congrArg Fin.val hj1_eq_cut).symm
          rw [hj1, ← hsucc] at hcut_eq_j1
          omega
        exact right4_not_leftsix
          (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by
            calc
              right (right (right (right t))) = gc.moverAt j := hj_right4.symm
              _ = gc.moverAt prev := by rw [hprev_eq_j]
              _ = right (right t) := hprev_right2))))))
      · rcases hRR4S with
          ⟨_hprev, _hkout_right3, _k1, _hk1, _hk1_right2,
            j, j1, hj_lt, hj1, hj_right4, hj1_right3, hj_tail⟩
        rcases hmin with
          ⟨cut, prev, hsucc, hcut_le, hprev_right2, hcut_right3, hcut_tail, hcut_min, _hstart⟩
        have hj_lt_cut : j.val < cut.val := by
          by_contra hnot
          push_neg at hnot
          have hj_in := hcut_tail j hnot
          rcases hj_in with hj | hj | hj | hj | hj | hj
          · exact right4_not_leftsix (Or.inr (Or.inl (Eq.trans hj_right4.symm hj)))
          · exact right4_not_leftsix (Or.inr (Or.inr (Or.inl (Eq.trans hj_right4.symm hj))))
          · exact right4_ne_self (Eq.trans hj_right4.symm hj)
          · exact right4_not_leftsix
              (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Eq.trans hj_right4.symm hj))))))
          · exact right4_not_leftsix
              (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Eq.trans hj_right4.symm hj))))))
          · exact right4_ne_right3 (Eq.trans hj_right4.symm hj)
        have hj1_le_cut : j1.val ≤ cut.val := by
          rw [hj1]
          omega
        have hj1_le_kout : j1.val ≤ k_out.val := by
          rw [hj1]
          omega
        have hj1_tail :
            ∀ k : Fin gc.configs.length,
              j1.val ≤ k.val →
              gc.moverAt k = left (left t) ∨
                gc.moverAt k = left t ∨
                gc.moverAt k = t ∨
                gc.moverAt k = right t ∨
                gc.moverAt k = right (right t) ∨
                gc.moverAt k = right (right (right t)) := by
          intro k hk_ge
          have hj_lt_k : j.val < k.val := by
            rw [hj1] at hk_ge
            omega
          exact hj_tail k hj_lt_k
        have hnot_lt : ¬ j1.val < cut.val := by
          intro hj1_lt_cut
          exact (hcut_min j1 hj1_lt_cut) ⟨hj1_le_kout, hj1_right3, hj1_tail⟩
        have hj1_eq_cut : j1 = cut := by
          apply Fin.ext
          exact Nat.le_antisymm hj1_le_cut (Nat.le_of_not_gt hnot_lt)
        have hprev_eq_j : prev = j := by
          apply Fin.ext
          have hcut_eq_j1 : cut.val = j1.val := by
            simpa using (congrArg Fin.val hj1_eq_cut).symm
          rw [hj1, ← hsucc] at hcut_eq_j1
          omega
        exact right4_not_leftsix
          (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by
            calc
              right (right (right (right t))) = gc.moverAt j := hj_right4.symm
              _ = gc.moverAt prev := by rw [hprev_eq_j]
              _ = right (right t) := hprev_right2))))))
    let LeftContinuationSharp : Prop :=
        (∃ phase0 : TernaryPhase gc t,
          phase0.a = k_out ∧
          k_out.val + 2 < phase0.s.val ∧
          (∀ k : Fin gc.configs.length,
            k_out.val < k.val → k.val < phase0.s.val →
            gc.moverAt k = left (left t) ∨ gc.moverAt k = left t)) ∨
        (∀ k : Fin gc.configs.length,
          k_out.val < k.val →
          gc.moverAt k = left (left t) ∨ gc.moverAt k = left t)
    let RightContinuationSharp : Prop :=
        (∃ phase0 : TernaryPhase gc t,
          phase0.a = k_out ∧
          k_out.val + 2 < phase0.s.val ∧
          (∀ k : Fin gc.configs.length,
            k_out.val < k.val → k.val < phase0.s.val →
            gc.moverAt k = right t ∨ gc.moverAt k = right (right t))) ∨
        (∀ k : Fin gc.configs.length,
          k_out.val < k.val →
          gc.moverAt k = right t ∨ gc.moverAt k = right (right t))
    let LeftSameSharpResidue : Prop :=
        ∃ j j1 : Fin gc.configs.length,
          j.val < k_out.val ∧
          j1.val = j.val + 1 ∧
          gc.moverAt j = left (left (left (left t))) ∧
          gc.moverAt j1 = left (left (left t)) ∧
          (∀ k : Fin gc.configs.length,
            j.val < k.val →
            gc.moverAt k = left (left (left t)) ∨
              gc.moverAt k = left (left t) ∨
              gc.moverAt k = left t ∨
              gc.moverAt k = t ∨
              gc.moverAt k = right t ∨
              gc.moverAt k = right (right t)) ∧
          gc.moverAt k_out = left (left (left t)) ∧
          ∃ k1 : Fin gc.configs.length,
            k1.val = k_out.val + 1 ∧
            gc.moverAt k1 = left (left t) ∧
            LeftContinuationSharp
    let LeftCrossSharpResidue : Prop :=
        ∃ j j1 : Fin gc.configs.length,
          j.val < k_out.val ∧
          j1.val = j.val + 1 ∧
          gc.moverAt j = right (right (right t)) ∧
          gc.moverAt j1 = right (right t) ∧
          (∀ k : Fin gc.configs.length,
            j.val < k.val →
            gc.moverAt k = left (left (left t)) ∨
              gc.moverAt k = left (left t) ∨
              gc.moverAt k = left t ∨
              gc.moverAt k = t ∨
              gc.moverAt k = right t ∨
              gc.moverAt k = right (right t)) ∧
          gc.moverAt k_out = left (left (left t)) ∧
          ∃ k1 : Fin gc.configs.length,
            k1.val = k_out.val + 1 ∧
            gc.moverAt k1 = left (left t) ∧
            LeftContinuationSharp
    let RightCrossSharpResidue : Prop :=
        ∃ j j1 : Fin gc.configs.length,
          j.val < k_out.val ∧
          j1.val = j.val + 1 ∧
          gc.moverAt j = left (left (left t)) ∧
          gc.moverAt j1 = left (left t) ∧
          (∀ k : Fin gc.configs.length,
            j.val < k.val →
            gc.moverAt k = left (left t) ∨
              gc.moverAt k = left t ∨
              gc.moverAt k = t ∨
              gc.moverAt k = right t ∨
              gc.moverAt k = right (right t) ∨
              gc.moverAt k = right (right (right t))) ∧
          gc.moverAt k_out = right (right (right t)) ∧
          ∃ k1 : Fin gc.configs.length,
            k1.val = k_out.val + 1 ∧
            gc.moverAt k1 = right (right t) ∧
            RightContinuationSharp
    let RightSameSharpResidue : Prop :=
        ∃ j j1 : Fin gc.configs.length,
          j.val < k_out.val ∧
          j1.val = j.val + 1 ∧
          gc.moverAt j = right (right (right (right t))) ∧
          gc.moverAt j1 = right (right (right t)) ∧
          (∀ k : Fin gc.configs.length,
            j.val < k.val →
            gc.moverAt k = left (left t) ∨
              gc.moverAt k = left t ∨
              gc.moverAt k = t ∨
              gc.moverAt k = right t ∨
              gc.moverAt k = right (right t) ∨
              gc.moverAt k = right (right (right t))) ∧
          gc.moverAt k_out = right (right (right t)) ∧
          ∃ k1 : Fin gc.configs.length,
            k1.val = k_out.val + 1 ∧
            gc.moverAt k1 = right (right t) ∧
            RightContinuationSharp
    have hleft_same_sharp :
        LeftStartedPrefixRestartPhaseSameResidue ∨ LeftStartedPrefixRestartTerminalSameResidue →
        LeftSameSharpResidue := by
      intro h
      rcases h with hphase | hterm
      · rcases hphase with ⟨hprefix, phase0, hphase0a, hlong, hphase_branch⟩
        rcases hprefix with ⟨hkout_left3, k1, hk1, hk1_left2, j, j1, hj_lt, hj1_eq, hj_left4, hj1_left3, hj_tail⟩
        exact ⟨j, j1, hj_lt, hj1_eq, hj_left4, hj1_left3, hj_tail, hkout_left3, k1, hk1, hk1_left2,
          Or.inl ⟨phase0, hphase0a, hlong, hphase_branch⟩⟩
      · rcases hterm with ⟨j, hj_lt, hj_left4, hj_tail, hkout_left3, k1, hk1, hk1_left2, hterm⟩
        have hj1_lt_len : j.val + 1 < gc.configs.length := by
          exact lt_of_le_of_lt (Nat.succ_le_of_lt hj_lt) k_out.isLt
        let j1 : Fin gc.configs.length := ⟨j.val + 1, hj1_lt_len⟩
        have hsucc := left_prefix_edge_successor_shape gc t (by omega) j hj1_lt_len (Or.inl hj_left4) hj_tail
        rcases hsucc with ⟨hj_left4', hj1_left3⟩ | hcross
        · exact ⟨j, j1, hj_lt, rfl, hj_left4', hj1_left3, hj_tail, hkout_left3, k1, hk1, hk1_left2, Or.inr hterm⟩
        · exfalso
          exact right4_ne_left3 (by
            have hEq : right (right (right t)) = left (left (left (left t))) := by
              calc
                right (right (right t)) = gc.moverAt j := hcross.1.symm
                _ = left (left (left (left t))) := hj_left4
            simpa [left_right_eq_self] using congrArg right hEq)
    have hleft_cross_sharp :
        LeftStartedPrefixRestartPhaseCrossResidue ∨ LeftStartedPrefixRestartTerminalCrossResidue →
        LeftCrossSharpResidue := by
      intro h
      rcases h with hphase | hterm
      · rcases hphase with ⟨hprefix, phase0, hphase0a, hlong, hphase_branch⟩
        rcases hprefix with ⟨hkout_left3, k1, hk1, hk1_left2, j, j1, hj_lt, hj1_eq, hj_right3, hj1_right2, hj_tail⟩
        exact ⟨j, j1, hj_lt, hj1_eq, hj_right3, hj1_right2, hj_tail, hkout_left3, k1, hk1, hk1_left2,
          Or.inl ⟨phase0, hphase0a, hlong, hphase_branch⟩⟩
      · rcases hterm with ⟨j, hj_lt, hj_right3, hj_tail, hkout_left3, k1, hk1, hk1_left2, hterm⟩
        have hj1_lt_len : j.val + 1 < gc.configs.length := by
          exact lt_of_le_of_lt (Nat.succ_le_of_lt hj_lt) k_out.isLt
        let j1 : Fin gc.configs.length := ⟨j.val + 1, hj1_lt_len⟩
        have hsucc := left_prefix_edge_successor_shape gc t (by omega) j hj1_lt_len (Or.inr hj_right3) hj_tail
        rcases hsucc with hsame | ⟨hj_right3', hj1_right2⟩
        · exfalso
          exact right4_ne_left3 (by
            have hEq : right (right (right t)) = left (left (left (left t))) := by
              calc
                right (right (right t)) = gc.moverAt j := hj_right3.symm
                _ = left (left (left (left t))) := hsame.1
            simpa [left_right_eq_self] using congrArg right hEq)
        · exact ⟨j, j1, hj_lt, rfl, hj_right3', hj1_right2, hj_tail, hkout_left3, k1, hk1, hk1_left2, Or.inr hterm⟩
    have hright_cross_sharp :
        RightStartedPrefixRestartPhaseCrossResidue ∨ RightStartedPrefixRestartTerminalCrossResidue →
        RightCrossSharpResidue := by
      intro h
      rcases h with hphase | hterm
      · rcases hphase with ⟨hprefix, phase0, hphase0a, hlong, hphase_branch⟩
        rcases hprefix with ⟨hkout_right3, k1, hk1, hk1_right2, j, j1, hj_lt, hj1_eq, hj_left3, hj1_left2, hj_tail⟩
        exact ⟨j, j1, hj_lt, hj1_eq, hj_left3, hj1_left2, hj_tail, hkout_right3, k1, hk1, hk1_right2,
          Or.inl ⟨phase0, hphase0a, hlong, hphase_branch⟩⟩
      · rcases hterm with ⟨j, hj_lt, hj_left3, hj_tail, hkout_right3, k1, hk1, hk1_right2, hterm⟩
        have hj1_lt_len : j.val + 1 < gc.configs.length := by
          exact lt_of_le_of_lt (Nat.succ_le_of_lt hj_lt) k_out.isLt
        let j1 : Fin gc.configs.length := ⟨j.val + 1, hj1_lt_len⟩
        have hsucc := right_prefix_edge_successor_shape gc t (by omega) j hj1_lt_len (Or.inl hj_left3) hj_tail
        rcases hsucc with ⟨hj_left3', hj1_left2⟩ | hsame
        · exact ⟨j, j1, hj_lt, rfl, hj_left3', hj1_left2, hj_tail, hkout_right3, k1, hk1, hk1_right2, Or.inr hterm⟩
        · exfalso
          exact right4_ne_left3 (by
            calc
              right (right (right (right t))) = gc.moverAt j := hsame.1.symm
              _ = left (left (left t)) := hj_left3)
    have hright_same_sharp :
        RightStartedPrefixRestartPhaseSameResidue ∨ RightStartedPrefixRestartTerminalSameResidue →
        RightSameSharpResidue := by
      intro h
      rcases h with hphase | hterm
      · rcases hphase with ⟨hprefix, phase0, hphase0a, hlong, hphase_branch⟩
        rcases hprefix with ⟨hkout_right3, k1, hk1, hk1_right2, j, j1, hj_lt, hj1_eq, hj_right4, hj1_right3, hj_tail⟩
        exact ⟨j, j1, hj_lt, hj1_eq, hj_right4, hj1_right3, hj_tail, hkout_right3, k1, hk1, hk1_right2,
          Or.inl ⟨phase0, hphase0a, hlong, hphase_branch⟩⟩
      · rcases hterm with ⟨j, hj_lt, hj_right4, hj_tail, hkout_right3, k1, hk1, hk1_right2, hterm⟩
        have hj1_lt_len : j.val + 1 < gc.configs.length := by
          exact lt_of_le_of_lt (Nat.succ_le_of_lt hj_lt) k_out.isLt
        let j1 : Fin gc.configs.length := ⟨j.val + 1, hj1_lt_len⟩
        have hsucc := right_prefix_edge_successor_shape gc t (by omega) j hj1_lt_len (Or.inr hj_right4) hj_tail
        rcases hsucc with hcross | ⟨hj_right4', hj1_right3⟩
        · exfalso
          exact right4_ne_left3 (by
            calc
              right (right (right (right t))) = gc.moverAt j := hj_right4.symm
              _ = left (left (left t)) := hcross.1)
        · exact ⟨j, j1, hj_lt, rfl, hj_right4', hj1_right3, hj_tail, hkout_right3, k1, hk1, hk1_right2, Or.inr hterm⟩
    have left_same_sharp_left4_min_live :
        LeftSameSharpResidue → LeftStartedFromLeft4MinRestartResidue := by
      intro h
      rcases h with ⟨j, j1, hj_lt, hj1_eq, hj_left4, hj1_left3, hj_tail, hkout_left3, k1, hk1, hk1_left2, hcont⟩
      have hsame_final : LeftFromLeft4Final := by
        exact ⟨hkout_left3, j, j1, hj_lt, hj1_eq, hj_left4, hj1_left3, hj_tail⟩
      have htail : LeftTailResidue := hleft_same_tail hsame_final
      have hstart : LeftKoutStartedResidue := by
        refine ⟨hkout_left3, ?_⟩
        rcases hcont with hphase | hterm
        · rcases hphase with ⟨phase0, hphase0a, hlong, hphase_branch⟩
          exact Or.inl ⟨phase0, hphase0a, hlong, hphase_branch, ⟨k1, hk1, hk1_left2⟩⟩
        · exact Or.inr hterm
      have hrestart : LeftTailRestartResidue := ⟨htail, hstart⟩
      have hprev :
          LeftStartedFromLeft4PrefixSameResidue ∨ LeftStartedFromLeft2PrefixSameResidue := by
        have hprefix : LeftStartedPrefixSameResidue := by
          exact ⟨hkout_left3, k1, hk1, hk1_left2, j, j1, hj_lt, hj1_eq, hj_left4, hj1_left3, hj_tail⟩
        rcases hleft_tail_restart_prev_shape0 hrestart with hLL4 | hLL2
        · exact Or.inl ⟨hLL4.1, hprefix⟩
        · exact Or.inr ⟨hLL2.1, hprefix⟩
      have hnot_left2 : ¬ LeftStartedFromLeft2MinRestartResidue :=
        hsame_prefix_not_left2_min hprev
      rcases hleft_tail_restart_prev_shape_min hrestart with hLL4 | hLL2
      · exact hLL4
      · exact False.elim (hnot_left2 hLL2)
    have left_cross_sharp_left2_min :
        LeftCrossSharpResidue → LeftStartedFromLeft2MinRestartResidue := by
      intro h
      rcases h with ⟨j, j1, hj_lt, hj1_eq, hj_right3, hj1_right2, hj_tail, hkout_left3, k1, hk1, hk1_left2, hcont⟩
      have hcross_final : LeftFromRight3Final := by
        exact ⟨hkout_left3, j, j1, hj_lt, hj1_eq, hj_right3, hj1_right2, hj_tail⟩
      have htail : LeftTailResidue := hleft_cross_tail hcross_final
      have hstart : LeftKoutStartedResidue := by
        refine ⟨hkout_left3, ?_⟩
        rcases hcont with hphase | hterm
        · rcases hphase with ⟨phase0, hphase0a, hlong, hphase_branch⟩
          exact Or.inl ⟨phase0, hphase0a, hlong, hphase_branch, ⟨k1, hk1, hk1_left2⟩⟩
        · exact Or.inr hterm
      have hrestart : LeftTailRestartResidue := ⟨htail, hstart⟩
      have hprev :
          LeftStartedFromLeft4PrefixCrossResidue ∨ LeftStartedFromLeft2PrefixCrossResidue := by
        have hprefix : LeftStartedPrefixCrossResidue := by
          exact ⟨hkout_left3, k1, hk1, hk1_left2, j, j1, hj_lt, hj1_eq, hj_right3, hj1_right2, hj_tail⟩
        rcases hleft_tail_restart_prev_shape0 hrestart with hLL4 | hLL2
        · exact Or.inl ⟨hLL4.1, hprefix⟩
        · exact Or.inr ⟨hLL2.1, hprefix⟩
      have hnot_left4 : ¬ LeftStartedFromLeft4MinRestartResidue :=
        hcross_prefix_not_left4_min hprev
      rcases hleft_tail_restart_prev_shape_min hrestart with hLL4 | hLL2
      · exact False.elim (hnot_left4 hLL4)
      · exact hLL2
    have right_cross_sharp_left2_min :
        RightCrossSharpResidue → RightStartedFromLeft2MinRestartResidue := by
      intro h
      rcases h with ⟨j, j1, hj_lt, hj1_eq, hj_left3, hj1_left2, hj_tail, hkout_right3, k1, hk1, hk1_right2, hcont⟩
      have hcross_final : RightFromLeft3Final := by
        exact ⟨hkout_right3, j, j1, hj_lt, hj1_eq, hj_left3, hj1_left2, hj_tail⟩
      have htail : RightTailResidue := hright_cross_tail hcross_final
      have hstart : RightKoutStartedResidue := by
        refine ⟨hkout_right3, ?_⟩
        rcases hcont with hphase | hterm
        · rcases hphase with ⟨phase0, hphase0a, hlong, hphase_branch⟩
          exact Or.inl ⟨phase0, hphase0a, hlong, hphase_branch, ⟨k1, hk1, hk1_right2⟩⟩
        · exact Or.inr hterm
      have hrestart : RightTailRestartResidue := ⟨htail, hstart⟩
      have hprev :
          RightStartedFromLeft2PrefixCrossResidue ∨ RightStartedFromRight4PrefixCrossResidue := by
        have hprefix : RightStartedPrefixCrossResidue := by
          exact ⟨hkout_right3, k1, hk1, hk1_right2, j, j1, hj_lt, hj1_eq, hj_left3, hj1_left2, hj_tail⟩
        rcases hright_tail_restart_prev_shape0 hrestart with hRL2 | hRR4
        · exact Or.inl ⟨hRL2.1, hprefix⟩
        · exact Or.inr ⟨hRR4.1, hprefix⟩
      have hnot_right4 : ¬ RightStartedFromRight4MinRestartResidue :=
        hcross_prefix_not_right4_min hprev
      rcases hright_tail_restart_prev_shape_min hrestart with hRL2 | hRR4
      · exact hRL2
      · exact False.elim (hnot_right4 hRR4)
    have right_same_sharp_right4_min_live :
        RightSameSharpResidue → RightStartedFromRight4MinRestartResidue := by
      intro h
      rcases h with ⟨j, j1, hj_lt, hj1_eq, hj_right4, hj1_right3, hj_tail, hkout_right3, k1, hk1, hk1_right2, hcont⟩
      have hsame_final : RightFromRight4Final := by
        exact ⟨hkout_right3, j, j1, hj_lt, hj1_eq, hj_right4, hj1_right3, hj_tail⟩
      have htail : RightTailResidue := hright_same_tail hsame_final
      have hstart : RightKoutStartedResidue := by
        refine ⟨hkout_right3, ?_⟩
        rcases hcont with hphase | hterm
        · rcases hphase with ⟨phase0, hphase0a, hlong, hphase_branch⟩
          exact Or.inl ⟨phase0, hphase0a, hlong, hphase_branch, ⟨k1, hk1, hk1_right2⟩⟩
        · exact Or.inr hterm
      have hrestart : RightTailRestartResidue := ⟨htail, hstart⟩
      have hprev :
          RightStartedFromLeft2PrefixSameResidue ∨ RightStartedFromRight4PrefixSameResidue := by
        have hprefix : RightStartedPrefixSameResidue := by
          exact ⟨hkout_right3, k1, hk1, hk1_right2, j, j1, hj_lt, hj1_eq, hj_right4, hj1_right3, hj_tail⟩
        rcases hright_tail_restart_prev_shape0 hrestart with hRL2 | hRR4
        · exact Or.inl ⟨hRL2.1, hprefix⟩
        · exact Or.inr ⟨hRR4.1, hprefix⟩
      have hnot_left2 : ¬ RightStartedFromLeft2MinRestartResidue :=
        hsame_prefix_not_left2_right_min hprev
      rcases hright_tail_restart_prev_shape_min hrestart with hRL2 | hRR4
      · exact False.elim (hnot_left2 hRL2)
      · exact hRR4
    have noFire_of_intervalFireCount_zero_local_live
        (p : Fin sys.rs.n) {a b : Nat}
        (hab : a ≤ b) (hb : b ≤ gc.configs.length)
        (hzero : gc.intervalFireCount p a b = 0) :
        ∀ k : Fin gc.configs.length, a ≤ k.val → k.val < b → gc.moverAt k ≠ p := by
      intro k hka hkb hmov
      have hpfc_step : gc.prefixFireCount p (k.val + 1) = gc.prefixFireCount p k.val + 1 := by
        rw [gc.prefixFireCount_succ]
        rw [gc.fireIndicator_of_lt p k.isLt]
        simp [hmov]
      have hmono1 : gc.prefixFireCount p a ≤ gc.prefixFireCount p k.val := by
        unfold GoodCycle.prefixFireCount
        exact Finset.sum_le_sum_of_subset (Finset.range_mono hka)
      have hmono2 : gc.prefixFireCount p (k.val + 1) ≤ gc.prefixFireCount p b := by
        unfold GoodCycle.prefixFireCount
        exact Finset.sum_le_sum_of_subset (Finset.range_mono (by omega))
      unfold GoodCycle.intervalFireCount at hzero
      omega
    have pre_step_fires_neighbor_local_live
        (phase : TernaryPhase gc t)
        (hgap : phase.s.val - phase.a.val ≥ 2) :
        gc.moverAt ⟨phase.s.val - 1,
            by have := phase.ha_lt_s; have := phase.s.isLt; omega⟩ = left t ∨
        gc.moverAt ⟨phase.s.val - 1,
            by have := phase.ha_lt_s; have := phase.s.isLt; omega⟩ = right t ∨
        gc.moverAt ⟨phase.s.val - 1,
            by have := phase.ha_lt_s; have := phase.s.isLt; omega⟩ = t := by
      set prev : Fin gc.configs.length := ⟨phase.s.val - 1, by
        have := phase.ha_lt_s
        have := phase.s.isLt
        omega⟩
      have hnext : nextIndex gc.configs prev = phase.s := by
        ext
        simp [nextIndex]
        rw [show phase.s.val - 1 + 1 = phase.s.val from by omega, Nat.mod_eq_of_lt phase.s.isLt]
      have hlocal := gc.next_mover_is_local prev
      simp only at hlocal
      rw [hnext, phase.hs_mover] at hlocal
      rcases hlocal with hleft | hself | hright
      · right; left
        calc
          gc.moverAt prev = right (left (gc.moverAt prev)) := (right_left_eq_self _).symm
          _ = right t := by rw [hleft]
      · right; right; exact hself.symm
      · left
        calc
          gc.moverAt prev = left (right (gc.moverAt prev)) := (left_right_eq_self _).symm
          _ = left t := by rw [hright]
    have one_sided_normal_prev_left_local_live
        (phase : TernaryPhase gc t)
        (hnorm : isNormalFormGap gc t phase)
        (hJ1 : gc.intervalFireCount (left t) phase.a.val phase.s.val = 1)
        (hK0 : gc.intervalFireCount (right t) phase.a.val phase.s.val = 0)
        (hgap2 : phase.s.val - phase.a.val ≥ 2) :
        gc.moverAt ⟨phase.s.val - 1,
            by have := phase.ha_lt_s; have := phase.s.isLt; omega⟩ = left t := by
      set prev : Fin gc.configs.length := ⟨phase.s.val - 1, by
        have := phase.ha_lt_s
        have := phase.s.isLt
        omega⟩
      have hprev_ge_a : phase.a.val ≤ prev.val := by
        dsimp [prev]
        omega
      have hprev_lt_s : prev.val < phase.s.val := by
        dsimp [prev]
        omega
      have hright_ne : gc.moverAt prev ≠ right t := by
        exact noFire_of_intervalFireCount_zero_local_live (right t)
          (show phase.a.val ≤ phase.s.val by omega)
          (Nat.le_of_lt phase.s.isLt) hK0 prev hprev_ge_a hprev_lt_s
      rcases pre_step_fires_neighbor_local_live phase hgap2 with hprevL | hprevR | hprevT
      · exact hprevL
      · exact False.elim (hright_ne hprevR)
      · exact False.elim (phase.ht_nofire prev hprev_ge_a hprev_lt_s hprevT)
    have one_sided_normal_prev_right_local_live
        (phase : TernaryPhase gc t)
        (hnorm : isNormalFormGap gc t phase)
        (hJ0 : gc.intervalFireCount (left t) phase.a.val phase.s.val = 0)
        (hK1 : gc.intervalFireCount (right t) phase.a.val phase.s.val = 1)
        (hgap2 : phase.s.val - phase.a.val ≥ 2) :
        gc.moverAt ⟨phase.s.val - 1,
            by have := phase.ha_lt_s; have := phase.s.isLt; omega⟩ = right t := by
      set prev : Fin gc.configs.length := ⟨phase.s.val - 1, by
        have := phase.ha_lt_s
        have := phase.s.isLt
        omega⟩
      have hprev_ge_a : phase.a.val ≤ prev.val := by
        dsimp [prev]
        omega
      have hprev_lt_s : prev.val < phase.s.val := by
        dsimp [prev]
        omega
      have hleft_ne : gc.moverAt prev ≠ left t := by
        exact noFire_of_intervalFireCount_zero_local_live (left t)
          (show phase.a.val ≤ phase.s.val by omega)
          (Nat.le_of_lt phase.s.isLt) hJ0 prev hprev_ge_a hprev_lt_s
      rcases pre_step_fires_neighbor_local_live phase hgap2 with hprevL | hprevR | hprevT
      · exact False.elim (hleft_ne hprevL)
      · exact hprevR
      · exact False.elim (phase.ht_nofire prev hprev_ge_a hprev_lt_s hprevT)
    have left_continuation_phase_counts
        (phase0 : TernaryPhase gc t)
        (hphase0a : phase0.a = k_out)
        (hlong : k_out.val + 2 < phase0.s.val)
        (hkout_left3 : gc.moverAt k_out = left (left (left t)))
        (hphase_branch :
          ∀ k : Fin gc.configs.length,
            k_out.val < k.val → k.val < phase0.s.val →
            gc.moverAt k = left (left t) ∨ gc.moverAt k = left t) :
        gc.intervalFireCount (left t) phase0.a.val phase0.s.val = 1 ∧
        gc.intervalFireCount (right t) phase0.a.val phase0.s.val = 0 := by
      have hK0 : gc.intervalFireCount (right t) phase0.a.val phase0.s.val = 0 := by
        apply intervalFireCount_eq_zero_of_noFire gc (right t)
          (Nat.le_of_lt phase0.ha_lt_s) (Nat.le_of_lt phase0.s.isLt)
        intro k hk_ge hk_lt
        by_cases hk_eq : k = k_out
        · subst hk_eq
          intro hk
          exact (left3_not_local5 (by omega) t) (Or.inr (Or.inr (Or.inl (Eq.trans hkout_left3.symm hk))))
        · have hk_gt : k_out.val < k.val := by
            have hneqv : k.val ≠ k_out.val := by
              intro hval
              exact hk_eq (Fin.ext hval)
            omega
          rcases hphase_branch k hk_gt hk_lt with hk | hk
          · intro hkr
            exact left2_ne_right (by omega) t (Eq.trans hk.symm hkr)
          · intro hkr
            exact left_ne_right (by omega) t (Eq.trans hk.symm hkr)
      have hnorm0 : isNormalFormGap gc t phase0 := hall_normal phase0
      have hJ1 : gc.intervalFireCount (left t) phase0.a.val phase0.s.val = 1 := by
        exact (normalForm_gap_constraint gc t phase0 hnorm0).2.1 hK0
      exact ⟨hJ1, hK0⟩
    have right_continuation_phase_counts_live
        (phase0 : TernaryPhase gc t)
        (hphase0a : phase0.a = k_out)
        (hlong : k_out.val + 2 < phase0.s.val)
        (hkout_right3 : gc.moverAt k_out = right (right (right t)))
        (hphase_branch :
          ∀ k : Fin gc.configs.length,
            k_out.val < k.val → k.val < phase0.s.val →
            gc.moverAt k = right t ∨ gc.moverAt k = right (right t)) :
        gc.intervalFireCount (left t) phase0.a.val phase0.s.val = 0 ∧
        gc.intervalFireCount (right t) phase0.a.val phase0.s.val = 1 := by
      have hJ0 : gc.intervalFireCount (left t) phase0.a.val phase0.s.val = 0 := by
        apply intervalFireCount_eq_zero_of_noFire gc (left t)
          (Nat.le_of_lt phase0.ha_lt_s) (Nat.le_of_lt phase0.s.isLt)
        intro k hk_ge hk_lt
        by_cases hk_eq : k = k_out
        · subst hk_eq
          intro hk
          exact (right3_not_local5 (by omega) t) (Or.inr (Or.inl (Eq.trans hkout_right3.symm hk)))
        · have hk_gt : k_out.val < k.val := by
            have hneqv : k.val ≠ k_out.val := by
              intro hval
              exact hk_eq (Fin.ext hval)
            omega
          rcases hphase_branch k hk_gt hk_lt with hk | hk
          · intro hkl
            exact right_ne_left (by omega) t (Eq.trans hk.symm hkl)
          · intro hkl
            exact right2_ne_left (by omega) t (Eq.trans hk.symm hkl)
      have hnorm0 : isNormalFormGap gc t phase0 := hall_normal phase0
      have hK1 : gc.intervalFireCount (right t) phase0.a.val phase0.s.val = 1 := by
        exact (normalForm_gap_constraint gc t phase0 hnorm0).1 hJ0
      exact ⟨hJ0, hK1⟩
    have left_continuation_len2_suffix_or_ec_live
        (phase0 : TernaryPhase gc t)
        (hphase0a : phase0.a = k_out)
        (hlong : k_out.val + 2 < phase0.s.val)
        (hkout_left3 : gc.moverAt k_out = left (left (left t)))
        (hphase_branch :
          ∀ k : Fin gc.configs.length,
            k_out.val < k.val → k.val < phase0.s.val →
            gc.moverAt k = left (left t) ∨ gc.moverAt k = left t) :
        hasEntryConflict gc ∨
        ∃ aL prevL : Fin gc.configs.length,
          k_out.val < aL.val ∧
          aL.val + 2 = phase0.s.val ∧
          gc.moverAt aL = left (left t) ∧
          prevL.val = aL.val + 1 ∧
          gc.moverAt prevL = left t := by
      have hJ1K0 := left_continuation_phase_counts phase0 hphase0a hlong hkout_left3 hphase_branch
      let aL : Fin gc.configs.length := ⟨phase0.s.val - 2, by
        have := phase0.s.isLt
        omega⟩
      have haL_eq : phase0.s.val = aL.val + 2 := by
        dsimp [aL]
        omega
      have haL_lt_s : aL.val < phase0.s.val := by
        dsimp [aL]
        omega
      have haL_ge_a : phase0.a.val ≤ aL.val := by
        dsimp [aL]
        omega
      have haL_nonmover : gc.moverAt aL ≠ t := phase0.ht_nofire aL haL_ge_a haL_lt_s
      let phaseL2 : TernaryPhase gc t := {
        a := aL
        s := phase0.s
        ha_lt_s := haL_lt_s
        hs_mover := phase0.hs_mover
        ha_nonmover := haL_nonmover
        ht_nofire := by
          intro k hk1 hk2
          exact phase0.ht_nofire k (le_trans haL_ge_a hk1) hk2
      }
      have hnormL2 : isNormalFormGap gc t phaseL2 := hall_normal phaseL2
      have hno_right_L2 :
          ∀ k : Fin gc.configs.length,
            aL.val ≤ k.val → k.val < phase0.s.val → gc.moverAt k ≠ right t := by
        intro k hk1 hk2
        exact noFire_of_intervalFireCount_zero_local_live (right t)
          (show phase0.a.val ≤ phase0.s.val by omega)
          (Nat.le_of_lt phase0.s.isLt) hJ1K0.2 k (le_trans haL_ge_a hk1) hk2
      have hK0L2 : gc.intervalFireCount (right t) phaseL2.a.val phaseL2.s.val = 0 :=
        intervalFireCount_eq_zero_of_noFire gc (right t)
          (Nat.le_of_lt phaseL2.ha_lt_s) (Nat.le_of_lt phaseL2.s.isLt)
          (fun k hk_ge hk_lt => hno_right_L2 k (by simpa [phaseL2, aL] using hk_ge) hk_lt)
      have hJ1L2 : gc.intervalFireCount (left t) phaseL2.a.val phaseL2.s.val = 1 := by
        exact (normalForm_gap_constraint gc t phaseL2 hnormL2).2.1 hK0L2
      have hlen2L2 : phaseL2.s.val = phaseL2.a.val + 2 := by
        dsimp [phaseL2, aL]
        omega
      rcases one_sided_left_len2_start_ll_or_ec gc t phaseL2 hnormL2 hJ1L2 hK0L2 hlen2L2 with hec | haL_left2
      · exact Or.inl hec
      · let prevL : Fin gc.configs.length := ⟨aL.val + 1, by
          have := phase0.s.isLt
          omega⟩
        have hprevL_eq : prevL.val = aL.val + 1 := by rfl
        have hprevL_left : gc.moverAt prevL = left t := by
          have hprev_eq :
              prevL = ⟨phaseL2.s.val - 1, by
                have := phaseL2.ha_lt_s
                have := phaseL2.s.isLt
                omega⟩ := by
            apply Fin.ext
            dsimp [prevL, phaseL2, aL]
            omega
          have hgap2L2 : phaseL2.s.val - phaseL2.a.val ≥ 2 := by omega
          rw [hprev_eq]
          exact one_sided_normal_prev_left_local_live phaseL2 hnormL2 hJ1L2 hK0L2 hgap2L2
        exact Or.inr ⟨aL, prevL, by
          dsimp [aL]
          omega, by simpa [haL_eq], haL_left2, hprevL_eq, hprevL_left⟩
    have right_continuation_len2_suffix_or_ec_live
        (phase0 : TernaryPhase gc t)
        (hphase0a : phase0.a = k_out)
        (hlong : k_out.val + 2 < phase0.s.val)
        (hkout_right3 : gc.moverAt k_out = right (right (right t)))
        (hphase_branch :
          ∀ k : Fin gc.configs.length,
            k_out.val < k.val → k.val < phase0.s.val →
            gc.moverAt k = right t ∨ gc.moverAt k = right (right t)) :
        hasEntryConflict gc ∨
        ∃ aR prevR : Fin gc.configs.length,
          k_out.val < aR.val ∧
          aR.val + 2 = phase0.s.val ∧
          gc.moverAt aR = right (right t) ∧
          prevR.val = aR.val + 1 ∧
          gc.moverAt prevR = right t := by
      have hJ0K1 := right_continuation_phase_counts_live phase0 hphase0a hlong hkout_right3 hphase_branch
      let aR : Fin gc.configs.length := ⟨phase0.s.val - 2, by
        have := phase0.s.isLt
        omega⟩
      have haR_eq : phase0.s.val = aR.val + 2 := by
        dsimp [aR]
        omega
      have haR_lt_s : aR.val < phase0.s.val := by
        dsimp [aR]
        omega
      have haR_ge_a : phase0.a.val ≤ aR.val := by
        dsimp [aR]
        omega
      have haR_nonmover : gc.moverAt aR ≠ t := phase0.ht_nofire aR haR_ge_a haR_lt_s
      let phaseR2 : TernaryPhase gc t := {
        a := aR
        s := phase0.s
        ha_lt_s := haR_lt_s
        hs_mover := phase0.hs_mover
        ha_nonmover := haR_nonmover
        ht_nofire := by
          intro k hk1 hk2
          exact phase0.ht_nofire k (le_trans haR_ge_a hk1) hk2
      }
      have hnormR2 : isNormalFormGap gc t phaseR2 := hall_normal phaseR2
      have hno_left_R2 :
          ∀ k : Fin gc.configs.length,
            aR.val ≤ k.val → k.val < phase0.s.val → gc.moverAt k ≠ left t := by
        intro k hk1 hk2
        exact noFire_of_intervalFireCount_zero_local_live (left t)
          (show phase0.a.val ≤ phase0.s.val by omega)
          (Nat.le_of_lt phase0.s.isLt) hJ0K1.1 k (le_trans haR_ge_a hk1) hk2
      have hJ0R2 : gc.intervalFireCount (left t) phaseR2.a.val phaseR2.s.val = 0 :=
        intervalFireCount_eq_zero_of_noFire gc (left t)
          (Nat.le_of_lt phaseR2.ha_lt_s) (Nat.le_of_lt phaseR2.s.isLt)
          (fun k hk_ge hk_lt => hno_left_R2 k (by simpa [phaseR2, aR] using hk_ge) hk_lt)
      have hK1R2 : gc.intervalFireCount (right t) phaseR2.a.val phaseR2.s.val = 1 := by
        exact (normalForm_gap_constraint gc t phaseR2 hnormR2).1 hJ0R2
      have hlen2R2 : phaseR2.s.val = phaseR2.a.val + 2 := by
        dsimp [phaseR2, aR]
        omega
      rcases one_sided_right_len2_start_rr_or_ec gc t phaseR2 hnormR2 hJ0R2 hK1R2 hlen2R2 with hec | haR_right2
      · exact Or.inl hec
      · let prevR : Fin gc.configs.length := ⟨aR.val + 1, by
          have := phase0.s.isLt
          omega⟩
        have hprevR_eq : prevR.val = aR.val + 1 := by rfl
        have hprevR_right : gc.moverAt prevR = right t := by
          have hprev_eq :
              prevR = ⟨phaseR2.s.val - 1, by
                have := phaseR2.ha_lt_s
                have := phaseR2.s.isLt
                omega⟩ := by
            apply Fin.ext
            dsimp [prevR, phaseR2, aR]
            omega
          have hgap2R2 : phaseR2.s.val - phaseR2.a.val ≥ 2 := by omega
          rw [hprev_eq]
          exact one_sided_normal_prev_right_local_live phaseR2 hnormR2 hJ0R2 hK1R2 hgap2R2
        exact Or.inr ⟨aR, prevR, by
          dsimp [aR]
          omega, by simpa [haR_eq], haR_right2, hprevR_eq, hprevR_right⟩
    have left_same_prefix_phase_counts
        {j j1 : Fin gc.configs.length}
        (hj1_eq : j1.val = j.val + 1)
        (hj1_left3 : gc.moverAt j1 = left (left (left t)))
        (hj_tail :
          ∀ k : Fin gc.configs.length,
            j.val < k.val →
            gc.moverAt k = left (left (left t)) ∨
              gc.moverAt k = left (left t) ∨
              gc.moverAt k = left t ∨
              gc.moverAt k = t ∨
              gc.moverAt k = right t ∨
              gc.moverAt k = right (right t))
        (hafter : ∃ s : Fin gc.configs.length, j1.val < s.val ∧ gc.moverAt s = t) :
        ∃ phase1 : TernaryPhase gc t,
          phase1.a = j1 ∧
          (∀ k : Fin gc.configs.length,
            phase1.a.val ≤ k.val → k.val < phase1.s.val →
            gc.moverAt k = left (left (left t)) ∨
              gc.moverAt k = left (left t) ∨
              gc.moverAt k = left t) ∧
          gc.intervalFireCount (left t) phase1.a.val phase1.s.val = 1 ∧
          gc.intervalFireCount (right t) phase1.a.val phase1.s.val = 0 := by
      have hleft_ne_self : left t ≠ t := by
        intro hEq
        have : right t = left t := by
          calc
            right t = right (left t) := by rw [hEq]
            _ = t := right_left_eq_self t
            _ = left t := hEq.symm
        exact right_ne_left (by omega) t this
      have hleft2_ne_self : left (left t) ≠ t := by
        intro hEq
        have : left t = right t := by
          calc
            left t = right (left (left t)) := by
              simpa using (right_left_eq_self (left t)).symm
            _ = right t := by rw [hEq]
        exact left_ne_right (by omega) t this
      have hj1_tail :
          ∀ k : Fin gc.configs.length,
            j1.val ≤ k.val →
            gc.moverAt k = left (left (left t)) ∨
              gc.moverAt k = left (left t) ∨
              gc.moverAt k = left t ∨
              gc.moverAt k = t ∨
              gc.moverAt k = right t ∨
              gc.moverAt k = right (right t) := by
        intro k hk_ge
        have hj_lt_k : j.val < k.val := by
          rw [hj1_eq] at hk_ge
          omega
        exact hj_tail k hj_lt_k
      rcases left_tail_one_sided_branch j1 hj1_left3 hj1_tail with hphase | hterm
      · rcases hphase with ⟨phase1, hphase1a, hphase1_branch⟩
        have hK0 : gc.intervalFireCount (right t) phase1.a.val phase1.s.val = 0 := by
          apply intervalFireCount_eq_zero_of_noFire gc (right t)
            (Nat.le_of_lt phase1.ha_lt_s) (Nat.le_of_lt phase1.s.isLt)
          intro k hk_ge hk_lt
          rcases hphase1_branch k hk_ge hk_lt with hk | hk | hk
          · intro hkr
            exact (left3_not_local5 (by omega) t) (Or.inr (Or.inr (Or.inl (Eq.trans hk.symm hkr))))
          · intro hkr
            exact left2_ne_right (by omega) t (Eq.trans hk.symm hkr)
          · intro hkr
            exact left_ne_right (by omega) t (Eq.trans hk.symm hkr)
        have hnorm1 : isNormalFormGap gc t phase1 := hall_normal phase1
        have hJ1 : gc.intervalFireCount (left t) phase1.a.val phase1.s.val = 1 := by
          exact (normalForm_gap_constraint gc t phase1 hnorm1).2.1 hK0
        exact ⟨phase1, hphase1a, hphase1_branch, hJ1, hK0⟩
      · rcases hafter with ⟨s, hs_gt, hs_t⟩
        rcases hterm s (le_of_lt hs_gt) with hs_l3 | hs_l2 | hs_l
        · exact False.elim (left3_ne_self (by omega) t (Eq.trans hs_l3.symm hs_t))
        · exact False.elim (hleft2_ne_self (Eq.trans hs_l2.symm hs_t))
        · exact False.elim (hleft_ne_self (Eq.trans hs_l.symm hs_t))
    have right_same_prefix_phase_counts
        {j j1 : Fin gc.configs.length}
        (hj1_eq : j1.val = j.val + 1)
        (hj1_right3 : gc.moverAt j1 = right (right (right t)))
        (hj_tail :
          ∀ k : Fin gc.configs.length,
            j.val < k.val →
            gc.moverAt k = left (left t) ∨
              gc.moverAt k = left t ∨
              gc.moverAt k = t ∨
              gc.moverAt k = right t ∨
              gc.moverAt k = right (right t) ∨
              gc.moverAt k = right (right (right t)))
        (hafter : ∃ s : Fin gc.configs.length, j1.val < s.val ∧ gc.moverAt s = t) :
        ∃ phase1 : TernaryPhase gc t,
          phase1.a = j1 ∧
          (∀ k : Fin gc.configs.length,
            phase1.a.val ≤ k.val → k.val < phase1.s.val →
              gc.moverAt k = right t ∨
              gc.moverAt k = right (right t) ∨
              gc.moverAt k = right (right (right t))) ∧
          gc.intervalFireCount (left t) phase1.a.val phase1.s.val = 0 ∧
          gc.intervalFireCount (right t) phase1.a.val phase1.s.val = 1 := by
      have hright_ne_self : right t ≠ t := by
        intro hEq
        have : left t = right t := by
          calc
            left t = left (right t) := by rw [hEq]
            _ = t := left_right_eq_self t
            _ = right t := hEq.symm
        exact left_ne_right (by omega) t this
      have hright2_ne_self : right (right t) ≠ t := by
        intro hEq
        have : right t = left t := by
          calc
            right t = left (right (right t)) := by
              simpa using (left_right_eq_self (right t)).symm
            _ = left t := by rw [hEq]
        exact right_ne_left (by omega) t this
      have hj1_tail :
          ∀ k : Fin gc.configs.length,
            j1.val ≤ k.val →
            gc.moverAt k = left (left t) ∨
              gc.moverAt k = left t ∨
              gc.moverAt k = t ∨
              gc.moverAt k = right t ∨
              gc.moverAt k = right (right t) ∨
              gc.moverAt k = right (right (right t)) := by
        intro k hk_ge
        have hj_lt_k : j.val < k.val := by
          rw [hj1_eq] at hk_ge
          omega
        exact hj_tail k hj_lt_k
      rcases right_tail_one_sided_branch j1 hj1_right3 hj1_tail with hphase | hterm
      · rcases hphase with ⟨phase1, hphase1a, hphase1_branch⟩
        have hJ0 : gc.intervalFireCount (left t) phase1.a.val phase1.s.val = 0 := by
          apply intervalFireCount_eq_zero_of_noFire gc (left t)
            (Nat.le_of_lt phase1.ha_lt_s) (Nat.le_of_lt phase1.s.isLt)
          intro k hk_ge hk_lt
          rcases hphase1_branch k hk_ge hk_lt with hk | hk | hk
          · intro hkl
            exact right_ne_left (by omega) t (Eq.trans hk.symm hkl)
          · intro hkl
            exact right2_ne_left (by omega) t (Eq.trans hk.symm hkl)
          · intro hkl
            exact (right3_not_local5 (by omega) t) (Or.inr (Or.inl (Eq.trans hk.symm hkl)))
        have hnorm1 : isNormalFormGap gc t phase1 := hall_normal phase1
        have hK1 : gc.intervalFireCount (right t) phase1.a.val phase1.s.val = 1 := by
          exact (normalForm_gap_constraint gc t phase1 hnorm1).1 hJ0
        exact ⟨phase1, hphase1a, hphase1_branch, hJ0, hK1⟩
      · rcases hafter with ⟨s, hs_gt, hs_t⟩
        rcases hterm s (le_of_lt hs_gt) with hs_r | hs_r2 | hs_r3
        · exact False.elim (hright_ne_self (Eq.trans hs_r.symm hs_t))
        · exact False.elim (hright2_ne_self (Eq.trans hs_r2.symm hs_t))
        · exact False.elim (right3_ne_self (by omega) t (Eq.trans hs_r3.symm hs_t))
    have left_one_sided_phase_len2_suffix_or_ec_live
        (phase : TernaryPhase gc t)
        (hJ1 : gc.intervalFireCount (left t) phase.a.val phase.s.val = 1)
        (hK0 : gc.intervalFireCount (right t) phase.a.val phase.s.val = 0)
        (hlong : phase.a.val + 2 < phase.s.val) :
        hasEntryConflict gc ∨
        ∃ aL prevL : Fin gc.configs.length,
          phase.a.val < aL.val ∧
          aL.val + 2 = phase.s.val ∧
          gc.moverAt aL = left (left t) ∧
          prevL.val = aL.val + 1 ∧
          gc.moverAt prevL = left t := by
      let aL : Fin gc.configs.length := ⟨phase.s.val - 2, by
        have := phase.s.isLt
        omega⟩
      have haL_eq : phase.s.val = aL.val + 2 := by
        dsimp [aL]
        omega
      have haL_lt_s : aL.val < phase.s.val := by
        dsimp [aL]
        omega
      have haL_ge_a : phase.a.val ≤ aL.val := by
        dsimp [aL]
        omega
      have haL_nonmover : gc.moverAt aL ≠ t := phase.ht_nofire aL haL_ge_a haL_lt_s
      let phaseL2 : TernaryPhase gc t := {
        a := aL
        s := phase.s
        ha_lt_s := haL_lt_s
        hs_mover := phase.hs_mover
        ha_nonmover := haL_nonmover
        ht_nofire := by
          intro k hk1 hk2
          exact phase.ht_nofire k (le_trans haL_ge_a hk1) hk2
      }
      have hnormL2 : isNormalFormGap gc t phaseL2 := hall_normal phaseL2
      have hno_right_L2 :
          ∀ k : Fin gc.configs.length,
            aL.val ≤ k.val → k.val < phase.s.val → gc.moverAt k ≠ right t := by
        intro k hk1 hk2
        exact noFire_of_intervalFireCount_zero_local_live (right t)
          (show phase.a.val ≤ phase.s.val by omega)
          (Nat.le_of_lt phase.s.isLt) hK0 k (le_trans haL_ge_a hk1) hk2
      have hK0L2 : gc.intervalFireCount (right t) phaseL2.a.val phaseL2.s.val = 0 :=
        intervalFireCount_eq_zero_of_noFire gc (right t)
          (Nat.le_of_lt phaseL2.ha_lt_s) (Nat.le_of_lt phaseL2.s.isLt)
          (fun k hk_ge hk_lt => hno_right_L2 k (by simpa [phaseL2, aL] using hk_ge) hk_lt)
      have hJ1L2 : gc.intervalFireCount (left t) phaseL2.a.val phaseL2.s.val = 1 := by
        exact (normalForm_gap_constraint gc t phaseL2 hnormL2).2.1 hK0L2
      have hlen2L2 : phaseL2.s.val = phaseL2.a.val + 2 := by
        dsimp [phaseL2, aL]
        omega
      rcases one_sided_left_len2_start_ll_or_ec gc t phaseL2 hnormL2 hJ1L2 hK0L2 hlen2L2 with hec | haL_left2
      · exact Or.inl hec
      · let prevL : Fin gc.configs.length := ⟨aL.val + 1, by
          have := phase.s.isLt
          omega⟩
        have hprevL_eq : prevL.val = aL.val + 1 := by rfl
        have hprevL_left : gc.moverAt prevL = left t := by
          have hprev_eq :
              prevL = ⟨phaseL2.s.val - 1, by
                have := phaseL2.ha_lt_s
                have := phaseL2.s.isLt
                omega⟩ := by
            apply Fin.ext
            dsimp [prevL, phaseL2, aL]
            omega
          have hgap2L2 : phaseL2.s.val - phaseL2.a.val ≥ 2 := by omega
          rw [hprev_eq]
          exact one_sided_normal_prev_left_local_live phaseL2 hnormL2 hJ1L2 hK0L2 hgap2L2
        exact Or.inr ⟨aL, prevL, by
          dsimp [aL]
          omega, by simpa [haL_eq], haL_left2, hprevL_eq, hprevL_left⟩
    have right_one_sided_phase_len2_suffix_or_ec_live
        (phase : TernaryPhase gc t)
        (hJ0 : gc.intervalFireCount (left t) phase.a.val phase.s.val = 0)
        (hK1 : gc.intervalFireCount (right t) phase.a.val phase.s.val = 1)
        (hlong : phase.a.val + 2 < phase.s.val) :
        hasEntryConflict gc ∨
        ∃ aR prevR : Fin gc.configs.length,
          phase.a.val < aR.val ∧
          aR.val + 2 = phase.s.val ∧
          gc.moverAt aR = right (right t) ∧
          prevR.val = aR.val + 1 ∧
          gc.moverAt prevR = right t := by
      let aR : Fin gc.configs.length := ⟨phase.s.val - 2, by
        have := phase.s.isLt
        omega⟩
      have haR_eq : phase.s.val = aR.val + 2 := by
        dsimp [aR]
        omega
      have haR_lt_s : aR.val < phase.s.val := by
        dsimp [aR]
        omega
      have haR_ge_a : phase.a.val ≤ aR.val := by
        dsimp [aR]
        omega
      have haR_nonmover : gc.moverAt aR ≠ t := phase.ht_nofire aR haR_ge_a haR_lt_s
      let phaseR2 : TernaryPhase gc t := {
        a := aR
        s := phase.s
        ha_lt_s := haR_lt_s
        hs_mover := phase.hs_mover
        ha_nonmover := haR_nonmover
        ht_nofire := by
          intro k hk1 hk2
          exact phase.ht_nofire k (le_trans haR_ge_a hk1) hk2
      }
      have hnormR2 : isNormalFormGap gc t phaseR2 := hall_normal phaseR2
      have hno_left_R2 :
          ∀ k : Fin gc.configs.length,
            aR.val ≤ k.val → k.val < phase.s.val → gc.moverAt k ≠ left t := by
        intro k hk1 hk2
        exact noFire_of_intervalFireCount_zero_local_live (left t)
          (show phase.a.val ≤ phase.s.val by omega)
          (Nat.le_of_lt phase.s.isLt) hJ0 k (le_trans haR_ge_a hk1) hk2
      have hJ0R2 : gc.intervalFireCount (left t) phaseR2.a.val phaseR2.s.val = 0 :=
        intervalFireCount_eq_zero_of_noFire gc (left t)
          (Nat.le_of_lt phaseR2.ha_lt_s) (Nat.le_of_lt phaseR2.s.isLt)
          (fun k hk_ge hk_lt => hno_left_R2 k (by simpa [phaseR2, aR] using hk_ge) hk_lt)
      have hK1R2 : gc.intervalFireCount (right t) phaseR2.a.val phaseR2.s.val = 1 := by
        exact (normalForm_gap_constraint gc t phaseR2 hnormR2).1 hJ0R2
      have hlen2R2 : phaseR2.s.val = phaseR2.a.val + 2 := by
        dsimp [phaseR2, aR]
        omega
      rcases one_sided_right_len2_start_rr_or_ec gc t phaseR2 hnormR2 hJ0R2 hK1R2 hlen2R2 with hec | haR_right2
      · exact Or.inl hec
      · let prevR : Fin gc.configs.length := ⟨aR.val + 1, by
          have := phase.s.isLt
          omega⟩
        have hprevR_eq : prevR.val = aR.val + 1 := by rfl
        have hprevR_right : gc.moverAt prevR = right t := by
          have hprev_eq :
              prevR = ⟨phaseR2.s.val - 1, by
                have := phaseR2.ha_lt_s
                have := phaseR2.s.isLt
                omega⟩ := by
            apply Fin.ext
            dsimp [prevR, phaseR2, aR]
            omega
          have hgap2R2 : phaseR2.s.val - phaseR2.a.val ≥ 2 := by omega
          rw [hprev_eq]
          exact one_sided_normal_prev_right_local_live phaseR2 hnormR2 hJ0R2 hK1R2 hgap2R2
        exact Or.inr ⟨aR, prevR, by
          dsimp [aR]
          omega, by simpa [haR_eq], haR_right2, hprevR_eq, hprevR_right⟩
    have left_same_prefix_suffix_position
        {j a1 : Fin gc.configs.length}
        (hj_lt : j.val < k_out.val)
        (hj_lt_a1 : j.val < a1.val)
        (ha1_left2 : gc.moverAt a1 = left (left t))
        (hkout_left3 : gc.moverAt k_out = left (left (left t)))
        (hj_tail :
          ∀ k : Fin gc.configs.length,
            j.val < k.val →
            gc.moverAt k = left (left (left t)) ∨
              gc.moverAt k = left (left t) ∨
              gc.moverAt k = left t ∨
              gc.moverAt k = t ∨
              gc.moverAt k = right t ∨
              gc.moverAt k = right (right t)) :
        k_out.val < a1.val ∨
        ∃ a prev : Fin gc.configs.length,
          a1.val ≤ prev.val ∧
          prev.val + 1 = a.val ∧
          a.val ≤ k_out.val ∧
          gc.moverAt prev = left (left t) ∧
          gc.moverAt a = left (left (left t)) := by
      by_cases ha1_lt_kout : a1.val < k_out.val
      · exact Or.inr <|
          first_left3_after_left2_in_leftsix_tail gc t (by omega) j a1 k_out
            hj_lt_a1 ha1_lt_kout ha1_left2 hkout_left3 hj_tail
      · left
        have ha1_ne_kout : a1.val ≠ k_out.val := by
          intro hEq
          have hEqFin : a1 = k_out := Fin.ext hEq
          exact (left3_not_local5 (by omega) t) (Or.inl (by
            calc
              left (left (left t)) = gc.moverAt k_out := hkout_left3.symm
              _ = gc.moverAt a1 := by rw [← hEqFin]
              _ = left (left t) := ha1_left2))
        omega
    have right_same_prefix_suffix_position
        {j a1 : Fin gc.configs.length}
        (hj_lt : j.val < k_out.val)
        (hj_lt_a1 : j.val < a1.val)
        (ha1_right2 : gc.moverAt a1 = right (right t))
        (hkout_right3 : gc.moverAt k_out = right (right (right t)))
        (hj_tail :
          ∀ k : Fin gc.configs.length,
            j.val < k.val →
            gc.moverAt k = left (left t) ∨
              gc.moverAt k = left t ∨
              gc.moverAt k = t ∨
              gc.moverAt k = right t ∨
              gc.moverAt k = right (right t) ∨
              gc.moverAt k = right (right (right t))) :
        k_out.val < a1.val ∨
        ∃ a prev : Fin gc.configs.length,
          a1.val ≤ prev.val ∧
          prev.val + 1 = a.val ∧
          a.val ≤ k_out.val ∧
          gc.moverAt prev = right (right t) ∧
          gc.moverAt a = right (right (right t)) := by
      by_cases ha1_lt_kout : a1.val < k_out.val
      · exact Or.inr <|
          first_right3_after_right2_in_rightsix_tail gc t (by omega) j a1 k_out
            hj_lt_a1 ha1_lt_kout ha1_right2 hkout_right3 hj_tail
      · left
        have ha1_ne_kout : a1.val ≠ k_out.val := by
          intro hEq
          have hEqFin : a1 = k_out := Fin.ext hEq
          exact (right3_not_local5 (by omega) t) (Or.inr (Or.inr (Or.inr (by
            calc
              right (right (right t)) = gc.moverAt k_out := hkout_right3.symm
              _ = gc.moverAt a1 := by rw [← hEqFin]
              _ = right (right t) := ha1_right2))))
        omega
    have left_same_prefix_short_phase_false
        {j j1 : Fin gc.configs.length}
        (hj1_left3 : gc.moverAt j1 = left (left (left t)))
        (phase1 : TernaryPhase gc t)
        (hphase1a : phase1.a = j1)
        (hJ1_phase1 : gc.intervalFireCount (left t) phase1.a.val phase1.s.val = 1)
        (hK0_phase1 : gc.intervalFireCount (right t) phase1.a.val phase1.s.val = 0)
        (hnot_long : ¬ phase1.a.val + 2 < phase1.s.val) :
        False := by
      have hnorm1 : isNormalFormGap gc t phase1 := hall_normal phase1
      by_cases hlen1 : phase1.s.val = phase1.a.val + 1
      · rcases normal_len1_phase_starts_at_neighbor gc t phase1 hnorm1 hlen1 with hL | hR
        · exact False.elim ((left3_not_local5 (by omega) t) (Or.inr (Or.inl (by
            calc
              left (left (left t)) = gc.moverAt j1 := hj1_left3.symm
              _ = gc.moverAt phase1.a := by rw [← hphase1a]
              _ = left t := hL))))
        · exact False.elim ((left3_not_local5 (by omega) t) (Or.inr (Or.inr (Or.inl (by
            calc
              left (left (left t)) = gc.moverAt j1 := hj1_left3.symm
              _ = gc.moverAt phase1.a := by rw [← hphase1a]
              _ = right t := hR)))))
      · have hsucc_le : phase1.a.val + 1 ≤ phase1.s.val := Nat.succ_le_of_lt phase1.ha_lt_s
        have hlen2 : phase1.s.val = phase1.a.val + 2 := by omega
        rcases one_sided_left_len2_start_ll_or_ec gc t phase1 hnorm1 hJ1_phase1 hK0_phase1 hlen2 with hec | hll
        · exact entryConflict_impossible gc hec
        · exact False.elim ((left3_not_local5 (by omega) t) (Or.inl (by
            calc
              left (left (left t)) = gc.moverAt j1 := hj1_left3.symm
              _ = gc.moverAt phase1.a := by rw [← hphase1a]
              _ = left (left t) := hll)))
    have right_same_prefix_short_phase_false
        {j j1 : Fin gc.configs.length}
        (hj1_right3 : gc.moverAt j1 = right (right (right t)))
        (phase1 : TernaryPhase gc t)
        (hphase1a : phase1.a = j1)
        (hJ0_phase1 : gc.intervalFireCount (left t) phase1.a.val phase1.s.val = 0)
        (hK1_phase1 : gc.intervalFireCount (right t) phase1.a.val phase1.s.val = 1)
        (hnot_long : ¬ phase1.a.val + 2 < phase1.s.val) :
        False := by
      have hnorm1 : isNormalFormGap gc t phase1 := hall_normal phase1
      by_cases hlen1 : phase1.s.val = phase1.a.val + 1
      · rcases normal_len1_phase_starts_at_neighbor gc t phase1 hnorm1 hlen1 with hL | hR
        · exact False.elim ((right3_not_local5 (by omega) t) (Or.inr (Or.inl (by
            calc
              right (right (right t)) = gc.moverAt j1 := hj1_right3.symm
              _ = gc.moverAt phase1.a := by rw [← hphase1a]
              _ = left t := hL))))
        · exact False.elim ((right3_not_local5 (by omega) t) (Or.inr (Or.inr (Or.inl (by
            calc
              right (right (right t)) = gc.moverAt j1 := hj1_right3.symm
              _ = gc.moverAt phase1.a := by rw [← hphase1a]
              _ = right t := hR)))))
      · have hsucc_le : phase1.a.val + 1 ≤ phase1.s.val := Nat.succ_le_of_lt phase1.ha_lt_s
        have hlen2 : phase1.s.val = phase1.a.val + 2 := by omega
        rcases one_sided_right_len2_start_rr_or_ec gc t phase1 hnorm1 hJ0_phase1 hK1_phase1 hlen2 with hec | hrr
        · exact entryConflict_impossible gc hec
        · exact False.elim ((right3_not_local5 (by omega) t) (Or.inr (Or.inr (Or.inr (by
            calc
              right (right (right t)) = gc.moverAt j1 := hj1_right3.symm
              _ = gc.moverAt phase1.a := by rw [← hphase1a]
              _ = right (right t) := hrr)))))
    have left_same_terminal_far_suffix_false
        (phase1 : TernaryPhase gc t)
        {a1 : Fin gc.configs.length}
        (hkout_lt_a1 : k_out.val < a1.val)
        (ha1_eq : a1.val + 2 = phase1.s.val)
        (hterm :
          ∀ k : Fin gc.configs.length,
            k_out.val < k.val →
            gc.moverAt k = left (left t) ∨ gc.moverAt k = left t) :
        False := by
      have hleft_ne_self : left t ≠ t := by
        intro hEq
        have : right t = left t := by
          calc
            right t = right (left t) := by rw [hEq]
            _ = t := right_left_eq_self t
            _ = left t := hEq.symm
        exact right_ne_left (by omega) t this
      have hleft2_ne_self : left (left t) ≠ t := by
        intro hEq
        have : left t = right t := by
          calc
            left t = right (left (left t)) := by
              simpa using (right_left_eq_self (left t)).symm
            _ = right t := by rw [hEq]
        exact left_ne_right (by omega) t this
      have hs_gt_kout : k_out.val < phase1.s.val := by omega
      rcases hterm phase1.s hs_gt_kout with hs_left2 | hs_left
      · exact False.elim (hleft2_ne_self (by
          calc
            left (left t) = gc.moverAt phase1.s := hs_left2.symm
            _ = t := phase1.hs_mover))
      · exact False.elim (hleft_ne_self (by
          calc
            left t = gc.moverAt phase1.s := hs_left.symm
            _ = t := phase1.hs_mover))
    have right_same_terminal_far_suffix_false
        (phase1 : TernaryPhase gc t)
        {a1 : Fin gc.configs.length}
        (hkout_lt_a1 : k_out.val < a1.val)
        (ha1_eq : a1.val + 2 = phase1.s.val)
        (hterm :
          ∀ k : Fin gc.configs.length,
            k_out.val < k.val →
            gc.moverAt k = right t ∨ gc.moverAt k = right (right t)) :
        False := by
      have hright_ne_self : right t ≠ t := by
        intro hEq
        have : left t = right t := by
          calc
            left t = left (right t) := by rw [hEq]
            _ = t := left_right_eq_self t
            _ = right t := hEq.symm
        exact left_ne_right (by omega) t this
      have hright2_ne_self : right (right t) ≠ t := by
        intro hEq
        have : right t = left t := by
          calc
            right t = left (right (right t)) := by
              simpa using (left_right_eq_self (right t)).symm
            _ = left t := by rw [hEq]
        exact right_ne_left (by omega) t this
      have hs_gt_kout : k_out.val < phase1.s.val := by omega
      rcases hterm phase1.s hs_gt_kout with hs_right | hs_right2
      · exact False.elim (hright_ne_self (by
          calc
            right t = gc.moverAt phase1.s := hs_right.symm
            _ = t := phase1.hs_mover))
      · exact False.elim (hright2_ne_self (by
          calc
            right (right t) = gc.moverAt phase1.s := hs_right2.symm
            _ = t := phase1.hs_mover))
    have left_prev_from_left2_of_later_edge
        {j a prev : Fin gc.configs.length}
        (hj_lt_a : j.val < a.val)
        (ha_le_kout : a.val ≤ k_out.val)
        (hprev_succ : prev.val + 1 = a.val)
        (hprev_left2 : gc.moverAt prev = left (left t))
        (ha_left3 : gc.moverAt a = left (left (left t)))
        (hj_tail :
          ∀ k : Fin gc.configs.length,
            j.val < k.val →
            gc.moverAt k = left (left (left t)) ∨
              gc.moverAt k = left (left t) ∨
              gc.moverAt k = left t ∨
              gc.moverAt k = t ∨
              gc.moverAt k = right t ∨
              gc.moverAt k = right (right t)) :
        LeftPrevFromLeft2Residue := by
      refine ⟨a, prev, hprev_succ, ha_le_kout, hprev_left2, ha_left3, ?_⟩
      intro k hk_ge
      exact hj_tail k (by omega)
    have right_prev_from_right2_of_later_edge
        {j a prev : Fin gc.configs.length}
        (hj_lt_a : j.val < a.val)
        (ha_le_kout : a.val ≤ k_out.val)
        (hprev_succ : prev.val + 1 = a.val)
        (hprev_right2 : gc.moverAt prev = right (right t))
        (ha_right3 : gc.moverAt a = right (right (right t)))
        (hj_tail :
          ∀ k : Fin gc.configs.length,
            j.val < k.val →
            gc.moverAt k = left (left t) ∨
              gc.moverAt k = left t ∨
              gc.moverAt k = t ∨
              gc.moverAt k = right t ∨
              gc.moverAt k = right (right t) ∨
              gc.moverAt k = right (right (right t))) :
        RightPrevFromLeft2Residue := by
      refine ⟨a, prev, hprev_succ, ha_le_kout, hprev_right2, ha_right3, ?_⟩
      intro k hk_ge
      exact hj_tail k (by omega)
    have left_same_terminal_after_reduction
        {j j1 k1 : Fin gc.configs.length}
        (hj_lt : j.val < k_out.val)
        (hj1_eq : j1.val = j.val + 1)
        (hj_left4 : gc.moverAt j = left (left (left (left t))))
        (hj1_left3 : gc.moverAt j1 = left (left (left t)))
        (hj_tail :
          ∀ k : Fin gc.configs.length,
            j.val < k.val →
            gc.moverAt k = left (left (left t)) ∨
              gc.moverAt k = left (left t) ∨
              gc.moverAt k = left t ∨
              gc.moverAt k = t ∨
              gc.moverAt k = right t ∨
              gc.moverAt k = right (right t))
        (hkout_left3 : gc.moverAt k_out = left (left (left t)))
        (hk1_eq : k1.val = k_out.val + 1)
        (hk1_left2 : gc.moverAt k1 = left (left t))
        (hterm :
          ∀ k : Fin gc.configs.length,
            k_out.val < k.val →
            gc.moverAt k = left (left t) ∨ gc.moverAt k = left t)
        (hafter : ∃ s : Fin gc.configs.length, j1.val < s.val ∧ gc.moverAt s = t) :
        False ∨ LeftStartedFromLeft2PrefixSameResidue := by
      have hprefix_phase :=
        left_same_prefix_phase_counts hj1_eq hj1_left3 hj_tail hafter
      rcases hprefix_phase with ⟨phase1, hphase1a, hphase1_branch, hJ1_phase1, hK0_phase1⟩
      by_cases hphase1_long : phase1.a.val + 2 < phase1.s.val
      · rcases left_one_sided_phase_len2_suffix_or_ec_live phase1 hJ1_phase1 hK0_phase1 hphase1_long with hec | hprefix_tail
        · exact Or.inl (entryConflict_impossible gc hec)
        · rcases hprefix_tail with ⟨a1, prev1, hphase1_lt_a1, ha1_eq, ha1_left2, hprev1_eq, hprev1_left⟩
          have hj_lt_a1 : j.val < a1.val := by
            have hj1_lt_a1 : j1.val < a1.val := by
              simpa [hphase1a] using hphase1_lt_a1
            rw [hj1_eq] at hj1_lt_a1
            omega
          rcases left_same_prefix_suffix_position hj_lt hj_lt_a1 ha1_left2 hkout_left3 hj_tail with hkout_lt_a1 | hinner
          · exact Or.inl (left_same_terminal_far_suffix_false phase1 hkout_lt_a1 ha1_eq hterm)
          · rcases hinner with ⟨a, prev, ha1_le_prev, hprev_succ, ha_le_kout, hprev_left2, ha_left3⟩
            have hprefix : LeftStartedPrefixSameResidue := by
              exact ⟨hkout_left3, k1, hk1_eq, hk1_left2, j, j1, hj_lt, hj1_eq, hj_left4, hj1_left3, hj_tail⟩
            exact Or.inr ⟨left_prev_from_left2_of_later_edge
              (by
                have : j1.val < a.val := by
                  rw [hj1_eq]
                  omega
                omega)
              ha_le_kout hprev_succ hprev_left2 ha_left3 hj_tail, hprefix⟩
      · exact Or.inl (left_same_prefix_short_phase_false (j := j) hj1_left3 phase1 hphase1a
          hJ1_phase1 hK0_phase1 hphase1_long)
    have right_same_terminal_after_reduction
        {j j1 k1 : Fin gc.configs.length}
        (hj_lt : j.val < k_out.val)
        (hj1_eq : j1.val = j.val + 1)
        (hj_right4 : gc.moverAt j = right (right (right (right t))))
        (hj1_right3 : gc.moverAt j1 = right (right (right t)))
        (hj_tail :
          ∀ k : Fin gc.configs.length,
            j.val < k.val →
            gc.moverAt k = left (left t) ∨
              gc.moverAt k = left t ∨
              gc.moverAt k = t ∨
              gc.moverAt k = right t ∨
              gc.moverAt k = right (right t) ∨
              gc.moverAt k = right (right (right t)))
        (hkout_right3 : gc.moverAt k_out = right (right (right t)))
        (hk1_eq : k1.val = k_out.val + 1)
        (hk1_right2 : gc.moverAt k1 = right (right t))
        (hterm :
          ∀ k : Fin gc.configs.length,
            k_out.val < k.val →
            gc.moverAt k = right t ∨ gc.moverAt k = right (right t))
        (hafter : ∃ s : Fin gc.configs.length, j1.val < s.val ∧ gc.moverAt s = t) :
        False ∨ RightStartedFromLeft2PrefixSameResidue := by
      have hprefix_phase :=
        right_same_prefix_phase_counts hj1_eq hj1_right3 hj_tail hafter
      rcases hprefix_phase with ⟨phase1, hphase1a, hphase1_branch, hJ0_phase1, hK1_phase1⟩
      by_cases hphase1_long : phase1.a.val + 2 < phase1.s.val
      · rcases right_one_sided_phase_len2_suffix_or_ec_live phase1 hJ0_phase1 hK1_phase1 hphase1_long with hec | hprefix_tail
        · exact Or.inl (entryConflict_impossible gc hec)
        · rcases hprefix_tail with ⟨a1, prev1, hphase1_lt_a1, ha1_eq, ha1_right2, hprev1_eq, hprev1_right⟩
          have hj_lt_a1 : j.val < a1.val := by
            have hj1_lt_a1 : j1.val < a1.val := by
              simpa [hphase1a] using hphase1_lt_a1
            rw [hj1_eq] at hj1_lt_a1
            omega
          rcases right_same_prefix_suffix_position hj_lt hj_lt_a1 ha1_right2 hkout_right3 hj_tail with hkout_lt_a1 | hinner
          · exact Or.inl (right_same_terminal_far_suffix_false phase1 hkout_lt_a1 ha1_eq hterm)
          · rcases hinner with ⟨a, prev, ha1_le_prev, hprev_succ, ha_le_kout, hprev_right2, ha_right3⟩
            have hprefix : RightStartedPrefixSameResidue := by
              exact ⟨hkout_right3, k1, hk1_eq, hk1_right2, j, j1, hj_lt, hj1_eq, hj_right4, hj1_right3, hj_tail⟩
            exact Or.inr ⟨right_prev_from_right2_of_later_edge
              (by
                have : j1.val < a.val := by
                  rw [hj1_eq]
                  omega
                omega)
              ha_le_kout hprev_succ hprev_right2 ha_right3 hj_tail, hprefix⟩
      · exact Or.inl (right_same_prefix_short_phase_false (j := j) hj1_right3 phase1 hphase1a
          hJ0_phase1 hK1_phase1 hphase1_long)
    have left_same_phase_after_reduction
        {j j1 k1 : Fin gc.configs.length}
        (hj_lt : j.val < k_out.val)
        (hj1_eq : j1.val = j.val + 1)
        (hj_left4 : gc.moverAt j = left (left (left (left t))))
        (hj1_left3 : gc.moverAt j1 = left (left (left t)))
        (hj_tail :
          ∀ k : Fin gc.configs.length,
            j.val < k.val →
            gc.moverAt k = left (left (left t)) ∨
              gc.moverAt k = left (left t) ∨
              gc.moverAt k = left t ∨
              gc.moverAt k = t ∨
              gc.moverAt k = right t ∨
              gc.moverAt k = right (right t))
        (hkout_left3 : gc.moverAt k_out = left (left (left t)))
        (hk1_eq : k1.val = k_out.val + 1)
        (hk1_left2 : gc.moverAt k1 = left (left t))
        (phase0 : TernaryPhase gc t)
        (hphase0a : phase0.a = k_out)
        (hlong : k_out.val + 2 < phase0.s.val)
        (hphase_branch :
          ∀ k : Fin gc.configs.length,
            k_out.val < k.val → k.val < phase0.s.val →
            gc.moverAt k = left (left t) ∨ gc.moverAt k = left t) :
        False ∨
          LeftStartedFromLeft2PrefixSameResidue ∨
          ∃ phase1 : TernaryPhase gc t, ∃ a1 prev1 : Fin gc.configs.length,
            phase1.a = j1 ∧
            phase1.s = phase0.s ∧
            k_out.val < a1.val ∧
            a1.val + 2 = phase1.s.val ∧
            gc.moverAt a1 = left (left t) ∧
            prev1.val = a1.val + 1 ∧
            gc.moverAt prev1 = left t := by
      have hj1_lt_phase0s : j1.val < phase0.s.val := by
        rw [hj1_eq]
        omega
      have hprefix_phase :=
        left_same_prefix_phase_counts hj1_eq hj1_left3 hj_tail
          ⟨phase0.s, hj1_lt_phase0s, phase0.hs_mover⟩
      rcases hprefix_phase with ⟨phase1, hphase1a, hphase1_branch, hJ1_phase1, hK0_phase1⟩
      by_cases hphase1_long : phase1.a.val + 2 < phase1.s.val
      · rcases left_one_sided_phase_len2_suffix_or_ec_live phase1 hJ1_phase1 hK0_phase1 hphase1_long with hec | hprefix_tail
        · exact Or.inl (entryConflict_impossible gc hec)
        · rcases hprefix_tail with ⟨a1, prev1, hphase1_lt_a1, ha1_eq, ha1_left2, hprev1_eq, hprev1_left⟩
          have hj_lt_a1 : j.val < a1.val := by
            have hj1_lt_a1 : j1.val < a1.val := by
              simpa [hphase1a] using hphase1_lt_a1
            rw [hj1_eq] at hj1_lt_a1
            omega
          rcases left_same_prefix_suffix_position hj_lt hj_lt_a1 ha1_left2 hkout_left3 hj_tail with hkout_lt_a1 | hinner
          · have hphase1s_le_phase0s : phase1.s.val ≤ phase0.s.val := by
              by_contra hgt
              have hphase0s_lt_phase1s : phase0.s.val < phase1.s.val := by omega
              have hj1_le_phase0s : j1.val ≤ phase0.s.val := le_of_lt hj1_lt_phase0s
              exact phase1.ht_nofire phase0.s (by simpa [hphase1a] using hj1_le_phase0s) hphase0s_lt_phase1s phase0.hs_mover
            have hphase1s_eq_phase0s : phase1.s = phase0.s := by
              apply Fin.ext
              have hphase1s_lt_or_eq : phase1.s.val < phase0.s.val ∨ phase1.s.val = phase0.s.val := by omega
              rcases hphase1s_lt_or_eq with hlt | heq
              · exfalso
                have hkout_lt_phase1s : k_out.val < phase1.s.val := by
                  have : k_out.val < a1.val := hkout_lt_a1
                  omega
                exact phase0.ht_nofire phase1.s (by simpa [hphase0a] using le_of_lt hkout_lt_phase1s) hlt phase1.hs_mover
              · exact heq
            exact Or.inr (Or.inr ⟨phase1, a1, prev1, hphase1a, hphase1s_eq_phase0s,
              hkout_lt_a1, ha1_eq, ha1_left2, hprev1_eq, hprev1_left⟩)
          · rcases hinner with ⟨a, prev, ha1_le_prev, hprev_succ, ha_le_kout, hprev_left2, ha_left3⟩
            have hprefix : LeftStartedPrefixSameResidue := by
              exact ⟨hkout_left3, k1, hk1_eq, hk1_left2, j, j1, hj_lt, hj1_eq, hj_left4, hj1_left3, hj_tail⟩
            exact Or.inr (Or.inl ⟨left_prev_from_left2_of_later_edge
              (by
                have : j1.val < a.val := by
                  rw [hj1_eq]
                  omega
                omega)
              ha_le_kout hprev_succ hprev_left2 ha_left3 hj_tail, hprefix⟩)
      · exact Or.inl (left_same_prefix_short_phase_false (j := j) hj1_left3 phase1 hphase1a
          hJ1_phase1 hK0_phase1 hphase1_long)
    have right_same_phase_after_reduction
        {j j1 k1 : Fin gc.configs.length}
        (hj_lt : j.val < k_out.val)
        (hj1_eq : j1.val = j.val + 1)
        (hj_right4 : gc.moverAt j = right (right (right (right t))))
        (hj1_right3 : gc.moverAt j1 = right (right (right t)))
        (hj_tail :
          ∀ k : Fin gc.configs.length,
            j.val < k.val →
            gc.moverAt k = left (left t) ∨
              gc.moverAt k = left t ∨
              gc.moverAt k = t ∨
              gc.moverAt k = right t ∨
              gc.moverAt k = right (right t) ∨
              gc.moverAt k = right (right (right t)))
        (hkout_right3 : gc.moverAt k_out = right (right (right t)))
        (hk1_eq : k1.val = k_out.val + 1)
        (hk1_right2 : gc.moverAt k1 = right (right t))
        (phase0 : TernaryPhase gc t)
        (hphase0a : phase0.a = k_out)
        (hlong : k_out.val + 2 < phase0.s.val)
        (hphase_branch :
          ∀ k : Fin gc.configs.length,
            k_out.val < k.val → k.val < phase0.s.val →
            gc.moverAt k = right t ∨ gc.moverAt k = right (right t)) :
        False ∨
          RightStartedFromLeft2PrefixSameResidue ∨
          ∃ phase1 : TernaryPhase gc t, ∃ a1 prev1 : Fin gc.configs.length,
            phase1.a = j1 ∧
            phase1.s = phase0.s ∧
            k_out.val < a1.val ∧
            a1.val + 2 = phase1.s.val ∧
            gc.moverAt a1 = right (right t) ∧
            prev1.val = a1.val + 1 ∧
            gc.moverAt prev1 = right t := by
      have hj1_lt_phase0s : j1.val < phase0.s.val := by
        rw [hj1_eq]
        omega
      have hprefix_phase :=
        right_same_prefix_phase_counts hj1_eq hj1_right3 hj_tail
          ⟨phase0.s, hj1_lt_phase0s, phase0.hs_mover⟩
      rcases hprefix_phase with ⟨phase1, hphase1a, hphase1_branch, hJ0_phase1, hK1_phase1⟩
      by_cases hphase1_long : phase1.a.val + 2 < phase1.s.val
      · rcases right_one_sided_phase_len2_suffix_or_ec_live phase1 hJ0_phase1 hK1_phase1 hphase1_long with hec | hprefix_tail
        · exact Or.inl (entryConflict_impossible gc hec)
        · rcases hprefix_tail with ⟨a1, prev1, hphase1_lt_a1, ha1_eq, ha1_right2, hprev1_eq, hprev1_right⟩
          have hj_lt_a1 : j.val < a1.val := by
            have hj1_lt_a1 : j1.val < a1.val := by
              simpa [hphase1a] using hphase1_lt_a1
            rw [hj1_eq] at hj1_lt_a1
            omega
          rcases right_same_prefix_suffix_position hj_lt hj_lt_a1 ha1_right2 hkout_right3 hj_tail with hkout_lt_a1 | hinner
          · have hphase1s_le_phase0s : phase1.s.val ≤ phase0.s.val := by
              by_contra hgt
              have hphase0s_lt_phase1s : phase0.s.val < phase1.s.val := by omega
              have hj1_le_phase0s : j1.val ≤ phase0.s.val := le_of_lt hj1_lt_phase0s
              exact phase1.ht_nofire phase0.s (by simpa [hphase1a] using hj1_le_phase0s) hphase0s_lt_phase1s phase0.hs_mover
            have hphase1s_eq_phase0s : phase1.s = phase0.s := by
              apply Fin.ext
              have hphase1s_lt_or_eq : phase1.s.val < phase0.s.val ∨ phase1.s.val = phase0.s.val := by omega
              rcases hphase1s_lt_or_eq with hlt | heq
              · exfalso
                have hkout_lt_phase1s : k_out.val < phase1.s.val := by
                  have : k_out.val < a1.val := hkout_lt_a1
                  omega
                exact phase0.ht_nofire phase1.s (by simpa [hphase0a] using le_of_lt hkout_lt_phase1s) hlt phase1.hs_mover
              · exact heq
            exact Or.inr (Or.inr ⟨phase1, a1, prev1, hphase1a, hphase1s_eq_phase0s,
              hkout_lt_a1, ha1_eq, ha1_right2, hprev1_eq, hprev1_right⟩)
          · rcases hinner with ⟨a, prev, ha1_le_prev, hprev_succ, ha_le_kout, hprev_right2, ha_right3⟩
            have hprefix : RightStartedPrefixSameResidue := by
              exact ⟨hkout_right3, k1, hk1_eq, hk1_right2, j, j1, hj_lt, hj1_eq, hj_right4, hj1_right3, hj_tail⟩
            exact Or.inr (Or.inl ⟨right_prev_from_right2_of_later_edge
              (by
                have : j1.val < a.val := by
                  rw [hj1_eq]
                  omega
                omega)
              ha_le_kout hprev_succ hprev_right2 ha_right3 hj_tail, hprefix⟩)
      · exact Or.inl (right_same_prefix_short_phase_false (j := j) hj1_right3 phase1 hphase1a
          hJ0_phase1 hK1_phase1 hphase1_long)
    have right_phase_from_right3_prefix
        {j : Fin gc.configs.length}
        (hj_lt : j.val < k_out.val)
        (hj_right3 : gc.moverAt j = right (right (right t)))
        (hj_tail :
          ∀ k : Fin gc.configs.length,
            j.val < k.val →
            gc.moverAt k = left (left (left t)) ∨
              gc.moverAt k = left (left t) ∨
              gc.moverAt k = left t ∨
              gc.moverAt k = t ∨
              gc.moverAt k = right t ∨
              gc.moverAt k = right (right t))
        (hkout_left3 : gc.moverAt k_out = left (left (left t))) :
        ∃ phaseR : TernaryPhase gc t,
          phaseR.a = j ∧
          (∀ k : Fin gc.configs.length,
            phaseR.a.val ≤ k.val → k.val < phaseR.s.val →
            gc.moverAt k = right t ∨
              gc.moverAt k = right (right t) ∨
              gc.moverAt k = right (right (right t))) := by
      have hj_nonmover : gc.moverAt j ≠ t := by
        intro hj_t
        exact right3_ne_self (by omega) t (by
          calc
            right (right (right t)) = gc.moverAt j := hj_right3.symm
            _ = t := hj_t)
      have hafter : ∃ s : Fin gc.configs.length, j.val < s.val ∧ gc.moverAt s = t := by
        by_contra hno
        push_neg at hno
        have htail_no_t : ∀ k : Fin gc.configs.length, j.val ≤ k.val → gc.moverAt k ≠ t := by
          intro k hk_ge
          by_cases hk_eq : k = j
          · subst hk_eq
            exact hj_nonmover
          · have hk_gt : j.val < k.val := by
              have hneqv : k.val ≠ j.val := by
                intro hval
                exact hk_eq (Fin.ext hval)
              omega
            exact hno k hk_gt
        have htail6 :
            ∀ k : Fin gc.configs.length,
              j.val < k.val →
              gc.moverAt k = left (left (left t)) ∨
                gc.moverAt k = left (left t) ∨
                gc.moverAt k = left t ∨
                gc.moverAt k = right t ∨
                gc.moverAt k = right (right t) ∨
                gc.moverAt k = right (right (right t)) := by
          intro k hk_gt
          rcases hj_tail k hk_gt with hk | hk | hk | hk | hk | hk
          · exact Or.inl hk
          · exact Or.inr (Or.inl hk)
          · exact Or.inr (Or.inr (Or.inl hk))
          · exfalso
            exact htail_no_t k (le_of_lt hk_gt) hk
          · exact Or.inr (Or.inr (Or.inr (Or.inl hk)))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hk))))
        have hright_tail :
            ∀ k : Fin gc.configs.length,
              j.val ≤ k.val →
              gc.moverAt k = right t ∨
                gc.moverAt k = right (right t) ∨
                gc.moverAt k = right (right (right t)) := by
          refine (last_outside_terminal_tail_one_sided6 gc t (by omega) j
            (Or.inr hj_right3) htail_no_t htail6).elim ?_ id
          intro hleft
          exfalso
          rcases hleft j le_rfl with hj_l3 | hj_l2 | hj_l
          · have hEq : left (left (left t)) = right (right (right t)) :=
              Eq.trans hj_l3.symm hj_right3
            exact False.elim (left3_ne_right3 (by omega) t hEq)
          · have hEq : right (right (right t)) = left (left t) :=
              Eq.trans hj_right3.symm hj_l2
            exact False.elim ((right3_not_local5 (by omega) t) (Or.inl hEq))
          · have hEq : right (right (right t)) = left t :=
              Eq.trans hj_right3.symm hj_l
            exact False.elim ((right3_not_local5 (by omega) t) (Or.inr (Or.inl hEq)))
        have hkout_right := hright_tail k_out (le_of_lt hj_lt)
        rcases hkout_right with hkout_r | hkout_rr | hkout_r3
        · exact False.elim ((left3_not_local5 (by omega) t)
            (Or.inr (Or.inr (Or.inl (by
              calc
                left (left (left t)) = gc.moverAt k_out := hkout_left3.symm
                _ = right t := hkout_r)))))
        · exact False.elim ((left3_not_local5 (by omega) t)
            (Or.inr (Or.inr (Or.inr (by
              calc
                left (left (left t)) = gc.moverAt k_out := hkout_left3.symm
                _ = right (right t) := hkout_rr)))))
        · exact False.elim (left3_ne_right3 (by omega) t (by
            calc
              left (left (left t)) = gc.moverAt k_out := hkout_left3.symm
              _ = right (right (right t)) := hkout_r3))
      obtain ⟨phaseR, hphaseRa⟩ :=
        exists_ternaryPhase_starting_at gc t j hj_nonmover hafter
      refine ⟨phaseR, hphaseRa, ?_⟩
      intro k hk_ge hk_lt
      have htail6 :
          ∀ k : Fin gc.configs.length,
            j.val < k.val →
            k.val < phaseR.s.val →
            gc.moverAt k = left (left (left t)) ∨
              gc.moverAt k = left (left t) ∨
              gc.moverAt k = left t ∨
              gc.moverAt k = right t ∨
              gc.moverAt k = right (right t) ∨
              gc.moverAt k = right (right (right t)) := by
        intro k hk_gt hk_lt
        rcases hj_tail k hk_gt with hk | hk | hk | hk | hk | hk
        · exact Or.inl hk
        · exact Or.inr (Or.inl hk)
        · exact Or.inr (Or.inr (Or.inl hk))
        · exfalso
          exact phaseR.ht_nofire k (by simpa [hphaseRa] using le_of_lt hk_gt) hk_lt hk
        · exact Or.inr (Or.inr (Or.inr (Or.inl hk)))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hk))))
      simpa [hphaseRa] using
        (phase_tail_from_right3_stays_right6 gc t phaseR (by omega) j
          (by simpa [hphaseRa] using (le_rfl : phaseR.a.val ≤ phaseR.a.val))
          (by simpa [hphaseRa] using phaseR.ha_lt_s)
          hj_right3 htail6 k (by simpa [hphaseRa] using hk_ge) hk_lt)
    have right_phase_from_right3_prefix_counts
        {j : Fin gc.configs.length}
        (hj_lt : j.val < k_out.val)
        (hj_right3 : gc.moverAt j = right (right (right t)))
        (hj_tail :
          ∀ k : Fin gc.configs.length,
            j.val < k.val →
            gc.moverAt k = left (left (left t)) ∨
              gc.moverAt k = left (left t) ∨
              gc.moverAt k = left t ∨
              gc.moverAt k = t ∨
              gc.moverAt k = right t ∨
              gc.moverAt k = right (right t))
        (hkout_left3 : gc.moverAt k_out = left (left (left t))) :
        ∃ phaseR : TernaryPhase gc t,
          phaseR.a = j ∧
          (∀ k : Fin gc.configs.length,
            phaseR.a.val ≤ k.val → k.val < phaseR.s.val →
            gc.moverAt k = right t ∨
              gc.moverAt k = right (right t) ∨
              gc.moverAt k = right (right (right t))) ∧
          gc.intervalFireCount (left t) phaseR.a.val phaseR.s.val = 0 ∧
          gc.intervalFireCount (right t) phaseR.a.val phaseR.s.val = 1 := by
      obtain ⟨phaseR, hphaseRa, hright_tail⟩ :=
        right_phase_from_right3_prefix hj_lt hj_right3 hj_tail hkout_left3
      have hJ0 : gc.intervalFireCount (left t) phaseR.a.val phaseR.s.val = 0 := by
        apply intervalFireCount_eq_zero_of_noFire gc (left t)
          (Nat.le_of_lt phaseR.ha_lt_s) (Nat.le_of_lt phaseR.s.isLt)
        intro k hk_ge hk_lt
        rcases hright_tail k hk_ge hk_lt with hk | hk | hk
        · intro hkl
          exact right_ne_left (by omega) t (Eq.trans hk.symm hkl)
        · intro hkl
          exact right2_ne_left (by omega) t (Eq.trans hk.symm hkl)
        · intro hkl
          exact (right3_not_local5 (by omega) t) (Or.inr (Or.inl (Eq.trans hk.symm hkl)))
      have hnormR : isNormalFormGap gc t phaseR := hall_normal phaseR
      have hK1 : gc.intervalFireCount (right t) phaseR.a.val phaseR.s.val = 1 := by
        exact (normalForm_gap_constraint gc t phaseR hnormR).1 hJ0
      exact ⟨phaseR, hphaseRa, hright_tail, hJ0, hK1⟩
    have right_phase_from_right3_prefix_ends_before_kout
        {j : Fin gc.configs.length}
        (hj_lt : j.val < k_out.val)
        (hj_right3 : gc.moverAt j = right (right (right t)))
        (hj_tail :
          ∀ k : Fin gc.configs.length,
            j.val < k.val →
            gc.moverAt k = left (left (left t)) ∨
              gc.moverAt k = left (left t) ∨
              gc.moverAt k = left t ∨
              gc.moverAt k = t ∨
              gc.moverAt k = right t ∨
              gc.moverAt k = right (right t))
        (hkout_left3 : gc.moverAt k_out = left (left (left t))) :
        ∃ phaseR : TernaryPhase gc t,
          phaseR.a = j ∧
          (∀ k : Fin gc.configs.length,
            phaseR.a.val ≤ k.val → k.val < phaseR.s.val →
            gc.moverAt k = right t ∨
              gc.moverAt k = right (right t) ∨
              gc.moverAt k = right (right (right t))) ∧
          gc.intervalFireCount (left t) phaseR.a.val phaseR.s.val = 0 ∧
          gc.intervalFireCount (right t) phaseR.a.val phaseR.s.val = 1 ∧
          phaseR.s.val ≤ k_out.val := by
      obtain ⟨phaseR, hphaseRa, hright_tail, hJ0, hK1⟩ :=
        right_phase_from_right3_prefix_counts hj_lt hj_right3 hj_tail hkout_left3
      have hs_le : phaseR.s.val ≤ k_out.val := by
        by_contra hgt
        have hk_lt_s : k_out.val < phaseR.s.val := by omega
        rcases hright_tail k_out (by simpa [hphaseRa] using le_of_lt hj_lt) hk_lt_s with hk | hk | hk
        · exact (left3_not_local5 (by omega) t) (Or.inr (Or.inr (Or.inl (Eq.trans hkout_left3.symm hk))))
        · exact (left3_not_local5 (by omega) t) (Or.inr (Or.inr (Or.inr (Eq.trans hkout_left3.symm hk))))
        · exact left3_ne_right3 (by omega) t (Eq.trans hkout_left3.symm hk)
      exact ⟨phaseR, hphaseRa, hright_tail, hJ0, hK1, hs_le⟩
    have left_phase_from_left3_prefix
        {j : Fin gc.configs.length}
        (hj_lt : j.val < k_out.val)
        (hj_left3 : gc.moverAt j = left (left (left t)))
        (hj_tail :
          ∀ k : Fin gc.configs.length,
            j.val < k.val →
            gc.moverAt k = left (left t) ∨
              gc.moverAt k = left t ∨
              gc.moverAt k = t ∨
              gc.moverAt k = right t ∨
              gc.moverAt k = right (right t) ∨
              gc.moverAt k = right (right (right t)))
        (hkout_right3 : gc.moverAt k_out = right (right (right t))) :
        ∃ phaseL : TernaryPhase gc t,
          phaseL.a = j ∧
          ∀ k : Fin gc.configs.length,
            phaseL.a.val ≤ k.val → k.val < phaseL.s.val →
            gc.moverAt k = left (left (left t)) ∨
              gc.moverAt k = left (left t) ∨
              gc.moverAt k = left t := by
      have hj_nonmover : gc.moverAt j ≠ t := by
        intro hj_t
        exact left3_ne_self (by omega) t (by
          calc
            left (left (left t)) = gc.moverAt j := hj_left3.symm
            _ = t := hj_t)
      have hafter : ∃ s : Fin gc.configs.length, j.val < s.val ∧ gc.moverAt s = t := by
        by_contra hno
        push_neg at hno
        have htail_no_t : ∀ k : Fin gc.configs.length, j.val ≤ k.val → gc.moverAt k ≠ t := by
          intro k hk_ge
          by_cases hk_eq : k = j
          · subst hk_eq
            exact hj_nonmover
          · have hk_gt : j.val < k.val := by
              have hneqv : k.val ≠ j.val := by
                intro hval
                exact hk_eq (Fin.ext hval)
              omega
            exact hno k hk_gt
        have htail6 :
            ∀ k : Fin gc.configs.length,
              j.val < k.val →
              gc.moverAt k = left (left (left t)) ∨
                gc.moverAt k = left (left t) ∨
                gc.moverAt k = left t ∨
                gc.moverAt k = right t ∨
                gc.moverAt k = right (right t) ∨
                gc.moverAt k = right (right (right t)) := by
          intro k hk_gt
          rcases hj_tail k hk_gt with hk | hk | hk | hk | hk | hk
          · exact Or.inr (Or.inl hk)
          · exact Or.inr (Or.inr (Or.inl hk))
          · exfalso
            exact htail_no_t k (le_of_lt hk_gt) hk
          · exact Or.inr (Or.inr (Or.inr (Or.inl hk)))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hk))))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hk))))
        have hleft_tail :
            ∀ k : Fin gc.configs.length,
              j.val ≤ k.val →
              gc.moverAt k = left (left (left t)) ∨
                gc.moverAt k = left (left t) ∨
                gc.moverAt k = left t := by
          refine (last_outside_terminal_tail_one_sided6 gc t (by omega) j
            (Or.inl hj_left3) htail_no_t htail6).elim id ?_
          intro hright
          exfalso
          rcases hright j le_rfl with hj_r | hj_rr | hj_r3
          · have hEq : left (left (left t)) = right t :=
              Eq.trans hj_left3.symm hj_r
            exact False.elim ((left3_not_local5 (by omega) t) (Or.inr (Or.inr (Or.inl hEq))))
          · have hEq : left (left (left t)) = right (right t) :=
              Eq.trans hj_left3.symm hj_rr
            exact False.elim ((left3_not_local5 (by omega) t) (Or.inr (Or.inr (Or.inr hEq))))
          · have hEq : left (left (left t)) = right (right (right t)) :=
              Eq.trans hj_left3.symm hj_r3
            exact False.elim (left3_ne_right3 (by omega) t hEq)
        have hkout_left := hleft_tail k_out (le_of_lt hj_lt)
        rcases hkout_left with hkout_l3 | hkout_l2 | hkout_l
        · exact False.elim (right3_ne_left3 (by omega) t (by
            calc
              right (right (right t)) = gc.moverAt k_out := hkout_right3.symm
              _ = left (left (left t)) := hkout_l3))
        · exact False.elim ((right3_not_local5 (by omega) t)
            (Or.inl (by
              calc
                right (right (right t)) = gc.moverAt k_out := hkout_right3.symm
                _ = left (left t) := hkout_l2)))
        · exact False.elim ((right3_not_local5 (by omega) t)
            (Or.inr (Or.inl (by
              calc
                right (right (right t)) = gc.moverAt k_out := hkout_right3.symm
                _ = left t := hkout_l))))
      obtain ⟨phaseL, hphaseLa⟩ :=
        exists_ternaryPhase_starting_at gc t j hj_nonmover hafter
      refine ⟨phaseL, hphaseLa, ?_⟩
      intro k hk_ge hk_lt
      have htail6 :
          ∀ k : Fin gc.configs.length,
            j.val < k.val →
            k.val < phaseL.s.val →
            gc.moverAt k = left (left (left t)) ∨
              gc.moverAt k = left (left t) ∨
              gc.moverAt k = left t ∨
              gc.moverAt k = right t ∨
              gc.moverAt k = right (right t) ∨
              gc.moverAt k = right (right (right t)) := by
        intro k hk_gt hk_lt
        rcases hj_tail k hk_gt with hk | hk | hk | hk | hk | hk
        · exact Or.inr (Or.inl hk)
        · exact Or.inr (Or.inr (Or.inl hk))
        · exfalso
          exact phaseL.ht_nofire k (by simpa [hphaseLa] using le_of_lt hk_gt) hk_lt hk
        · exact Or.inr (Or.inr (Or.inr (Or.inl hk)))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hk))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hk))))
      simpa [hphaseLa] using
        (phase_tail_from_left3_stays_left6 gc t phaseL (by omega) j
          (by simpa [hphaseLa] using (le_rfl : phaseL.a.val ≤ phaseL.a.val))
          (by simpa [hphaseLa] using phaseL.ha_lt_s)
          hj_left3 htail6 k (by simpa [hphaseLa] using hk_ge) hk_lt)
    have left_phase_from_left3_prefix_counts
        {j : Fin gc.configs.length}
        (hj_lt : j.val < k_out.val)
        (hj_left3 : gc.moverAt j = left (left (left t)))
        (hj_tail :
          ∀ k : Fin gc.configs.length,
            j.val < k.val →
            gc.moverAt k = left (left t) ∨
              gc.moverAt k = left t ∨
              gc.moverAt k = t ∨
              gc.moverAt k = right t ∨
              gc.moverAt k = right (right t) ∨
              gc.moverAt k = right (right (right t)))
        (hkout_right3 : gc.moverAt k_out = right (right (right t))) :
        ∃ phaseL : TernaryPhase gc t,
          phaseL.a = j ∧
          (∀ k : Fin gc.configs.length,
            phaseL.a.val ≤ k.val → k.val < phaseL.s.val →
            gc.moverAt k = left (left (left t)) ∨
              gc.moverAt k = left (left t) ∨
              gc.moverAt k = left t) ∧
          gc.intervalFireCount (left t) phaseL.a.val phaseL.s.val = 1 ∧
          gc.intervalFireCount (right t) phaseL.a.val phaseL.s.val = 0 := by
      obtain ⟨phaseL, hphaseLa, hleft_tail⟩ :=
        left_phase_from_left3_prefix hj_lt hj_left3 hj_tail hkout_right3
      have hK0 : gc.intervalFireCount (right t) phaseL.a.val phaseL.s.val = 0 := by
        apply intervalFireCount_eq_zero_of_noFire gc (right t)
          (Nat.le_of_lt phaseL.ha_lt_s) (Nat.le_of_lt phaseL.s.isLt)
        intro k hk_ge hk_lt
        rcases hleft_tail k hk_ge hk_lt with hk | hk | hk
        · intro hkr
          exact (left3_not_local5 (by omega) t) (Or.inr (Or.inr (Or.inl (Eq.trans hk.symm hkr))))
        · intro hkr
          exact left2_ne_right (by omega) t (Eq.trans hk.symm hkr)
        · intro hkr
          exact left_ne_right (by omega) t (Eq.trans hk.symm hkr)
      have hnormL : isNormalFormGap gc t phaseL := hall_normal phaseL
      have hJ1 : gc.intervalFireCount (left t) phaseL.a.val phaseL.s.val = 1 := by
        exact (normalForm_gap_constraint gc t phaseL hnormL).2.1 hK0
      exact ⟨phaseL, hphaseLa, hleft_tail, hJ1, hK0⟩
    have left_phase_from_left3_prefix_ends_before_kout
        {j : Fin gc.configs.length}
        (hj_lt : j.val < k_out.val)
        (hj_left3 : gc.moverAt j = left (left (left t)))
        (hj_tail :
          ∀ k : Fin gc.configs.length,
            j.val < k.val →
            gc.moverAt k = left (left t) ∨
              gc.moverAt k = left t ∨
              gc.moverAt k = t ∨
              gc.moverAt k = right t ∨
              gc.moverAt k = right (right t) ∨
              gc.moverAt k = right (right (right t)))
        (hkout_right3 : gc.moverAt k_out = right (right (right t))) :
        ∃ phaseL : TernaryPhase gc t,
          phaseL.a = j ∧
          (∀ k : Fin gc.configs.length,
            phaseL.a.val ≤ k.val → k.val < phaseL.s.val →
            gc.moverAt k = left (left (left t)) ∨
              gc.moverAt k = left (left t) ∨
              gc.moverAt k = left t) ∧
          gc.intervalFireCount (left t) phaseL.a.val phaseL.s.val = 1 ∧
          gc.intervalFireCount (right t) phaseL.a.val phaseL.s.val = 0 ∧
          phaseL.s.val ≤ k_out.val := by
      obtain ⟨phaseL, hphaseLa, hleft_tail, hJ1, hK0⟩ :=
        left_phase_from_left3_prefix_counts hj_lt hj_left3 hj_tail hkout_right3
      have hs_le : phaseL.s.val ≤ k_out.val := by
        by_contra hgt
        have hk_lt_s : k_out.val < phaseL.s.val := by omega
        rcases hleft_tail k_out (by simpa [hphaseLa] using le_of_lt hj_lt) hk_lt_s with hk | hk | hk
        · exact left3_ne_right3 (by omega) t (Eq.trans hk.symm hkout_right3)
        · exact left2_ne_right3 (by omega) t (Eq.trans hk.symm hkout_right3)
        · exact (right3_not_local5 (by omega) t) (Or.inr (Or.inl (Eq.trans hkout_right3.symm hk)))
      exact ⟨phaseL, hphaseLa, hleft_tail, hJ1, hK0, hs_le⟩
    have left_cross_phase_neighbors_or_ec
        {j : Fin gc.configs.length}
        (hj_lt : j.val < k_out.val)
        (hj_right3 : gc.moverAt j = right (right (right t)))
        (hj_tail :
          ∀ k : Fin gc.configs.length,
            j.val < k.val →
            gc.moverAt k = left (left (left t)) ∨
              gc.moverAt k = left (left t) ∨
              gc.moverAt k = left t ∨
              gc.moverAt k = t ∨
              gc.moverAt k = right t ∨
              gc.moverAt k = right (right t))
        (hkout_left3 : gc.moverAt k_out = left (left (left t)))
        (phase0 : TernaryPhase gc t)
        (hphase0a : phase0.a = k_out)
        (hlong : k_out.val + 2 < phase0.s.val)
        (hphase_branch :
          ∀ k : Fin gc.configs.length,
            k_out.val < k.val → k.val < phase0.s.val →
            gc.moverAt k = left (left t) ∨ gc.moverAt k = left t) :
        hasEntryConflict gc ∨
        ∃ phaseR : TernaryPhase gc t, ∃ prevR prevL : Fin gc.configs.length,
          phaseR.a = j ∧
          phaseR.s.val < k_out.val ∧
          prevR.val + 1 = phaseR.s.val ∧
          gc.moverAt prevR = right t ∧
          k_out.val < prevL.val ∧
          prevL.val + 1 = phase0.s.val ∧
          gc.moverAt prevL = left t := by
      obtain ⟨phaseR, hphaseRa, hright_tail, hJ0, hK1, hs_le⟩ :=
        right_phase_from_right3_prefix_ends_before_kout hj_lt hj_right3 hj_tail hkout_left3
      have hs_lt : phaseR.s.val < k_out.val := by
        have hs_ne : phaseR.s ≠ k_out := by
          intro hEq
          exact left3_ne_self (by omega) t (by
            calc
              left (left (left t)) = gc.moverAt k_out := hkout_left3.symm
              _ = gc.moverAt phaseR.s := by rw [← hEq]
              _ = t := phaseR.hs_mover)
        omega
      rcases normal_phase_has_localized_short_suffix_or_ec gc t hall_normal phaseR with hec | hshortR
      · exact Or.inl hec
      · rcases hshortR with ⟨phaseR1, hs1, hlen1, hstart1, _hloc1⟩
        have hprevR_eq : phaseR1.a.val + 1 = phaseR.s.val := by
          simpa [hs1] using hlen1.symm
        have hphaseRa_le_prevR : phaseR.a.val ≤ phaseR1.a.val := by
          have hphaseR_gap : phaseR.a.val < phaseR.s.val := phaseR.ha_lt_s
          omega
        have hprevR_lt_s : phaseR1.a.val < phaseR.s.val := by
          omega
        have hprevR_right : gc.moverAt phaseR1.a = right t := by
          rcases hstart1 with hleft | hright
          · rcases hright_tail phaseR1.a hphaseRa_le_prevR hprevR_lt_s with hR | hR2 | hR3
            · exact False.elim (right_ne_left (by omega) t (Eq.trans hR.symm hleft))
            · exact False.elim (right2_ne_left (by omega) t (Eq.trans hR2.symm hleft))
            · exact False.elim ((right3_not_local5 (by omega) t) (Or.inr (Or.inl (Eq.trans hR3.symm hleft))))
          · exact hright
        rcases normal_phase_has_localized_short_suffix_or_ec gc t hall_normal phase0 with hec | hshortL
        · exact Or.inl hec
        · rcases hshortL with ⟨phaseL1, hs1, hlen1, hstart1, _hloc1⟩
          have hprevL_eq : phaseL1.a.val + 1 = phase0.s.val := by
            simpa [hs1] using hlen1.symm
          have hkout_lt_prevL : k_out.val < phaseL1.a.val := by
            have : k_out.val + 2 < phaseL1.a.val + 1 := by
              simpa [hprevL_eq] using hlong
            omega
          have hprevL_lt_s : phaseL1.a.val < phase0.s.val := by
            omega
          have hprevL_left : gc.moverAt phaseL1.a = left t := by
            rcases hstart1 with hleft | hright
            · exact hleft
            · rcases hphase_branch phaseL1.a hkout_lt_prevL hprevL_lt_s with hL2 | hL
              · exact False.elim (left2_ne_right (by omega) t (Eq.trans hL2.symm hright))
              · exact False.elim (left_ne_right (by omega) t (Eq.trans hL.symm hright))
          exact Or.inr ⟨phaseR, phaseR1.a, phaseL1.a, hphaseRa, hs_lt, hprevR_eq, hprevR_right,
            hkout_lt_prevL, hprevL_eq, hprevL_left⟩
    have left_cross_phase_len2_suffixes_or_ec_live
        {j : Fin gc.configs.length}
        (hj_lt : j.val < k_out.val)
        (hj_right3 : gc.moverAt j = right (right (right t)))
        (hj_tail :
          ∀ k : Fin gc.configs.length,
            j.val < k.val →
            gc.moverAt k = left (left (left t)) ∨
              gc.moverAt k = left (left t) ∨
              gc.moverAt k = left t ∨
              gc.moverAt k = t ∨
              gc.moverAt k = right t ∨
              gc.moverAt k = right (right t))
        (hkout_left3 : gc.moverAt k_out = left (left (left t)))
        (phase0 : TernaryPhase gc t)
        (hphase0a : phase0.a = k_out)
        (hlong : k_out.val + 2 < phase0.s.val)
        (hphase_branch :
          ∀ k : Fin gc.configs.length,
            k_out.val < k.val → k.val < phase0.s.val →
            gc.moverAt k = left (left t) ∨ gc.moverAt k = left t) :
        hasEntryConflict gc ∨
        ∃ phaseR : TernaryPhase gc t, ∃ aR prevR aL prevL : Fin gc.configs.length,
          phaseR.a = j ∧
          phaseR.s.val < k_out.val ∧
          aR.val + 2 = phaseR.s.val ∧
          gc.moverAt aR = right (right t) ∧
          prevR.val = aR.val + 1 ∧
          gc.moverAt prevR = right t ∧
          k_out.val < aL.val ∧
          aL.val + 2 = phase0.s.val ∧
          gc.moverAt aL = left (left t) ∧
          prevL.val = aL.val + 1 ∧
          gc.moverAt prevL = left t := by
      obtain ⟨phaseR, hphaseRa, hright_tail, hJ0, hK1, hs_le⟩ :=
        right_phase_from_right3_prefix_ends_before_kout hj_lt hj_right3 hj_tail hkout_left3
      have hs_lt : phaseR.s.val < k_out.val := by
        have hs_ne : phaseR.s ≠ k_out := by
          intro hEq
          exact left3_ne_self (by omega) t (by
            calc
              left (left (left t)) = gc.moverAt k_out := hkout_left3.symm
              _ = gc.moverAt phaseR.s := by rw [← hEq]
              _ = t := phaseR.hs_mover)
        omega
      have hnormR : isNormalFormGap gc t phaseR := hall_normal phaseR
      have hlen2R : phaseR.s.val ≠ phaseR.a.val + 2 := by
        intro hEq
        rcases one_sided_right_len2_start_rr_or_ec gc t phaseR hnormR hJ0 hK1 hEq with hec | hrr
        · exact False.elim (entryConflict_impossible gc hec)
        · exact right3_not_local5 (by omega) t (Or.inr (Or.inr (Or.inr (by
            calc
              right (right (right t)) = gc.moverAt j := hj_right3.symm
              _ = gc.moverAt phaseR.a := by simpa [hphaseRa]
              _ = right (right t) := hrr))))
      have hphaseR_long : phaseR.a.val + 2 < phaseR.s.val := by
        have hsucc_le : phaseR.a.val + 1 ≤ phaseR.s.val := Nat.succ_le_of_lt phaseR.ha_lt_s
        have hneq : phaseR.a.val + 1 ≠ phaseR.s.val := by
          intro hEq
          have hlen1 : phaseR.s.val = phaseR.a.val + 1 := by omega
          rcases normal_len1_phase_starts_at_neighbor gc t phaseR hnormR hlen1 with hL | hR
          · exact right3_not_local5 (by omega) t
              (Or.inr (Or.inl (Eq.trans hj_right3.symm (by simpa [hphaseRa] using hL))))
          · exact right3_not_local5 (by omega) t
              (Or.inr (Or.inr (Or.inl (Eq.trans hj_right3.symm (by simpa [hphaseRa] using hR)))))
        omega
      let aR : Fin gc.configs.length := ⟨phaseR.s.val - 2, by
        have := phaseR.s.isLt
        omega⟩
      have haR_eq : aR.val + 2 = phaseR.s.val := by
        dsimp [aR]
        omega
      have haR_lt_s : aR.val < phaseR.s.val := by
        dsimp [aR]
        omega
      have haR_ge_a : phaseR.a.val ≤ aR.val := by
        dsimp [aR]
        omega
      have haR_nonmover : gc.moverAt aR ≠ t := phaseR.ht_nofire aR haR_ge_a haR_lt_s
      let phaseR2 : TernaryPhase gc t := {
        a := aR
        s := phaseR.s
        ha_lt_s := haR_lt_s
        hs_mover := phaseR.hs_mover
        ha_nonmover := haR_nonmover
        ht_nofire := by
          intro k hk1 hk2
          exact phaseR.ht_nofire k (le_trans haR_ge_a hk1) hk2
      }
      have hnormR2 : isNormalFormGap gc t phaseR2 := hall_normal phaseR2
      have hno_left_R2 :
          ∀ k : Fin gc.configs.length,
            aR.val ≤ k.val → k.val < phaseR.s.val → gc.moverAt k ≠ left t := by
        intro k hk1 hk2
        exact noFire_of_intervalFireCount_zero_local_live (left t)
          (show phaseR.a.val ≤ phaseR.s.val by omega)
          (Nat.le_of_lt phaseR.s.isLt) hJ0 k (le_trans haR_ge_a hk1) hk2
      have hJ0R2 : gc.intervalFireCount (left t) phaseR2.a.val phaseR2.s.val = 0 :=
        intervalFireCount_eq_zero_of_noFire gc (left t)
          (Nat.le_of_lt phaseR2.ha_lt_s) (Nat.le_of_lt phaseR2.s.isLt)
          (fun k hk_ge hk_lt => hno_left_R2 k (by simpa [phaseR2, aR] using hk_ge) hk_lt)
      have hK1R2 : gc.intervalFireCount (right t) phaseR2.a.val phaseR2.s.val = 1 := by
        exact (normalForm_gap_constraint gc t phaseR2 hnormR2).1 hJ0R2
      have hlen2R2 : phaseR2.s.val = phaseR2.a.val + 2 := by
        dsimp [phaseR2, aR]
        omega
      rcases one_sided_right_len2_start_rr_or_ec gc t phaseR2 hnormR2 hJ0R2 hK1R2 hlen2R2 with hec | haR_right2
      · exact Or.inl hec
      · let prevR : Fin gc.configs.length := ⟨aR.val + 1, by
          have := phaseR.s.isLt
          omega⟩
        have hprevR_eq : prevR.val = aR.val + 1 := by rfl
        have hprevR_right : gc.moverAt prevR = right t := by
          have hprev_eq :
              prevR = ⟨phaseR2.s.val - 1, by
                have := phaseR2.ha_lt_s
                have := phaseR2.s.isLt
                omega⟩ := by
            apply Fin.ext
            dsimp [prevR, phaseR2, aR]
            omega
          have hgap2R2 : phaseR2.s.val - phaseR2.a.val ≥ 2 := by omega
          rw [hprev_eq]
          exact one_sided_normal_prev_right_local_live phaseR2 hnormR2 hJ0R2 hK1R2 hgap2R2
        rcases left_continuation_len2_suffix_or_ec_live phase0 hphase0a hlong hkout_left3 hphase_branch with hec | hpair
        · exact Or.inl hec
        · rcases hpair with ⟨aL, prevL, hkout_lt_aL, haL_eq, haL_left2, hprevL_eq, hprevL_left⟩
          exact Or.inr ⟨phaseR, aR, prevR, aL, prevL, hphaseRa, hs_lt, haR_eq,
            haR_right2, hprevR_eq, hprevR_right, hkout_lt_aL, haL_eq, haL_left2,
            hprevL_eq, hprevL_left⟩
    have right_cross_phase_neighbors_or_ec
        {j : Fin gc.configs.length}
        (hj_lt : j.val < k_out.val)
        (hj_left3 : gc.moverAt j = left (left (left t)))
        (hj_tail :
          ∀ k : Fin gc.configs.length,
            j.val < k.val →
            gc.moverAt k = left (left t) ∨
              gc.moverAt k = left t ∨
              gc.moverAt k = t ∨
              gc.moverAt k = right t ∨
              gc.moverAt k = right (right t) ∨
              gc.moverAt k = right (right (right t)))
        (hkout_right3 : gc.moverAt k_out = right (right (right t)))
        (phase0 : TernaryPhase gc t)
        (hphase0a : phase0.a = k_out)
        (hlong : k_out.val + 2 < phase0.s.val)
        (hphase_branch :
          ∀ k : Fin gc.configs.length,
            k_out.val < k.val → k.val < phase0.s.val →
            gc.moverAt k = right t ∨ gc.moverAt k = right (right t)) :
        hasEntryConflict gc ∨
        ∃ phaseL : TernaryPhase gc t, ∃ prevL prevR : Fin gc.configs.length,
          phaseL.a = j ∧
          phaseL.s.val < k_out.val ∧
          prevL.val + 1 = phaseL.s.val ∧
          gc.moverAt prevL = left t ∧
          k_out.val < prevR.val ∧
          prevR.val + 1 = phase0.s.val ∧
          gc.moverAt prevR = right t := by
      obtain ⟨phaseL, hphaseLa, hleft_tail, hJ1, hK0, hs_le⟩ :=
        left_phase_from_left3_prefix_ends_before_kout hj_lt hj_left3 hj_tail hkout_right3
      have hs_lt : phaseL.s.val < k_out.val := by
        have hs_ne : phaseL.s ≠ k_out := by
          intro hEq
          exact right3_ne_self (by omega) t (by
            calc
              right (right (right t)) = gc.moverAt k_out := hkout_right3.symm
              _ = gc.moverAt phaseL.s := by rw [← hEq]
              _ = t := phaseL.hs_mover)
        omega
      rcases normal_phase_has_localized_short_suffix_or_ec gc t hall_normal phaseL with hec | hshortL
      · exact Or.inl hec
      · rcases hshortL with ⟨phaseL1, hs1, hlen1, hstart1, _hloc1⟩
        have hprevL_eq : phaseL1.a.val + 1 = phaseL.s.val := by
          simpa [hs1] using hlen1.symm
        have hphaseLa_le_prevL : phaseL.a.val ≤ phaseL1.a.val := by
          have hphaseL_gap : phaseL.a.val < phaseL.s.val := phaseL.ha_lt_s
          omega
        have hprevL_lt_s : phaseL1.a.val < phaseL.s.val := by
          omega
        have hprevL_left : gc.moverAt phaseL1.a = left t := by
          rcases hstart1 with hleft | hright
          · exact hleft
          · rcases hleft_tail phaseL1.a hphaseLa_le_prevL hprevL_lt_s with hL3 | hL2 | hL
            · exact False.elim ((left3_not_local5 (by omega) t) (Or.inr (Or.inr (Or.inl (Eq.trans hL3.symm hright)))))
            · exact False.elim (left2_ne_right (by omega) t (Eq.trans hL2.symm hright))
            · exact False.elim (left_ne_right (by omega) t (Eq.trans hL.symm hright))
        rcases normal_phase_has_localized_short_suffix_or_ec gc t hall_normal phase0 with hec | hshortR
        · exact Or.inl hec
        · rcases hshortR with ⟨phaseR1, hs1, hlen1, hstart1, _hloc1⟩
          have hprevR_eq : phaseR1.a.val + 1 = phase0.s.val := by
            simpa [hs1] using hlen1.symm
          have hkout_lt_prevR : k_out.val < phaseR1.a.val := by
            have : k_out.val + 2 < phaseR1.a.val + 1 := by
              simpa [hprevR_eq] using hlong
            omega
          have hprevR_lt_s : phaseR1.a.val < phase0.s.val := by
            omega
          have hprevR_right : gc.moverAt phaseR1.a = right t := by
            rcases hstart1 with hleft | hright
            · rcases hphase_branch phaseR1.a hkout_lt_prevR hprevR_lt_s with hR | hR2
              · exact False.elim (right_ne_left (by omega) t (Eq.trans hR.symm hleft))
              · exact False.elim (right2_ne_left (by omega) t (Eq.trans hR2.symm hleft))
            · exact hright
          exact Or.inr ⟨phaseL, phaseL1.a, phaseR1.a, hphaseLa, hs_lt, hprevL_eq, hprevL_left,
            hkout_lt_prevR, hprevR_eq, hprevR_right⟩
    have right_cross_phase_len2_suffixes_or_ec_live
        {j : Fin gc.configs.length}
        (hj_lt : j.val < k_out.val)
        (hj_left3 : gc.moverAt j = left (left (left t)))
        (hj_tail :
          ∀ k : Fin gc.configs.length,
            j.val < k.val →
            gc.moverAt k = left (left t) ∨
              gc.moverAt k = left t ∨
              gc.moverAt k = t ∨
              gc.moverAt k = right t ∨
              gc.moverAt k = right (right t) ∨
              gc.moverAt k = right (right (right t)))
        (hkout_right3 : gc.moverAt k_out = right (right (right t)))
        (phase0 : TernaryPhase gc t)
        (hphase0a : phase0.a = k_out)
        (hlong : k_out.val + 2 < phase0.s.val)
        (hphase_branch :
          ∀ k : Fin gc.configs.length,
            k_out.val < k.val → k.val < phase0.s.val →
            gc.moverAt k = right t ∨ gc.moverAt k = right (right t)) :
        hasEntryConflict gc ∨
        ∃ phaseL : TernaryPhase gc t, ∃ aL prevL aR prevR : Fin gc.configs.length,
          phaseL.a = j ∧
          phaseL.s.val < k_out.val ∧
          aL.val + 2 = phaseL.s.val ∧
          gc.moverAt aL = left (left t) ∧
          prevL.val = aL.val + 1 ∧
          gc.moverAt prevL = left t ∧
          k_out.val < aR.val ∧
          aR.val + 2 = phase0.s.val ∧
          gc.moverAt aR = right (right t) ∧
          prevR.val = aR.val + 1 ∧
          gc.moverAt prevR = right t := by
      obtain ⟨phaseL, hphaseLa, hleft_tail, hJ1, hK0, hs_le⟩ :=
        left_phase_from_left3_prefix_ends_before_kout hj_lt hj_left3 hj_tail hkout_right3
      have hs_lt : phaseL.s.val < k_out.val := by
        have hs_ne : phaseL.s ≠ k_out := by
          intro hEq
          exact right3_ne_self (by omega) t (by
            calc
              right (right (right t)) = gc.moverAt k_out := hkout_right3.symm
              _ = gc.moverAt phaseL.s := by rw [← hEq]
              _ = t := phaseL.hs_mover)
        omega
      have hnormL : isNormalFormGap gc t phaseL := hall_normal phaseL
      have hlen2L : phaseL.s.val ≠ phaseL.a.val + 2 := by
        intro hEq
        rcases one_sided_left_len2_start_ll_or_ec gc t phaseL hnormL hJ1 hK0 hEq with hec | hll
        · exact False.elim (entryConflict_impossible gc hec)
        · exact left3_not_local5 (by omega) t (Or.inl (by
            calc
              left (left (left t)) = gc.moverAt j := hj_left3.symm
              _ = gc.moverAt phaseL.a := by simpa [hphaseLa]
              _ = left (left t) := hll))
      have hphaseL_long : phaseL.a.val + 2 < phaseL.s.val := by
        have hsucc_le : phaseL.a.val + 1 ≤ phaseL.s.val := Nat.succ_le_of_lt phaseL.ha_lt_s
        have hneq : phaseL.a.val + 1 ≠ phaseL.s.val := by
          intro hEq
          have hlen1 : phaseL.s.val = phaseL.a.val + 1 := by omega
          rcases normal_len1_phase_starts_at_neighbor gc t phaseL hnormL hlen1 with hL | hR
          · exact left3_not_local5 (by omega) t
              (Or.inr (Or.inl (Eq.trans hj_left3.symm (by simpa [hphaseLa] using hL))))
          · exact left3_not_local5 (by omega) t
              (Or.inr (Or.inr (Or.inl (Eq.trans hj_left3.symm (by simpa [hphaseLa] using hR)))))
        omega
      let aL : Fin gc.configs.length := ⟨phaseL.s.val - 2, by
        have := phaseL.s.isLt
        omega⟩
      have haL_eq : phaseL.s.val = aL.val + 2 := by
        dsimp [aL]
        omega
      have haL_lt_s : aL.val < phaseL.s.val := by
        dsimp [aL]
        omega
      have haL_ge_a : phaseL.a.val ≤ aL.val := by
        dsimp [aL]
        omega
      have haL_nonmover : gc.moverAt aL ≠ t := phaseL.ht_nofire aL haL_ge_a haL_lt_s
      let phaseL2 : TernaryPhase gc t := {
        a := aL
        s := phaseL.s
        ha_lt_s := haL_lt_s
        hs_mover := phaseL.hs_mover
        ha_nonmover := haL_nonmover
        ht_nofire := by
          intro k hk1 hk2
          exact phaseL.ht_nofire k (le_trans haL_ge_a hk1) hk2
      }
      have hnormL2 : isNormalFormGap gc t phaseL2 := hall_normal phaseL2
      have hno_right_L2 :
          ∀ k : Fin gc.configs.length,
            aL.val ≤ k.val → k.val < phaseL.s.val → gc.moverAt k ≠ right t := by
        intro k hk1 hk2
        exact noFire_of_intervalFireCount_zero_local_live (right t)
          (show phaseL.a.val ≤ phaseL.s.val by omega)
          (Nat.le_of_lt phaseL.s.isLt) hK0 k (le_trans haL_ge_a hk1) hk2
      have hK0L2 : gc.intervalFireCount (right t) phaseL2.a.val phaseL2.s.val = 0 :=
        intervalFireCount_eq_zero_of_noFire gc (right t)
          (Nat.le_of_lt phaseL2.ha_lt_s) (Nat.le_of_lt phaseL2.s.isLt)
          (fun k hk_ge hk_lt => hno_right_L2 k (by simpa [phaseL2, aL] using hk_ge) hk_lt)
      have hJ1L2 : gc.intervalFireCount (left t) phaseL2.a.val phaseL2.s.val = 1 := by
        exact (normalForm_gap_constraint gc t phaseL2 hnormL2).2.1 hK0L2
      have hlen2L2 : phaseL2.s.val = phaseL2.a.val + 2 := by
        dsimp [phaseL2, aL]
        omega
      rcases one_sided_left_len2_start_ll_or_ec gc t phaseL2 hnormL2 hJ1L2 hK0L2 hlen2L2 with hec | haL_left2
      · exact Or.inl hec
      · let prevL : Fin gc.configs.length := ⟨aL.val + 1, by
          have := phaseL.s.isLt
          omega⟩
        have hprevL_eq : prevL.val = aL.val + 1 := by rfl
        have hprevL_left : gc.moverAt prevL = left t := by
          have hprev_eq :
              prevL = ⟨phaseL2.s.val - 1, by
                have := phaseL2.ha_lt_s
                have := phaseL2.s.isLt
                omega⟩ := by
            apply Fin.ext
            dsimp [prevL, phaseL2, aL]
            omega
          have hgap2L2 : phaseL2.s.val - phaseL2.a.val ≥ 2 := by omega
          rw [hprev_eq]
          exact one_sided_normal_prev_left_local_live phaseL2 hnormL2 hJ1L2 hK0L2 hgap2L2
        have hJ0 : gc.intervalFireCount (left t) phase0.a.val phase0.s.val = 0 := by
          exact right_continuation_phase_counts_live phase0 hphase0a hlong hkout_right3 hphase_branch |>.1
        have hK1 : gc.intervalFireCount (right t) phase0.a.val phase0.s.val = 1 := by
          exact right_continuation_phase_counts_live phase0 hphase0a hlong hkout_right3 hphase_branch |>.2
        let aR : Fin gc.configs.length := ⟨phase0.s.val - 2, by
          have := phase0.s.isLt
          omega⟩
        have haR_eq : phase0.s.val = aR.val + 2 := by
          dsimp [aR]
          omega
        have haR_lt_s : aR.val < phase0.s.val := by
          dsimp [aR]
          omega
        have haR_ge_a : phase0.a.val ≤ aR.val := by
          dsimp [aR]
          omega
        have haR_nonmover : gc.moverAt aR ≠ t := phase0.ht_nofire aR haR_ge_a haR_lt_s
        let phaseR2 : TernaryPhase gc t := {
          a := aR
          s := phase0.s
          ha_lt_s := haR_lt_s
          hs_mover := phase0.hs_mover
          ha_nonmover := haR_nonmover
          ht_nofire := by
            intro k hk1 hk2
            exact phase0.ht_nofire k (le_trans haR_ge_a hk1) hk2
        }
        have hnormR2 : isNormalFormGap gc t phaseR2 := hall_normal phaseR2
        have hno_left_R2 :
            ∀ k : Fin gc.configs.length,
              aR.val ≤ k.val → k.val < phase0.s.val → gc.moverAt k ≠ left t := by
          intro k hk1 hk2
          exact noFire_of_intervalFireCount_zero_local_live (left t)
            (show phase0.a.val ≤ phase0.s.val by omega)
            (Nat.le_of_lt phase0.s.isLt) hJ0 k (le_trans haR_ge_a hk1) hk2
        have hJ0R2 : gc.intervalFireCount (left t) phaseR2.a.val phaseR2.s.val = 0 :=
          intervalFireCount_eq_zero_of_noFire gc (left t)
            (Nat.le_of_lt phaseR2.ha_lt_s) (Nat.le_of_lt phaseR2.s.isLt)
            (fun k hk_ge hk_lt => hno_left_R2 k (by simpa [phaseR2, aR] using hk_ge) hk_lt)
        have hK1R2 : gc.intervalFireCount (right t) phaseR2.a.val phaseR2.s.val = 1 := by
          exact (normalForm_gap_constraint gc t phaseR2 hnormR2).1 hJ0R2
        have hlen2R2 : phaseR2.s.val = phaseR2.a.val + 2 := by
          dsimp [phaseR2, aR]
          omega
        rcases one_sided_right_len2_start_rr_or_ec gc t phaseR2 hnormR2 hJ0R2 hK1R2 hlen2R2 with hec | haR_right2
        · exact Or.inl hec
        · let prevR : Fin gc.configs.length := ⟨aR.val + 1, by
            have := phase0.s.isLt
            omega⟩
          have hprevR_eq : prevR.val = aR.val + 1 := by rfl
          have hprevR_right : gc.moverAt prevR = right t := by
            have hprev_eq :
                prevR = ⟨phaseR2.s.val - 1, by
                  have := phaseR2.ha_lt_s
                  have := phaseR2.s.isLt
                  omega⟩ := by
              apply Fin.ext
              dsimp [prevR, phaseR2, aR]
              omega
            have hgap2R2 : phaseR2.s.val - phaseR2.a.val ≥ 2 := by omega
            rw [hprev_eq]
            exact one_sided_normal_prev_right_local_live phaseR2 hnormR2 hJ0R2 hK1R2 hgap2R2
          exact Or.inr ⟨phaseL, aL, prevL, aR, prevR, hphaseLa, hs_lt, by simpa [haL_eq],
            haL_left2, hprevL_eq, hprevL_left, by
              have hkout_lt_aR : k_out.val < aR.val := by
                dsimp [aR]
                omega
              exact hkout_lt_aR, by simpa [haR_eq], haR_right2, hprevR_eq, hprevR_right⟩
    let LeftSameNoAfterHardResidue : Prop :=
        ∃ j j1 k1 : Fin gc.configs.length,
          j.val < k_out.val ∧
          j1.val = j.val + 1 ∧
          gc.moverAt j = left (left (left (left t))) ∧
          gc.moverAt j1 = left (left (left t)) ∧
          (∀ k : Fin gc.configs.length,
            j.val < k.val →
            gc.moverAt k = left (left (left t)) ∨
              gc.moverAt k = left (left t) ∨
              gc.moverAt k = left t ∨
              gc.moverAt k = t ∨
              gc.moverAt k = right t ∨
              gc.moverAt k = right (right t)) ∧
          gc.moverAt k_out = left (left (left t)) ∧
          k1.val = k_out.val + 1 ∧
          gc.moverAt k1 = left (left t) ∧
          (∀ k : Fin gc.configs.length,
            k_out.val < k.val →
            gc.moverAt k = left (left t) ∨ gc.moverAt k = left t) ∧
          (¬∃ s : Fin gc.configs.length, j1.val < s.val ∧ gc.moverAt s = t)
    let RightSameNoAfterHardResidue : Prop :=
        ∃ j j1 k1 : Fin gc.configs.length,
          j.val < k_out.val ∧
          j1.val = j.val + 1 ∧
          gc.moverAt j = right (right (right (right t))) ∧
          gc.moverAt j1 = right (right (right t)) ∧
          (∀ k : Fin gc.configs.length,
            j.val < k.val →
            gc.moverAt k = left (left t) ∨
              gc.moverAt k = left t ∨
              gc.moverAt k = t ∨
              gc.moverAt k = right t ∨
              gc.moverAt k = right (right t) ∨
              gc.moverAt k = right (right (right t))) ∧
          gc.moverAt k_out = right (right (right t)) ∧
          k1.val = k_out.val + 1 ∧
          gc.moverAt k1 = right (right t) ∧
          (∀ k : Fin gc.configs.length,
            k_out.val < k.val →
            gc.moverAt k = right t ∨ gc.moverAt k = right (right t)) ∧
          (¬∃ s : Fin gc.configs.length, j1.val < s.val ∧ gc.moverAt s = t)
    let LeftSameSharedEndPhaseHardResidue : Prop :=
        ∃ j j1 k1 : Fin gc.configs.length, ∃ phase0 phase1 : TernaryPhase gc t, ∃ a1 prev1 : Fin gc.configs.length,
          j.val < k_out.val ∧
          j1.val = j.val + 1 ∧
          gc.moverAt j = left (left (left (left t))) ∧
          gc.moverAt j1 = left (left (left t)) ∧
          (∀ k : Fin gc.configs.length,
            j.val < k.val →
            gc.moverAt k = left (left (left t)) ∨
              gc.moverAt k = left (left t) ∨
              gc.moverAt k = left t ∨
              gc.moverAt k = t ∨
              gc.moverAt k = right t ∨
              gc.moverAt k = right (right t)) ∧
          gc.moverAt k_out = left (left (left t)) ∧
          k1.val = k_out.val + 1 ∧
          gc.moverAt k1 = left (left t) ∧
          phase0.a = k_out ∧
          k_out.val + 2 < phase0.s.val ∧
          (∀ k : Fin gc.configs.length,
            k_out.val < k.val → k.val < phase0.s.val →
            gc.moverAt k = left (left t) ∨ gc.moverAt k = left t) ∧
          phase1.a = j1 ∧
          phase1.s = phase0.s ∧
          k_out.val < a1.val ∧
          a1.val + 2 = phase1.s.val ∧
          gc.moverAt a1 = left (left t) ∧
          prev1.val = a1.val + 1 ∧
          gc.moverAt prev1 = left t
    let RightSameSharedEndPhaseHardResidue : Prop :=
        ∃ j j1 k1 : Fin gc.configs.length, ∃ phase0 phase1 : TernaryPhase gc t, ∃ a1 prev1 : Fin gc.configs.length,
          j.val < k_out.val ∧
          j1.val = j.val + 1 ∧
          gc.moverAt j = right (right (right (right t))) ∧
          gc.moverAt j1 = right (right (right t)) ∧
          (∀ k : Fin gc.configs.length,
            j.val < k.val →
            gc.moverAt k = left (left t) ∨
              gc.moverAt k = left t ∨
              gc.moverAt k = t ∨
              gc.moverAt k = right t ∨
              gc.moverAt k = right (right t) ∨
              gc.moverAt k = right (right (right t))) ∧
          gc.moverAt k_out = right (right (right t)) ∧
          k1.val = k_out.val + 1 ∧
          gc.moverAt k1 = right (right t) ∧
          phase0.a = k_out ∧
          k_out.val + 2 < phase0.s.val ∧
          (∀ k : Fin gc.configs.length,
            k_out.val < k.val → k.val < phase0.s.val →
            gc.moverAt k = right t ∨ gc.moverAt k = right (right t)) ∧
          phase1.a = j1 ∧
          phase1.s = phase0.s ∧
          k_out.val < a1.val ∧
          a1.val + 2 = phase1.s.val ∧
          gc.moverAt a1 = right (right t) ∧
          prev1.val = a1.val + 1 ∧
          gc.moverAt prev1 = right t
    let LeftCrossPhaseHardResidue : Prop :=
        ∃ j j1 k1 : Fin gc.configs.length, ∃ phase0 phaseR : TernaryPhase gc t,
            ∃ aR prevR aL prevL : Fin gc.configs.length,
          j.val < k_out.val ∧
          j1.val = j.val + 1 ∧
          gc.moverAt j = right (right (right t)) ∧
          gc.moverAt j1 = right (right t) ∧
          (∀ k : Fin gc.configs.length,
            j.val < k.val →
            gc.moverAt k = left (left (left t)) ∨
              gc.moverAt k = left (left t) ∨
              gc.moverAt k = left t ∨
              gc.moverAt k = t ∨
              gc.moverAt k = right t ∨
              gc.moverAt k = right (right t)) ∧
          gc.moverAt k_out = left (left (left t)) ∧
          k1.val = k_out.val + 1 ∧
          gc.moverAt k1 = left (left t) ∧
          phase0.a = k_out ∧
          k_out.val + 2 < phase0.s.val ∧
          (∀ k : Fin gc.configs.length,
            k_out.val < k.val → k.val < phase0.s.val →
            gc.moverAt k = left (left t) ∨ gc.moverAt k = left t) ∧
          phaseR.a = j ∧
          phaseR.s.val < k_out.val ∧
          aR.val + 2 = phaseR.s.val ∧
          gc.moverAt aR = right (right t) ∧
          prevR.val = aR.val + 1 ∧
          gc.moverAt prevR = right t ∧
          k_out.val < aL.val ∧
          aL.val + 2 = phase0.s.val ∧
          gc.moverAt aL = left (left t) ∧
          prevL.val = aL.val + 1 ∧
          gc.moverAt prevL = left t
    let LeftCrossTerminalHardResidue : Prop :=
        ∃ j j1 k1 : Fin gc.configs.length,
          j.val < k_out.val ∧
          j1.val = j.val + 1 ∧
          gc.moverAt j = right (right (right t)) ∧
          gc.moverAt j1 = right (right t) ∧
          (∀ k : Fin gc.configs.length,
            j.val < k.val →
            gc.moverAt k = left (left (left t)) ∨
              gc.moverAt k = left (left t) ∨
              gc.moverAt k = left t ∨
              gc.moverAt k = t ∨
              gc.moverAt k = right t ∨
              gc.moverAt k = right (right t)) ∧
          gc.moverAt k_out = left (left (left t)) ∧
          k1.val = k_out.val + 1 ∧
          gc.moverAt k1 = left (left t) ∧
          (∀ k : Fin gc.configs.length,
            k_out.val < k.val →
            gc.moverAt k = left (left t) ∨ gc.moverAt k = left t)
    let RightCrossPhaseHardResidue : Prop :=
        ∃ j j1 k1 : Fin gc.configs.length, ∃ phase0 phaseL : TernaryPhase gc t,
            ∃ aL prevL aR prevR : Fin gc.configs.length,
          j.val < k_out.val ∧
          j1.val = j.val + 1 ∧
          gc.moverAt j = left (left (left t)) ∧
          gc.moverAt j1 = left (left t) ∧
          (∀ k : Fin gc.configs.length,
            j.val < k.val →
            gc.moverAt k = left (left t) ∨
              gc.moverAt k = left t ∨
              gc.moverAt k = t ∨
              gc.moverAt k = right t ∨
              gc.moverAt k = right (right t) ∨
              gc.moverAt k = right (right (right t))) ∧
          gc.moverAt k_out = right (right (right t)) ∧
          k1.val = k_out.val + 1 ∧
          gc.moverAt k1 = right (right t) ∧
          phase0.a = k_out ∧
          k_out.val + 2 < phase0.s.val ∧
          (∀ k : Fin gc.configs.length,
            k_out.val < k.val → k.val < phase0.s.val →
            gc.moverAt k = right t ∨ gc.moverAt k = right (right t)) ∧
          phaseL.a = j ∧
          phaseL.s.val < k_out.val ∧
          aL.val + 2 = phaseL.s.val ∧
          gc.moverAt aL = left (left t) ∧
          prevL.val = aL.val + 1 ∧
          gc.moverAt prevL = left t ∧
          k_out.val < aR.val ∧
          aR.val + 2 = phase0.s.val ∧
          gc.moverAt aR = right (right t) ∧
          prevR.val = aR.val + 1 ∧
          gc.moverAt prevR = right t
    let RightCrossTerminalHardResidue : Prop :=
        ∃ j j1 k1 : Fin gc.configs.length,
          j.val < k_out.val ∧
          j1.val = j.val + 1 ∧
          gc.moverAt j = left (left (left t)) ∧
          gc.moverAt j1 = left (left t) ∧
          (∀ k : Fin gc.configs.length,
            j.val < k.val →
            gc.moverAt k = left (left t) ∨
              gc.moverAt k = left t ∨
              gc.moverAt k = t ∨
              gc.moverAt k = right t ∨
              gc.moverAt k = right (right t) ∨
              gc.moverAt k = right (right (right t))) ∧
          gc.moverAt k_out = right (right (right t)) ∧
          k1.val = k_out.val + 1 ∧
          gc.moverAt k1 = right (right t) ∧
          (∀ k : Fin gc.configs.length,
            k_out.val < k.val →
            gc.moverAt k = right t ∨ gc.moverAt k = right (right t))
    let LeftSameHardResidue : Prop :=
      LeftStartedFromLeft2PrefixSameRestartResidue ∨
      LeftSameSharedEndPhaseHardResidue ∨
      LeftSameNoAfterHardResidue
    let LeftCrossHardResidue : Prop :=
      LeftCrossPhaseHardResidue ∨ LeftCrossTerminalHardResidue
    let RightCrossHardResidue : Prop :=
      RightCrossPhaseHardResidue ∨ RightCrossTerminalHardResidue
    let RightSameHardResidue : Prop :=
      RightStartedFromLeft2PrefixSameRestartResidue ∨
      RightSameSharedEndPhaseHardResidue ∨
      RightSameNoAfterHardResidue
    have left_same_sharp_reduction :
        LeftSameSharpResidue → False ∨ LeftSameHardResidue := by
      intro h
      rcases h with ⟨j, j1, hj_lt, hj1_eq, hj_left4, hj1_left3, hj_tail, hkout_left3, k1, hk1_eq, hk1_left2, hcont⟩
      have hstart : LeftKoutStartedResidue := by
        refine ⟨hkout_left3, ?_⟩
        rcases hcont with hphase | hterm
        · rcases hphase with ⟨phase0, hphase0a, hlong, hphase_branch⟩
          exact Or.inl ⟨phase0, hphase0a, hlong, hphase_branch, ⟨k1, hk1_eq, hk1_left2⟩⟩
        · exact Or.inr hterm
      rcases hcont with hphase | hterm
      · rcases hphase with ⟨phase0, hphase0a, hlong, hphase_branch⟩
        rcases left_continuation_len2_suffix_or_ec_live phase0 hphase0a hlong hkout_left3 hphase_branch with hec | hpair
        · exact Or.inl (entryConflict_impossible gc hec)
        · rcases hpair with ⟨aL, prevL, hkout_lt_aL, haL_eq, haL_left2, hprevL_eq, hprevL_left⟩
          rcases left_same_phase_after_reduction hj_lt hj1_eq hj_left4 hj1_left3 hj_tail
              hkout_left3 hk1_eq hk1_left2 phase0 hphase0a hlong hphase_branch with
              hfalse | hprefix | hshared
          · exact Or.inl hfalse
          · exact Or.inr (Or.inl ⟨hprefix, hstart⟩)
          · rcases hshared with ⟨phase1, a1, prev1, hphase1a, hphase1s, hkout_lt_a1, ha1_eq, ha1_left2, hprev1_eq, hprev1_left⟩
            exact Or.inr (Or.inr (Or.inl
              ⟨j, j1, k1, phase0, phase1, a1, prev1, hj_lt, hj1_eq, hj_left4, hj1_left3, hj_tail,
                hkout_left3, hk1_eq, hk1_left2, hphase0a, hlong, hphase_branch, hphase1a, hphase1s,
                hkout_lt_a1, ha1_eq, ha1_left2, hprev1_eq, hprev1_left⟩))
      · by_cases hafter : ∃ s : Fin gc.configs.length, j1.val < s.val ∧ gc.moverAt s = t
        · rcases left_same_terminal_after_reduction hj_lt hj1_eq hj_left4 hj1_left3 hj_tail
            hkout_left3 hk1_eq hk1_left2 hterm hafter with hfalse | hprefix
          · exact Or.inl hfalse
          · exact Or.inr (Or.inl ⟨hprefix, hstart⟩)
        · exact Or.inr <| Or.inr <| Or.inr <|
            ⟨j, j1, k1, hj_lt, hj1_eq, hj_left4, hj1_left3, hj_tail,
              hkout_left3, hk1_eq, hk1_left2, hterm, hafter⟩
    have right_same_sharp_reduction :
        RightSameSharpResidue → False ∨ RightSameHardResidue := by
      intro h
      rcases h with ⟨j, j1, hj_lt, hj1_eq, hj_right4, hj1_right3, hj_tail, hkout_right3, k1, hk1_eq, hk1_right2, hcont⟩
      have hstart : RightKoutStartedResidue := by
        refine ⟨hkout_right3, ?_⟩
        rcases hcont with hphase | hterm
        · rcases hphase with ⟨phase0, hphase0a, hlong, hphase_branch⟩
          exact Or.inl ⟨phase0, hphase0a, hlong, hphase_branch, ⟨k1, hk1_eq, hk1_right2⟩⟩
        · exact Or.inr hterm
      rcases hcont with hphase | hterm
      · rcases hphase with ⟨phase0, hphase0a, hlong, hphase_branch⟩
        rcases right_continuation_len2_suffix_or_ec_live phase0 hphase0a hlong hkout_right3 hphase_branch with hec | hpair
        · exact Or.inl (entryConflict_impossible gc hec)
        · rcases hpair with ⟨aR, prevR, hkout_lt_aR, haR_eq, haR_right2, hprevR_eq, hprevR_right⟩
          rcases right_same_phase_after_reduction hj_lt hj1_eq hj_right4 hj1_right3 hj_tail
              hkout_right3 hk1_eq hk1_right2 phase0 hphase0a hlong hphase_branch with
              hfalse | hprefix | hshared
          · exact Or.inl hfalse
          · exact Or.inr (Or.inl ⟨hprefix, hstart⟩)
          · rcases hshared with ⟨phase1, a1, prev1, hphase1a, hphase1s, hkout_lt_a1, ha1_eq, ha1_right2, hprev1_eq, hprev1_right⟩
            exact Or.inr (Or.inr (Or.inl
              ⟨j, j1, k1, phase0, phase1, a1, prev1, hj_lt, hj1_eq, hj_right4, hj1_right3, hj_tail,
                hkout_right3, hk1_eq, hk1_right2, hphase0a, hlong, hphase_branch, hphase1a, hphase1s,
                hkout_lt_a1, ha1_eq, ha1_right2, hprev1_eq, hprev1_right⟩))
      · by_cases hafter : ∃ s : Fin gc.configs.length, j1.val < s.val ∧ gc.moverAt s = t
        · rcases right_same_terminal_after_reduction hj_lt hj1_eq hj_right4 hj1_right3 hj_tail
            hkout_right3 hk1_eq hk1_right2 hterm hafter with hfalse | hprefix
          · exact Or.inl hfalse
          · exact Or.inr (Or.inl ⟨hprefix, hstart⟩)
        · exact Or.inr <| Or.inr <| Or.inr <|
            ⟨j, j1, k1, hj_lt, hj1_eq, hj_right4, hj1_right3, hj_tail,
              hkout_right3, hk1_eq, hk1_right2, hterm, hafter⟩
    have left_cross_sharp_reduction :
        LeftCrossSharpResidue → False ∨ LeftCrossHardResidue := by
      intro h
      rcases h with ⟨j, j1, hj_lt, hj1_eq, hj_right3, hj1_right2, hj_tail, hkout_left3, k1, hk1_eq, hk1_left2, hcont⟩
      rcases hcont with hphase | hterm
      · rcases hphase with ⟨phase0, hphase0a, hlong, hphase_branch⟩
        rcases left_cross_phase_len2_suffixes_or_ec_live hj_lt hj_right3 hj_tail hkout_left3
            phase0 hphase0a hlong hphase_branch with hec | hpair
        · exact Or.inl (entryConflict_impossible gc hec)
        · rcases hpair with ⟨phaseR, aR, prevR, aL, prevL, hphaseRa, hs_lt, haR_eq,
            haR_right2, hprevR_eq, hprevR_right, hkout_lt_aL, haL_eq, haL_left2,
            hprevL_eq, hprevL_left⟩
          exact Or.inr (Or.inl
            ⟨j, j1, k1, phase0, phaseR, aR, prevR, aL, prevL,
              hj_lt, hj1_eq, hj_right3, hj1_right2, hj_tail,
              hkout_left3, hk1_eq, hk1_left2,
              hphase0a, hlong, hphase_branch,
              hphaseRa, hs_lt, haR_eq, haR_right2, hprevR_eq, hprevR_right,
              hkout_lt_aL, haL_eq, haL_left2, hprevL_eq, hprevL_left⟩)
      · exact Or.inr (Or.inr
          ⟨j, j1, k1, hj_lt, hj1_eq, hj_right3, hj1_right2, hj_tail,
            hkout_left3, hk1_eq, hk1_left2, hterm⟩)
    have right_cross_sharp_reduction :
        RightCrossSharpResidue → False ∨ RightCrossHardResidue := by
      intro h
      rcases h with ⟨j, j1, hj_lt, hj1_eq, hj_left3, hj1_left2, hj_tail, hkout_right3, k1, hk1_eq, hk1_right2, hcont⟩
      rcases hcont with hphase | hterm
      · rcases hphase with ⟨phase0, hphase0a, hlong, hphase_branch⟩
        rcases right_cross_phase_len2_suffixes_or_ec_live hj_lt hj_left3 hj_tail hkout_right3
            phase0 hphase0a hlong hphase_branch with hec | hpair
        · exact Or.inl (entryConflict_impossible gc hec)
        · rcases hpair with ⟨phaseL, aL, prevL, aR, prevR, hphaseLa, hs_lt, haL_eq,
            haL_left2, hprevL_eq, hprevL_left, hkout_lt_aR, haR_eq, haR_right2,
            hprevR_eq, hprevR_right⟩
          exact Or.inr (Or.inl
            ⟨j, j1, k1, phase0, phaseL, aL, prevL, aR, prevR,
              hj_lt, hj1_eq, hj_left3, hj1_left2, hj_tail,
              hkout_right3, hk1_eq, hk1_right2,
              hphase0a, hlong, hphase_branch,
              hphaseLa, hs_lt, haL_eq, haL_left2, hprevL_eq, hprevL_left,
              hkout_lt_aR, haR_eq, haR_right2, hprevR_eq, hprevR_right⟩)
      · exact Or.inr (Or.inr
            ⟨j, j1, k1, hj_lt, hj1_eq, hj_left3, hj1_left2, hj_tail,
              hkout_right3, hk1_eq, hk1_right2, hterm⟩)
    have hk_last_not_near_false
        (hk_last : k_out.val + 1 = gc.configs.length)
        (hp_far :
          let p := gc.moverAt k_out
          let i₀ := gc.moverAt ⟨0, gc.configs_length_pos⟩
          ¬(p = i₀ ∨ p = left i₀ ∨ p = right i₀)) :
        False := by
      let hL := gc.configs_length_pos
      let p := gc.moverAt k_out
      let i₀ := gc.moverAt ⟨0, hL⟩
      have hnext_eq : nextIndex gc.configs k_out = ⟨0, hL⟩ := by
        apply Fin.ext
        simp [nextIndex, hk_last, Nat.mod_self]
      have hconfig_eq :
          ∀ (q : Fin sys.rs.n), q ≠ p →
            (gc.configs.get k_out) q = (gc.configs.get ⟨0, hL⟩) q := by
        intro q hq
        have hne : q ≠ gc.moverAt k_out := by
          simpa [p] using hq
        have := gc.state_eq_of_ne_moverAt k_out q hne
        rw [hnext_eq] at this
        exact this.symm
      have hp_far' : ¬(p = i₀ ∨ p = left i₀ ∨ p = right i₀) := by
        simpa [p, i₀, hL] using hp_far
      push_neg at hp_far'
      have hp_ne_i₀ : p ≠ i₀ := hp_far'.1
      have hp_ne_li₀ : p ≠ left i₀ := hp_far'.2.1
      have hp_ne_ri₀ : p ≠ right i₀ := hp_far'.2.2
      have hL_eq := (hconfig_eq (left i₀) (Ne.symm hp_ne_li₀)).symm
      have hS_eq := (hconfig_eq i₀ (Ne.symm hp_ne_i₀)).symm
      have hR_eq := (hconfig_eq (right i₀) (Ne.symm hp_ne_ri₀)).symm
      have hmover_ne : gc.moverAt k_out ≠ i₀ := by
        change p ≠ i₀
        exact hp_ne_i₀
      have hmover_eq : gc.moverAt ⟨0, hL⟩ = i₀ := by
        rfl
      exact entryConflict_impossible gc
        ⟨⟨0, hL⟩, k_out, i₀, hmover_eq, hmover_ne, hL_eq, hS_eq, hR_eq⟩
    have hk_last_near_i0_not_local
        (hp_near :
          let p := gc.moverAt k_out
          let i₀ := gc.moverAt ⟨0, gc.configs_length_pos⟩
          p = i₀ ∨ p = left i₀ ∨ p = right i₀) :
        gc.moverAt ⟨0, gc.configs_length_pos⟩ ≠ left t ∧
        gc.moverAt ⟨0, gc.configs_length_pos⟩ ≠ t ∧
        gc.moverAt ⟨0, gc.configs_length_pos⟩ ≠ right t := by
      let hL := gc.configs_length_pos
      let p := gc.moverAt k_out
      let i₀ := gc.moverAt ⟨0, hL⟩
      have hp_near' : p = i₀ ∨ p = left i₀ ∨ p = right i₀ := by
        simpa [p, i₀, hL] using hp_near
      have hp_not_ll : p ≠ left (left t) := hk_outside.1
      have hp_not_l : p ≠ left t := hk_outside.2.1
      have hp_not_t : p ≠ t := hk_outside.2.2.1
      have hp_not_r : p ≠ right t := hk_outside.2.2.2.1
      have hp_not_rr : p ≠ right (right t) := hk_outside.2.2.2.2
      constructor
      · intro hi0_left
        have hi0_eq : i₀ = left t := by simpa [i₀, hL] using hi0_left
        rcases hp_near' with h | h | h
        · rw [hi0_eq] at h; exact hp_not_l h
        · rw [hi0_eq] at h; exact hp_not_ll h
        · rw [hi0_eq] at h; exact hp_not_t (by simpa [right_left_eq_self] using h)
      constructor
      · intro hi0_t
        have hi0_eq : i₀ = t := by simpa [i₀, hL] using hi0_t
        rcases hp_near' with h | h | h
        · rw [hi0_eq] at h; exact hp_not_t h
        · rw [hi0_eq] at h; exact hp_not_l h
        · rw [hi0_eq] at h; exact hp_not_r h
      · intro hi0_right
        have hi0_eq : i₀ = right t := by simpa [i₀, hL] using hi0_right
        rcases hp_near' with h | h | h
        · rw [hi0_eq] at h; exact hp_not_r h
        · rw [hi0_eq] at h; exact hp_not_t (by simpa [left_right_eq_self] using h)
        · rw [hi0_eq] at h; exact hp_not_rr h
    have hk_last_first_local_t_false
        (hk_last : k_out.val + 1 = gc.configs.length)
        (hp_near :
          let p := gc.moverAt k_out
          let i₀ := gc.moverAt ⟨0, gc.configs_length_pos⟩
          p = i₀ ∨ p = left i₀ ∨ p = right i₀)
        {s : Fin gc.configs.length}
        (hs_t : gc.moverAt s = t)
        (hs_first_local :
          ∀ k : Fin gc.configs.length,
            k.val < s.val →
            gc.moverAt k ≠ left t ∧ gc.moverAt k ≠ t ∧ gc.moverAt k ≠ right t) :
        False := by
      let hL := gc.configs_length_pos
      let p := gc.moverAt k_out
      let i₀ := gc.moverAt ⟨0, hL⟩
      have hnext_eq : nextIndex gc.configs k_out = ⟨0, hL⟩ := by
        apply Fin.ext
        simp [nextIndex, hk_last, Nat.mod_self]
      have hconfig_eq :
          ∀ (q : Fin sys.rs.n), q ≠ p →
            (gc.configs.get k_out) q = (gc.configs.get ⟨0, hL⟩) q := by
        intro q hq
        have hne : q ≠ gc.moverAt k_out := by
          simpa [p] using hq
        have := gc.state_eq_of_ne_moverAt k_out q hne
        rw [hnext_eq] at this
        exact this.symm
      have hi0_not_local : i₀ ≠ left t ∧ i₀ ≠ t ∧ i₀ ≠ right t :=
        hk_last_near_i0_not_local hp_near
      have hs_ne_zero : s.val ≠ 0 := by
        intro hs0
        have hs_eq0 : s = ⟨0, hL⟩ := Fin.ext hs0
        exact hi0_not_local.2.1 (by
          calc
            i₀ = gc.moverAt ⟨0, hL⟩ := rfl
            _ = gc.moverAt s := by rw [← hs_eq0]
            _ = t := hs_t)
      have hs_pos : 0 < s.val := by omega
      have hL_0s : (gc.configs.get ⟨0, hL⟩) (left t) = (gc.configs.get s) (left t) := by
        exact configVal_eq_of_noFire_between gc (left t) 0 s.val (by omega) s.isLt
          (fun k _ hk_lt => (hs_first_local k hk_lt).1)
      have hS_0s : (gc.configs.get ⟨0, hL⟩) t = (gc.configs.get s) t := by
        exact configVal_eq_of_noFire_between gc t 0 s.val (by omega) s.isLt
          (fun k _ hk_lt => (hs_first_local k hk_lt).2.1)
      have hR_0s : (gc.configs.get ⟨0, hL⟩) (right t) = (gc.configs.get s) (right t) := by
        exact configVal_eq_of_noFire_between gc (right t) 0 s.val (by omega) s.isLt
          (fun k _ hk_lt => (hs_first_local k hk_lt).2.2)
      have hL_sk : (gc.configs.get s) (left t) = (gc.configs.get k_out) (left t) := by
        calc
          (gc.configs.get s) (left t) = (gc.configs.get ⟨0, hL⟩) (left t) := hL_0s.symm
          _ = (gc.configs.get k_out) (left t) := (hconfig_eq (left t) (by
            intro hEq
            exact hk_outside.2.1 hEq.symm)).symm
      have hS_sk : (gc.configs.get s) t = (gc.configs.get k_out) t := by
        calc
          (gc.configs.get s) t = (gc.configs.get ⟨0, hL⟩) t := hS_0s.symm
          _ = (gc.configs.get k_out) t := (hconfig_eq t (by
            intro hEq
            exact hk_outside.2.2.1 hEq.symm)).symm
      have hR_sk : (gc.configs.get s) (right t) = (gc.configs.get k_out) (right t) := by
        calc
          (gc.configs.get s) (right t) = (gc.configs.get ⟨0, hL⟩) (right t) := hR_0s.symm
          _ = (gc.configs.get k_out) (right t) := (hconfig_eq (right t) (by
            intro hEq
            exact hk_outside.2.2.2.1 hEq.symm)).symm
      exact entryConflict_impossible gc
        ⟨s, k_out, t, hs_t, hk_outside.2.2.1, hL_sk, hS_sk, hR_sk⟩
    have hk_last_near_false
        (hk_last : k_out.val + 1 = gc.configs.length)
        (hp_near :
          let p := gc.moverAt k_out
          let i₀ := gc.moverAt ⟨0, gc.configs_length_pos⟩
          p = i₀ ∨ p = left i₀ ∨ p = right i₀) :
        False := by
      let hL := gc.configs_length_pos
      let i₀ := gc.moverAt ⟨0, hL⟩
      have hp_near' :
          gc.moverAt k_out = i₀ ∨
            gc.moverAt k_out = left i₀ ∨
            gc.moverAt k_out = right i₀ := by
        simpa [i₀, hL] using hp_near
      have near_i0_violates_normal :
          ∀ (p : Fin sys.rs.n),
            p = i₀ ∨ p = left i₀ ∨ p = right i₀ →
            gc.moverAt k_out = p →
            False := by
        sorry
      exact near_i0_violates_normal (gc.moverAt k_out) hp_near' rfl
    have hard_residue_boundary_composition_false :
        LeftSameHardResidue ∨ LeftCrossHardResidue ∨
          RightCrossHardResidue ∨ RightSameHardResidue → False := by
      intro hhard
      sorry
    have hard_endgame_false :
        (k_out.val + 1 = gc.configs.length) ∨
        LeftSameHardResidue ∨ LeftCrossHardResidue ∨ RightCrossHardResidue ∨ RightSameHardResidue → False := by
      -- Remaining hard core:
      -- 0. last-step outside branch
      -- 1. same-start left2-prefix residue closure
      -- 2. same-start shared-end phase closure
      -- 3. same-start no-later-t terminal closure
      -- 4. cross-start contradictions
      intro hhard
      rcases hhard with hk_last | hleft_same | hleft_cross | hright_cross | hright_same
      · by_cases hp_near :
          let p := gc.moverAt k_out
          let i₀ := gc.moverAt ⟨0, gc.configs_length_pos⟩
          p = i₀ ∨ p = left i₀ ∨ p = right i₀
        · exact hk_last_near_false hk_last hp_near
        · exact hk_last_not_near_false hk_last hp_near
      · exact hard_residue_boundary_composition_false (Or.inl hleft_same)
      · exact hard_residue_boundary_composition_false (Or.inr (Or.inl hleft_cross))
      · exact hard_residue_boundary_composition_false (Or.inr (Or.inr (Or.inl hright_cross)))
      · exact hard_residue_boundary_composition_false (Or.inr (Or.inr (Or.inr hright_same)))
    rcases hresidue_started_prefix_restart_phase_or_terminal_prefix_sharp_split with
      hk_last | hLPS | hLPX | hLTS | hLTX | hRPX | hRPS | hRTX | hRTS
    · exact hard_endgame_false (Or.inl hk_last)
    · rcases left_same_sharp_reduction (hleft_same_sharp (Or.inl hLPS)) with hfalse | hhard
      · exact hfalse
      · exact hard_endgame_false (Or.inr (Or.inl hhard))
    · rcases left_cross_sharp_reduction (hleft_cross_sharp (Or.inl hLPX)) with hfalse | hhard
      · exact hfalse
      · exact hard_endgame_false (Or.inr (Or.inr (Or.inl hhard)))
    · rcases left_same_sharp_reduction (hleft_same_sharp (Or.inr hLTS)) with hfalse | hhard
      · exact hfalse
      · exact hard_endgame_false (Or.inr (Or.inl hhard))
    · rcases left_cross_sharp_reduction (hleft_cross_sharp (Or.inr hLTX)) with hfalse | hhard
      · exact hfalse
      · exact hard_endgame_false (Or.inr (Or.inr (Or.inl hhard)))
    · rcases right_cross_sharp_reduction (hright_cross_sharp (Or.inl hRPX)) with hfalse | hhard
      · exact hfalse
      · exact hard_endgame_false (Or.inr (Or.inr (Or.inr (Or.inl hhard))))
    · rcases right_same_sharp_reduction (hright_same_sharp (Or.inl hRPS)) with hfalse | hhard
      · exact hfalse
      · exact hard_endgame_false (Or.inr (Or.inr (Or.inr (Or.inr hhard))))
    · rcases right_cross_sharp_reduction (hright_cross_sharp (Or.inr hRTX)) with hfalse | hhard
      · exact hfalse
      · exact hard_endgame_false (Or.inr (Or.inr (Or.inr (Or.inl hhard))))
    · rcases right_same_sharp_reduction (hright_same_sharp (Or.inr hRTS)) with hfalse | hhard
      · exact hfalse
      · exact hard_endgame_false (Or.inr (Or.inr (Or.inr (Or.inr hhard))))

end LeanMn
