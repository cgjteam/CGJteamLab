import CGJteamLab.Wyler.HilbertWylerMetric
import CGJteamLab.Wyler.HilbertWylerPlanes
import CGJteamLab.Hilbert3DPlanePerpendicular

/-!
# Hilbert-Wyler perpendicular-plane compatibility module

The Euclid XI.Def.4 definition of perpendicular planes now has its canonical
home in

    CGJteamLab.Hilbert3DPlanePerpendicular

This compatibility module retains the established Wyler helper API required by
the existing Book XI development:

* `HilbertWylerMetric` provides the reusable XI.4 metric helpers and ambient
  line-perpendicularity symmetry;
* `HilbertWylerPlanes` provides the Wyler plane-normal/XI.14 helper layer;
* `Hilbert3DPlanePerpendicular` provides the neutral XI.Def.4 definitions.

No perpendicular-plane definition is duplicated here.
-/
