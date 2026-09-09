import CGJteamLab.Coxeter.E4NormalParallel

/-!
# E4 hyperplane common-plane compatibility module

The durable common-plane API now lives in `E4NormalParallel`.

This wrapper is intentionally declaration-free.  Existing imports of
`E4HyperplaneCommonPlane` continue to expose:

* `hyperplaneGeo4_plane_through_point_avoiding_point_corrected`;
* `hilbert4D_two_hyperplanes_common_plane_through_two_points_corrected`.

No workshop `AffineFlat4D_testNN` module is imported.
-/
