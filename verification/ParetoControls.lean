import SoftwareIsQuantifiable.Pareto
open SoftwareIsQuantifiable.Pareto
#guard admitted (1,10) [(1,10),(10,1)] == [(1,10)]
#guard admitted (10,10) [(1,10),(10,1),(10,10),(11,0)] == [(1,10),(10,1),(10,10)]
#guard acceptsRelease 1 1 { qualified := [1,2] } { offered := [1,2] } (10,10) (10,10)
#guard !(acceptsRelease 1 2 { qualified := [1,2] } { offered := [1,2] } (10,10) (1,1))
#guard !(acceptsRelease 1 1 { qualified := [1,2] } { offered := [1] } (10,10) (1,1))
#guard !(acceptsRelease 1 1 { qualified := [1,2] } { offered := [1,2] } (10,10) (11,1))
#guard !(acceptsRelease 1 1 { qualified := [1,2] } { offered := [1,2] } (10,10) (1,11))
#guard acceptsRelease 1 1 { qualified := [1,2] } { offered := [1,2,3] } (10,10) (1,1)
#guard !(acceptsRelease 1 1 { qualified := [1,2] } { offered := [] } (10,10) (1,1))
example : ¬ dominates (1,10) (10,1) := by simp [dominates]
example : ¬ dominates (10,1) (1,10) := by simp [dominates]
example : noWorse (1,10) (1,10) := by simp [noWorse]
example : admitted (1,1) [(2,2)] = [] := by decide
