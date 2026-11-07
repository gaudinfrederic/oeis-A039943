import A007770Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

/-- Certificat orbites : tout n ∈ [1,99] atteint S = {1} ∪ 8-cycle
    en ≤ 30 pas (verifie VM : 0 echec). -/
theorem cert_orbits770 :
    (List.range' 1 99).all (fun n => reachesS 30 n) = true := by
  decide

/-- Certificat descente : sqSum n < n pour n ∈ [100,999]
    (verifie VM : 0 echec). -/
theorem cert_descent770 :
    (List.range 900).all
      (fun i => decide (sqSum (i + 100) < i + 100)) = true := by
  decide
