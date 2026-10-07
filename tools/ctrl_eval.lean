import Srg154.Certificates
open Srg154
-- admissible pairs for m <= 110 according to the paper's exhaustive deciders (Computation comp:adm)
def admKnown : List (ℤ × ℤ) := [(33,22),(66,4),(84,5),(87,18),(89,6),(93,2),(98,7),(100,4),(101,5),
  (102,0),(102,17),(103,3),(104,1),(104,16),(106,6),(110,2),(110,15)]
#eval admKnown.map (fun p => (p, forbiddenCheck p.1 p.2))
-- how many m <= 110 does the Lean checker certify as wholly forbidden (all l)? compare: paper says all but the 14 norms above
def lmax (m : ℤ) : ℕ := ((List.range 60).filter (fun L => decide (3 * (L:ℤ)^2 ≤ 44 * m))).length - 1
#eval ((List.range 111).filter (fun m => m ≥ 1 && !(normCheck m (lmax m)))).map (fun m => (m, ((List.range (lmax m + 1)).filter (fun l => !forbiddenCheck m l))))
