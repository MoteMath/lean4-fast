import DownstreamBench.Prelude

namespace DownstreamBench.Verify

theorem omega_interval_add (lo₁ hi₁ lo₂ hi₂ x y : Int)
    (hx : lo₁ ≤ x ∧ x ≤ hi₁) (hy : lo₂ ≤ y ∧ y ≤ hi₂) :
    lo₁ + lo₂ ≤ x + y ∧ x + y ≤ hi₁ + hi₂ := by
  omega

theorem omega_interval_sub (lo₁ hi₁ lo₂ hi₂ x y : Int)
    (hx : lo₁ ≤ x ∧ x ≤ hi₁) (hy : lo₂ ≤ y ∧ y ≤ hi₂) :
    lo₁ - hi₂ ≤ x - y ∧ x - y ≤ hi₁ - lo₂ := by
  omega

theorem omega_ring_buffer_wrap (cap head len i : Nat)
    (hcap : cap > 0) (hlen : len ≤ cap) (hhead : head < cap) (hi : i < len) :
    (head + i) % cap < cap ∧ head + i < 2 * cap := by
  refine ⟨Nat.mod_lt _ hcap, by omega⟩

theorem omega_scheduler_load_balance (w₁ w₂ w₃ w₄ total : Nat)
    (ht : w₁ + w₂ + w₃ + w₄ = total)
    (h1 : w₁ ≤ w₂ + 2) (h2 : w₂ ≤ w₃ + 2) (h3 : w₃ ≤ w₄ + 2) (_h4 : w₄ ≤ w₁ + 2) :
    4 * w₁ ≤ total + 12 ∧ total ≤ 4 * w₄ + 12 := by
  omega

theorem omega_linear_system_1 (a b c d : Int)
    (h1 : 2 * a + b ≤ 10) (h2 : b ≥ 3) (h3 : c = a + 1) (h4 : d ≥ c) :
    2 * c ≤ 9 ∧ d + b ≥ a + 4 := by
  omega

theorem omega_array_slice_bounds (off len cap idx : Nat)
    (h1 : off + len ≤ cap) (h2 : idx < len) :
    off + idx < cap ∧ off + idx ≥ off := by
  omega

theorem omega_nat_div_mod_partition (n k : Nat) (hk : k = 8) :
    n = 8 * (n / k) + n % k ∧ n % k < 8 := by
  subst hk
  omega

theorem omega_two_level_tiling (tileR tileC r c : Nat)
    (htr : tileR = 16) (htc : tileC = 16) :
    (r / tileR) * tileR ≤ r ∧ r < (r / tileR + 1) * tileR ∧
    (c / tileC) * tileC ≤ c ∧ c < (c / tileC + 1) * tileC := by
  subst htr; subst htc
  omega

theorem omega_budget_conservation (gpu cpu deleg total : Nat)
    (h1 : gpu + cpu + deleg = total) (h2 : gpu ≥ cpu) (h3 : deleg = 0) :
    2 * cpu ≤ total ∧ 2 * gpu ≥ total := by
  omega

theorem omega_memory_ceiling (workers rss_mb max_mb : Nat)
    (hw : workers = 96) (hr : rss_mb ≤ 40) (hm : max_mb = 128000) :
    workers * rss_mb + 2048 < max_mb := by
  subst hw
  omega

end DownstreamBench.Verify
