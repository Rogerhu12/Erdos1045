import RiemannAuditPort
import Mathlib.Analysis.Complex.OpenMapping
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Calculus.MeanValue

open Set Function Filter Metric
open scoped Topology

namespace RiemannBiholomorphic

theorem not_eventually_constant_of_injOn {f : ℂ → ℂ} {U : Set ℂ} {x : ℂ}
    (hU : IsOpen U) (hinj : InjOn f U) (hx : x ∈ U) :
    ¬ ∀ᶠ z in 𝓝 x, f z = f x := by
  intro hc
  have he : ∀ᶠ z in 𝓝 x, z = x := by
    filter_upwards [hc, hU.mem_nhds hx] with z hz hzU
    exact hinj hzU hx hz
  have hs : ({x} : Set ℂ) ∈ 𝓝 x := he
  exact not_isOpen_singleton x (isOpen_singleton_of_finite_mem_nhds x hs (finite_singleton x))

theorem continuousAt_inverse {f g : ℂ → ℂ} {U V : Set ℂ}
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) (hbij : BijOn f U V)
    (hleft : LeftInvOn g f U) {y : ℂ} (hy : y ∈ V) : ContinuousAt g y := by
  obtain ⟨x, hx, rfl⟩ := hbij.surjOn hy
  have hopen : 𝓝 (f x) ≤ map f (𝓝 x) :=
    ((hf.analyticOnNhd hU x hx).eventually_constant_or_nhds_le_map_nhds).resolve_left
      (not_eventually_constant_of_injOn hU hbij.injOn hx)
  change map g (𝓝 (f x)) ≤ 𝓝 (g (f x))
  rw [hleft hx]
  calc
    map g (𝓝 (f x)) ≤ map g (map f (𝓝 x)) := map_mono hopen
    _ = 𝓝 x := by
      rw [map_map]
      have he : g ∘ f =ᶠ[𝓝 x] id := hleft.eqOn.eventuallyEq_of_mem (hU.mem_nhds hx)
      rw [Filter.map_congr he, map_id]

theorem deriv_eventually_ne_zero {f : ℂ → ℂ} {U : Set ℂ} {x : ℂ}
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) (hinj : InjOn f U) (hx : x ∈ U) :
    ∀ᶠ z in 𝓝[≠] x, deriv f z ≠ 0 := by
  apply ((hf.analyticOnNhd hU x hx).deriv.eventually_eq_zero_or_eventually_ne_zero).resolve_left
  intro hz
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hz.and (hU.mem_nhds hx))
  have hconst : ∀ᶠ z in 𝓝 x, f z = f x := by
    filter_upwards [ball_mem_nhds x hr] with z hz
    exact isOpen_ball.is_const_of_deriv_eq_zero (convex_ball x r).isPreconnected
      (hf.mono fun w hw ↦ (hball hw).2) (fun w hw ↦ (hball hw).1)
      hz (mem_ball_self hr)
  exact not_eventually_constant_of_injOn hU hinj hx hconst

/-- A holomorphic bijection between open complex domains has a holomorphic inverse.
The proof uses open mapping, isolated critical points, and removable singularities.
No assumption that an arbitrary differentiable injection has invertible derivative is used. -/
theorem differentiableOn_inverse {f g : ℂ → ℂ} {U V : Set ℂ}
    (hU : IsOpen U) (hV : IsOpen V) (hf : DifferentiableOn ℂ f U)
    (hbij : BijOn f U V) (hgmap : MapsTo g V U) (hinv : InvOn g f U V) :
    DifferentiableOn ℂ g V := by
  have hcont : ∀ y ∈ V, ContinuousAt g y := fun y hy ↦
    continuousAt_inverse hU hf hbij hinv.1 hy
  intro y hy
  have hyU := hgmap hy
  have hzero := deriv_eventually_ne_zero hU hf hbij.injOn hyU
  have hlim : Tendsto g (𝓝[≠] y) (𝓝[≠] g y) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨(hcont y hy).tendsto.mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin,
      (nhdsWithin_le_nhds (hV.mem_nhds hy))] with z hz hzV
    change g z ≠ g y
    intro heq
    apply hz
    calc z = f (g z) := (hinv.2 hzV).symm
         _ = f (g y) := congrArg f heq
         _ = y := hinv.2 hy
  apply (Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
    ?_ (hcont y hy)).differentiableAt.differentiableWithinAt
  filter_upwards [hlim hzero,
    (nhdsWithin_le_nhds (hV.mem_nhds hy))] with z hz hzV
  have hfd := (hf.analyticOnNhd hU (g z) (hgmap hzV)).hasStrictDerivAt
  exact (hfd.of_local_left_inverse (hcont z hzV) hz
    (hinv.2.eqOn.eventuallyEq_of_mem (hV.mem_nhds hzV))).hasDerivAt.differentiableAt

theorem derivative_product_eq_one {f g : ℂ → ℂ} {U V : Set ℂ}
    (hU : IsOpen U) (hV : IsOpen V) (hf : DifferentiableOn ℂ f U)
    (hg : DifferentiableOn ℂ g V) (hfmap : MapsTo f U V)
    (hleft : LeftInvOn g f U) {x : ℂ} (hx : x ∈ U) :
    deriv g (f x) * deriv f x = 1 := by
  have he := hleft.eqOn.eventuallyEq_of_mem (hU.mem_nhds hx) |>.deriv_eq
  rw [deriv_comp x (hg.differentiableAt (hV.mem_nhds (hfmap hx)))
    (hf.differentiableAt (hU.mem_nhds hx)), deriv_id] at he
  exact he

theorem deriv_ne_zero_of_biholomorphic {f g : ℂ → ℂ} {U V : Set ℂ}
    (hU : IsOpen U) (hV : IsOpen V) (hf : DifferentiableOn ℂ f U)
    (hg : DifferentiableOn ℂ g V) (hfmap : MapsTo f U V)
    (hleft : LeftInvOn g f U) {x : ℂ} (hx : x ∈ U) : deriv f x ≠ 0 := by
  have he := derivative_product_eq_one hU hV hf hg hfmap hleft hx
  intro hz
  simp [hz] at he

theorem exists_biholomorphic_unitBall {U : Set ℂ} (hUo : IsOpen U)
    (hUc : IsSimplyConnected U) (hU : U ≠ univ) {x₀ : ℂ} (hx₀ : x₀ ∈ U) :
    ∃ f g : ℂ → ℂ, DifferentiableOn ℂ f U ∧
      DifferentiableOn ℂ g (ball 0 1) ∧ BijOn f U (ball 0 1) ∧
      MapsTo g (ball 0 1) U ∧ InvOn g f U (ball 0 1) ∧ f x₀ = 0 ∧ g 0 = x₀ := by
  obtain ⟨f, hf, hbij, hf₀⟩ := Complex.exists_bijOn_unitBall_map_eq_zero hUo hUc hU hx₀
  let g := invFunOn f U
  have hinv : InvOn g f U (ball 0 1) := hbij.invOn_invFunOn
  have hgmap : MapsTo g (ball 0 1) U := hbij.surjOn.mapsTo_invFunOn
  refine ⟨f, g, hf, differentiableOn_inverse hUo isOpen_ball hf hbij hgmap hinv,
    hbij, hgmap, hinv, hf₀, ?_⟩
  rw [← hf₀]
  exact hinv.1 hx₀

end RiemannBiholomorphic
