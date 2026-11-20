import Exploding

/-!
# Correspondence of chemical-distance-free results

Each equality checks that the unconditional result has exactly the registered type after
the chemical-distance hypothesis is removed.
-/

example : @Exploding.limit_shape =
    fun d hd p hp hp1 _ => Exploding.limit_shape_unconditional d hd p hp hp1 := rfl

example : @Exploding.convergence_of_time_constant =
    fun d hd p hp hp1 _ => Exploding.convergence_of_time_constant_unconditional d hd p hp hp1 := rfl

example : @Exploding.renormalization_properties =
    fun d hd p hp hp1 _ => Exploding.renormalization_properties_unconditional d hd p hp hp1 := rfl

example : @Exploding.finite_exploding =
    fun d hd p hp hp1 _ => Exploding.finite_exploding_unconditional d hd p hp hp1 := rfl

example : @Exploding.last_penultimate_cluster =
    fun d hd p hp hp1 _ => Exploding.last_penultimate_cluster_unconditional d hd p hp hp1 := rfl

example : @Exploding.penultimate_upper_bound =
    fun d hd p hp hp1 _ => Exploding.penultimate_upper_bound_unconditional d hd p hp hp1 := rfl

example : @Exploding.last_penultimate_close =
    fun d hd p hp hp1 _ => Exploding.last_penultimate_close_unconditional d hd p hp hp1 := rfl

example : @Exploding.convergence_of_the_last_wave =
    fun d hd p hp hp1 _ => Exploding.convergence_of_the_last_wave_unconditional d hd p hp hp1 := rfl

example : @Exploding.approximate_subadditive =
    fun d hd p hp hp1 _ => Exploding.approximate_subadditive_unconditional d hd p hp hp1 := rfl

example : @Exploding.convergence_of_the_generalized_last_wave =
    fun d hd ηmin L hL P hP hsupp hstat herg h1 h3 h4 _ =>
      Exploding.convergence_of_the_generalized_last_wave_unconditional
        d hd ηmin L hL P hP hsupp hstat herg h1 h3 h4 := rfl

example : @Exploding.generalized_convergence =
    fun d hd ηmin L hL P hP hsupp hstat herg h1 h3 h4 h5 _ =>
      Exploding.generalized_convergence_unconditional
        d hd ηmin L hL P hP hsupp hstat herg h1 h3 h4 h5 := rfl
