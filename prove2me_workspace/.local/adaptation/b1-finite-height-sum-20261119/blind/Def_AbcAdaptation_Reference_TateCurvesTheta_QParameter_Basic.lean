open Filter Topology

namespace TateCurvesTheta

variable (K : Type*) [NormedField K]

structure TateParameter where

  q : Kˣ

  norm_lt_one : ‖(q : K)‖ < 1
