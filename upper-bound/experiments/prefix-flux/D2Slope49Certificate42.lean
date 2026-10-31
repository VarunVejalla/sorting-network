import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.FinCases
import D2Slope49Abstract

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Chvatal.D2Slope49Certificate42

def potentials : Array (Array Int) := #[#[(6 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int),(6 : Int),(6 : Int),(6 : Int),(7 : Int),(7 : Int),(7 : Int),(7 : Int),(7 : Int),(7 : Int),(7 : Int),(7 : Int),(7 : Int),(7 : Int),(7 : Int),(7 : Int),(7 : Int),(7 : Int),(8 : Int),(8 : Int),(9 : Int),(9 : Int),(9 : Int),(9 : Int),(10 : Int),(10 : Int),(10 : Int),(10 : Int),(10 : Int),(10 : Int),(10 : Int),(10 : Int),(10 : Int),(10 : Int),(10 : Int),(10 : Int),(10 : Int),(10 : Int),(11 : Int),(11 : Int),(11 : Int),(11 : Int),(12 : Int),(12 : Int),(12 : Int),(12 : Int),(13 : Int),(13 : Int),(13 : Int),(13 : Int),(13 : Int),(13 : Int),(13 : Int),(13 : Int),(13 : Int),(13 : Int),(13 : Int),(13 : Int)],
#[(3 : Int),(3 : Int),(4 : Int),(3 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(5 : Int),(5 : Int),(5 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(7 : Int),(7 : Int),(8 : Int),(8 : Int),(8 : Int),(8 : Int),(9 : Int),(9 : Int),(9 : Int),(9 : Int),(9 : Int),(9 : Int),(9 : Int),(9 : Int),(9 : Int),(9 : Int),(9 : Int),(9 : Int),(9 : Int),(9 : Int),(9 : Int),(9 : Int),(9 : Int),(9 : Int),(10 : Int),(10 : Int),(10 : Int),(10 : Int),(11 : Int),(11 : Int),(11 : Int),(11 : Int),(11 : Int),(11 : Int),(11 : Int),(11 : Int),(11 : Int),(11 : Int),(11 : Int)],
#[(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(4 : Int),(4 : Int),(4 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int),(6 : Int),(6 : Int),(7 : Int),(7 : Int),(7 : Int),(7 : Int),(7 : Int),(7 : Int),(8 : Int),(8 : Int),(8 : Int),(8 : Int),(8 : Int),(8 : Int),(8 : Int),(8 : Int),(8 : Int),(8 : Int),(8 : Int),(8 : Int),(9 : Int),(9 : Int),(9 : Int),(9 : Int),(10 : Int),(10 : Int),(10 : Int),(10 : Int),(10 : Int),(10 : Int),(10 : Int),(10 : Int),(10 : Int),(10 : Int)],
#[(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(2 : Int),(2 : Int),(1 : Int),(1 : Int),(1 : Int),(2 : Int),(2 : Int),(2 : Int),(3 : Int),(2 : Int),(3 : Int),(3 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(5 : Int),(5 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(7 : Int),(7 : Int),(7 : Int),(7 : Int),(7 : Int),(7 : Int),(7 : Int),(7 : Int),(7 : Int),(7 : Int),(7 : Int),(7 : Int),(8 : Int),(8 : Int),(8 : Int),(8 : Int),(9 : Int),(9 : Int),(9 : Int),(9 : Int),(9 : Int),(9 : Int),(9 : Int),(9 : Int),(9 : Int)],
#[(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(2 : Int),(2 : Int),(2 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(4 : Int),(4 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(7 : Int),(7 : Int),(7 : Int),(7 : Int),(7 : Int),(7 : Int),(7 : Int),(7 : Int)],
#[(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(1 : Int),(1 : Int),(1 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int)],
#[(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-1 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int)],
#[(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int)],
#[(-6 : Int),(-5 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int)],
#[(-7 : Int),(-7 : Int),(-6 : Int),(-5 : Int),(-6 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int)],
#[(-8 : Int),(-8 : Int),(-8 : Int),(-8 : Int),(-8 : Int),(-8 : Int),(-7 : Int),(-7 : Int),(-7 : Int),(-7 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-2 : Int),(-3 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int)],
#[(-6 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(2 : Int),(2 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int)],
#[(-7 : Int),(-7 : Int),(-7 : Int),(-7 : Int),(-7 : Int),(-7 : Int),(-7 : Int),(-7 : Int),(-7 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-2 : Int),(-2 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(1 : Int),(1 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int)],
#[(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(1 : Int),(1 : Int),(1 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(4 : Int),(4 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int)],
#[(-5 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(1 : Int),(1 : Int),(1 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(3 : Int),(3 : Int),(4 : Int),(3 : Int),(3 : Int),(4 : Int)],
#[(-6 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(0 : Int),(0 : Int),(0 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int)],
#[(-7 : Int),(-7 : Int),(-7 : Int),(-7 : Int),(-7 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-5 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-5 : Int),(-5 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int)],
#[(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(0 : Int),(0 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(2 : Int),(2 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(5 : Int),(5 : Int),(5 : Int),(6 : Int),(6 : Int),(6 : Int),(7 : Int),(7 : Int),(7 : Int),(7 : Int),(7 : Int),(7 : Int),(7 : Int),(7 : Int),(7 : Int),(7 : Int),(7 : Int),(7 : Int),(7 : Int),(7 : Int),(7 : Int),(7 : Int),(7 : Int)],
#[(-3 : Int),(-2 : Int),(-3 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-1 : Int),(-1 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(1 : Int),(1 : Int),(1 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int)],
#[(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-2 : Int),(-2 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(1 : Int),(1 : Int),(1 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int)],
#[(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-4 : Int),(-4 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(0 : Int),(0 : Int),(0 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int)],
#[(-6 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(2 : Int),(2 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int)],
#[(-7 : Int),(-7 : Int),(-7 : Int),(-7 : Int),(-7 : Int),(-7 : Int),(-7 : Int),(-7 : Int),(-7 : Int),(-7 : Int),(-7 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-3 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(1 : Int),(1 : Int),(1 : Int),(2 : Int),(2 : Int),(2 : Int)],
#[(-8 : Int),(-8 : Int),(-8 : Int),(-8 : Int),(-8 : Int),(-8 : Int),(-8 : Int),(-8 : Int),(-8 : Int),(-8 : Int),(-8 : Int),(-8 : Int),(-8 : Int),(-8 : Int),(-8 : Int),(-8 : Int),(-7 : Int),(-7 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(0 : Int),(0 : Int),(0 : Int),(1 : Int),(1 : Int)],
#[(-9 : Int),(-9 : Int),(-9 : Int),(-8 : Int),(-8 : Int),(-8 : Int),(-8 : Int),(-8 : Int),(-8 : Int),(-8 : Int),(-8 : Int),(-8 : Int),(-8 : Int),(-8 : Int),(-8 : Int),(-8 : Int),(-8 : Int),(-7 : Int),(-7 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(0 : Int)],
#[(2 : Int),(2 : Int),(2 : Int),(2 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(4 : Int),(4 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(7 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(7 : Int),(7 : Int),(7 : Int),(7 : Int),(8 : Int),(8 : Int),(9 : Int),(9 : Int),(9 : Int),(9 : Int),(9 : Int),(9 : Int),(9 : Int),(9 : Int),(9 : Int),(9 : Int),(9 : Int),(9 : Int),(9 : Int),(9 : Int),(10 : Int),(10 : Int),(10 : Int)],
#[(0 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(3 : Int),(3 : Int),(3 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(7 : Int),(7 : Int),(8 : Int),(8 : Int),(8 : Int),(8 : Int),(8 : Int),(8 : Int),(8 : Int),(8 : Int),(8 : Int),(8 : Int),(8 : Int),(8 : Int),(8 : Int),(8 : Int),(9 : Int),(9 : Int)],
#[(-1 : Int),(-1 : Int),(-1 : Int),(0 : Int),(0 : Int),(0 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(3 : Int),(3 : Int),(3 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(7 : Int),(7 : Int),(7 : Int),(8 : Int),(8 : Int),(8 : Int),(8 : Int),(8 : Int),(8 : Int),(8 : Int),(8 : Int),(8 : Int),(8 : Int),(8 : Int),(8 : Int),(8 : Int),(8 : Int)],
#[(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int)],
#[(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(2 : Int),(2 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int)],
#[(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-3 : Int),(-4 : Int),(-4 : Int),(-3 : Int),(-4 : Int),(-3 : Int),(-3 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(1 : Int),(1 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int)],
#[(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(0 : Int),(0 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int)],
#[(-6 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-2 : Int),(-2 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int)],
#[(-7 : Int),(-7 : Int),(-7 : Int),(-7 : Int),(-7 : Int),(-7 : Int),(-7 : Int),(-7 : Int),(-7 : Int),(-7 : Int),(-7 : Int),(-7 : Int),(-7 : Int),(-7 : Int),(-7 : Int),(-7 : Int),(-7 : Int),(-7 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-3 : Int),(-3 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int)],
#[(-8 : Int),(-8 : Int),(-8 : Int),(-8 : Int),(-8 : Int),(-7 : Int),(-7 : Int),(-7 : Int),(-7 : Int),(-7 : Int),(-7 : Int),(-7 : Int),(-7 : Int),(-7 : Int),(-7 : Int),(-7 : Int),(-7 : Int),(-7 : Int),(-7 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-3 : Int),(-3 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int)],
#[(-9 : Int),(-9 : Int),(-9 : Int),(-9 : Int),(-9 : Int),(-9 : Int),(-8 : Int),(-8 : Int),(-8 : Int),(-8 : Int),(-8 : Int),(-8 : Int),(-8 : Int),(-8 : Int),(-8 : Int),(-8 : Int),(-8 : Int),(-8 : Int),(-8 : Int),(-8 : Int),(-7 : Int),(-7 : Int),(-7 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-3 : Int),(-4 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int)],
#[(-10 : Int),(-10 : Int),(-10 : Int),(-10 : Int),(-10 : Int),(-10 : Int),(-10 : Int),(-9 : Int),(-9 : Int),(-9 : Int),(-9 : Int),(-9 : Int),(-9 : Int),(-9 : Int),(-9 : Int),(-9 : Int),(-9 : Int),(-9 : Int),(-9 : Int),(-9 : Int),(-9 : Int),(-9 : Int),(-9 : Int),(-9 : Int),(-8 : Int),(-8 : Int),(-8 : Int),(-7 : Int),(-7 : Int),(-7 : Int),(-7 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int)],
#[(-11 : Int),(-11 : Int),(-12 : Int),(-12 : Int),(-12 : Int),(-12 : Int),(-12 : Int),(-12 : Int),(-11 : Int),(-11 : Int),(-11 : Int),(-11 : Int),(-10 : Int),(-10 : Int),(-10 : Int),(-10 : Int),(-10 : Int),(-10 : Int),(-10 : Int),(-10 : Int),(-10 : Int),(-10 : Int),(-10 : Int),(-10 : Int),(-10 : Int),(-9 : Int),(-9 : Int),(-9 : Int),(-9 : Int),(-8 : Int),(-8 : Int),(-8 : Int),(-8 : Int),(-8 : Int),(-7 : Int),(-7 : Int),(-7 : Int),(-7 : Int),(-7 : Int),(-7 : Int),(-7 : Int),(-7 : Int),(-7 : Int),(-7 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int)],
#[(-14 : Int),(-14 : Int),(-13 : Int),(-14 : Int),(-13 : Int),(-13 : Int),(-13 : Int),(-13 : Int),(-13 : Int),(-12 : Int),(-12 : Int),(-12 : Int),(-12 : Int),(-11 : Int),(-11 : Int),(-11 : Int),(-11 : Int),(-11 : Int),(-11 : Int),(-11 : Int),(-11 : Int),(-11 : Int),(-11 : Int),(-11 : Int),(-11 : Int),(-11 : Int),(-10 : Int),(-10 : Int),(-10 : Int),(-10 : Int),(-9 : Int),(-9 : Int),(-9 : Int),(-9 : Int),(-9 : Int),(-8 : Int),(-8 : Int),(-8 : Int),(-8 : Int),(-8 : Int),(-8 : Int),(-8 : Int),(-8 : Int),(-8 : Int),(-8 : Int),(-7 : Int),(-7 : Int),(-8 : Int),(-8 : Int),(-8 : Int),(-8 : Int),(-7 : Int),(-7 : Int),(-7 : Int),(-7 : Int),(-6 : Int),(-6 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int)],
#[(-15 : Int),(-15 : Int),(-15 : Int),(-15 : Int),(-15 : Int),(-14 : Int),(-14 : Int),(-14 : Int),(-14 : Int),(-14 : Int),(-13 : Int),(-13 : Int),(-13 : Int),(-13 : Int),(-13 : Int),(-12 : Int),(-12 : Int),(-12 : Int),(-12 : Int),(-12 : Int),(-12 : Int),(-12 : Int),(-12 : Int),(-12 : Int),(-12 : Int),(-12 : Int),(-12 : Int),(-12 : Int),(-12 : Int),(-12 : Int),(-12 : Int),(-12 : Int),(-11 : Int),(-11 : Int),(-11 : Int),(-11 : Int),(-10 : Int),(-10 : Int),(-10 : Int),(-9 : Int),(-9 : Int),(-9 : Int),(-9 : Int),(-9 : Int),(-9 : Int),(-9 : Int),(-9 : Int),(-9 : Int),(-9 : Int),(-9 : Int),(-9 : Int),(-9 : Int),(-8 : Int),(-8 : Int),(-8 : Int),(-8 : Int),(-7 : Int),(-7 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-6 : Int)],
#[(-16 : Int),(-16 : Int),(-16 : Int),(-16 : Int),(-16 : Int),(-16 : Int),(-16 : Int),(-15 : Int),(-15 : Int),(-16 : Int),(-16 : Int),(-15 : Int),(-15 : Int),(-15 : Int),(-15 : Int),(-15 : Int),(-14 : Int),(-14 : Int),(-14 : Int),(-13 : Int),(-13 : Int),(-13 : Int),(-13 : Int),(-13 : Int),(-13 : Int),(-13 : Int),(-13 : Int),(-13 : Int),(-13 : Int),(-13 : Int),(-13 : Int),(-13 : Int),(-13 : Int),(-12 : Int),(-12 : Int),(-12 : Int),(-12 : Int),(-11 : Int),(-11 : Int),(-11 : Int),(-10 : Int),(-10 : Int),(-10 : Int),(-10 : Int),(-10 : Int),(-10 : Int),(-10 : Int),(-10 : Int),(-10 : Int),(-10 : Int),(-10 : Int),(-10 : Int),(-10 : Int),(-9 : Int),(-9 : Int),(-9 : Int),(-9 : Int),(-8 : Int),(-8 : Int),(-7 : Int),(-7 : Int),(-7 : Int),(-7 : Int),(-7 : Int),(-7 : Int)],
#[(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(1 : Int),(1 : Int),(1 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(3 : Int),(3 : Int),(4 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int)],
#[(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(0 : Int),(0 : Int),(0 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int)],
#[(-6 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-5 : Int),(-5 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int)],
#[(-7 : Int),(-7 : Int),(-7 : Int),(-7 : Int),(-7 : Int),(-7 : Int),(-7 : Int),(-7 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int)],
#[(7 : Int),(9 : Int),(9 : Int),(8 : Int),(8 : Int),(9 : Int),(9 : Int),(9 : Int),(9 : Int),(10 : Int),(10 : Int),(10 : Int),(10 : Int),(10 : Int),(10 : Int),(10 : Int),(10 : Int),(10 : Int),(10 : Int),(10 : Int),(10 : Int),(11 : Int),(11 : Int),(11 : Int),(11 : Int),(12 : Int),(12 : Int),(12 : Int),(12 : Int),(13 : Int),(13 : Int),(13 : Int),(13 : Int),(13 : Int),(13 : Int),(13 : Int),(13 : Int),(13 : Int),(13 : Int),(13 : Int),(13 : Int),(13 : Int),(13 : Int),(13 : Int),(13 : Int),(14 : Int),(14 : Int),(14 : Int),(14 : Int),(14 : Int),(15 : Int),(15 : Int),(15 : Int),(16 : Int),(16 : Int),(16 : Int),(16 : Int),(16 : Int),(16 : Int),(16 : Int),(16 : Int),(16 : Int),(16 : Int),(16 : Int),(16 : Int)],
#[(6 : Int),(6 : Int),(7 : Int),(7 : Int),(7 : Int),(7 : Int),(7 : Int),(8 : Int),(8 : Int),(8 : Int),(9 : Int),(9 : Int),(9 : Int),(9 : Int),(9 : Int),(9 : Int),(9 : Int),(9 : Int),(9 : Int),(9 : Int),(9 : Int),(9 : Int),(10 : Int),(9 : Int),(9 : Int),(9 : Int),(9 : Int),(10 : Int),(10 : Int),(10 : Int),(11 : Int),(11 : Int),(11 : Int),(12 : Int),(12 : Int),(12 : Int),(12 : Int),(12 : Int),(12 : Int),(12 : Int),(12 : Int),(12 : Int),(12 : Int),(12 : Int),(12 : Int),(12 : Int),(13 : Int),(13 : Int),(13 : Int),(13 : Int),(13 : Int),(14 : Int),(14 : Int),(14 : Int),(15 : Int),(15 : Int),(15 : Int),(15 : Int),(15 : Int),(15 : Int),(15 : Int),(15 : Int),(15 : Int),(15 : Int),(15 : Int)],
#[(5 : Int),(5 : Int),(5 : Int),(6 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int),(6 : Int),(6 : Int),(6 : Int),(7 : Int),(7 : Int),(7 : Int),(8 : Int),(8 : Int),(8 : Int),(8 : Int),(8 : Int),(8 : Int),(8 : Int),(8 : Int),(8 : Int),(8 : Int),(8 : Int),(8 : Int),(8 : Int),(8 : Int),(9 : Int),(9 : Int),(9 : Int),(10 : Int),(10 : Int),(10 : Int),(11 : Int),(11 : Int),(11 : Int),(11 : Int),(11 : Int),(11 : Int),(11 : Int),(11 : Int),(11 : Int),(11 : Int),(11 : Int),(11 : Int),(11 : Int),(12 : Int),(12 : Int),(12 : Int),(12 : Int),(12 : Int),(13 : Int),(13 : Int),(13 : Int),(14 : Int),(14 : Int),(14 : Int),(14 : Int),(14 : Int),(14 : Int),(14 : Int),(14 : Int),(14 : Int),(14 : Int)],
#[(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(5 : Int),(5 : Int),(5 : Int),(6 : Int),(6 : Int),(6 : Int),(7 : Int),(7 : Int),(7 : Int),(7 : Int),(7 : Int),(7 : Int),(7 : Int),(7 : Int),(7 : Int),(7 : Int),(7 : Int),(7 : Int),(7 : Int),(7 : Int),(8 : Int),(8 : Int),(8 : Int),(9 : Int),(9 : Int),(9 : Int),(10 : Int),(10 : Int),(10 : Int),(10 : Int),(10 : Int),(10 : Int),(10 : Int),(10 : Int),(10 : Int),(10 : Int),(10 : Int),(10 : Int),(10 : Int),(11 : Int),(10 : Int),(10 : Int),(10 : Int),(10 : Int),(11 : Int),(11 : Int),(11 : Int),(11 : Int),(12 : Int),(12 : Int),(13 : Int),(13 : Int),(13 : Int),(13 : Int),(13 : Int),(13 : Int)],
#[(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(5 : Int),(5 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(7 : Int),(7 : Int),(8 : Int),(8 : Int),(8 : Int),(8 : Int),(9 : Int),(9 : Int),(9 : Int),(9 : Int),(9 : Int),(9 : Int),(9 : Int),(9 : Int),(9 : Int),(9 : Int),(9 : Int),(9 : Int),(9 : Int),(9 : Int),(10 : Int),(10 : Int),(10 : Int),(10 : Int),(11 : Int),(11 : Int),(12 : Int),(12 : Int),(12 : Int),(12 : Int),(12 : Int)],
#[(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(3 : Int),(3 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(5 : Int),(4 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int),(6 : Int),(6 : Int),(7 : Int),(7 : Int),(7 : Int),(7 : Int),(8 : Int),(8 : Int),(8 : Int),(8 : Int),(8 : Int),(8 : Int),(8 : Int),(8 : Int),(8 : Int),(8 : Int),(8 : Int),(8 : Int),(8 : Int),(8 : Int),(9 : Int),(9 : Int),(9 : Int),(9 : Int),(10 : Int),(10 : Int),(11 : Int),(11 : Int),(10 : Int),(10 : Int)],
#[(1 : Int),(1 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(3 : Int),(3 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(7 : Int),(7 : Int),(7 : Int),(8 : Int),(8 : Int),(8 : Int),(8 : Int),(8 : Int),(8 : Int),(8 : Int),(8 : Int),(8 : Int),(8 : Int),(8 : Int),(8 : Int),(8 : Int),(8 : Int),(8 : Int),(8 : Int),(8 : Int),(9 : Int),(9 : Int),(9 : Int),(9 : Int),(9 : Int)],
#[(0 : Int),(0 : Int),(0 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(2 : Int),(2 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(5 : Int),(5 : Int),(5 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(7 : Int),(7 : Int),(7 : Int),(7 : Int),(7 : Int),(7 : Int),(7 : Int),(7 : Int),(7 : Int),(7 : Int),(7 : Int),(7 : Int),(7 : Int),(8 : Int),(8 : Int),(8 : Int),(8 : Int)],
#[(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(2 : Int),(2 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(4 : Int),(4 : Int),(4 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(7 : Int),(7 : Int),(7 : Int)],
#[(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(2 : Int),(2 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int)],
#[(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(1 : Int),(1 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int)],
#[(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-1 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-1 : Int),(-1 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int)],
#[(-5 : Int),(-6 : Int),(-5 : Int),(-6 : Int),(-6 : Int),(-5 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-2 : Int),(-2 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int)],
#[(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int)],
#[(-6 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int)],
#[(-7 : Int),(-7 : Int),(-7 : Int),(-7 : Int),(-7 : Int),(-7 : Int),(-7 : Int),(-7 : Int),(-7 : Int),(-7 : Int),(-7 : Int),(-7 : Int),(-7 : Int),(-7 : Int),(-7 : Int),(-7 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-5 : Int),(-5 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int)],
#[(9 : Int),(9 : Int),(9 : Int),(9 : Int),(9 : Int),(10 : Int),(10 : Int),(10 : Int),(10 : Int),(10 : Int),(10 : Int),(10 : Int),(10 : Int),(10 : Int),(10 : Int),(10 : Int),(10 : Int),(11 : Int),(11 : Int),(11 : Int),(11 : Int),(11 : Int),(12 : Int),(12 : Int),(13 : Int),(13 : Int),(13 : Int),(13 : Int),(13 : Int),(13 : Int),(13 : Int),(13 : Int),(13 : Int),(13 : Int),(13 : Int),(13 : Int),(13 : Int),(13 : Int),(14 : Int),(14 : Int),(14 : Int),(15 : Int),(15 : Int),(15 : Int),(15 : Int),(15 : Int),(16 : Int),(16 : Int),(16 : Int),(16 : Int),(16 : Int),(16 : Int),(16 : Int),(16 : Int),(16 : Int),(16 : Int),(16 : Int),(16 : Int),(16 : Int),(16 : Int),(16 : Int),(16 : Int),(16 : Int),(16 : Int),(16 : Int)],
#[(8 : Int),(8 : Int),(8 : Int),(8 : Int),(8 : Int),(8 : Int),(9 : Int),(9 : Int),(9 : Int),(9 : Int),(9 : Int),(9 : Int),(9 : Int),(9 : Int),(9 : Int),(9 : Int),(9 : Int),(9 : Int),(10 : Int),(10 : Int),(10 : Int),(10 : Int),(10 : Int),(11 : Int),(11 : Int),(12 : Int),(12 : Int),(12 : Int),(12 : Int),(12 : Int),(12 : Int),(12 : Int),(12 : Int),(12 : Int),(12 : Int),(12 : Int),(12 : Int),(12 : Int),(12 : Int),(12 : Int),(12 : Int),(12 : Int),(12 : Int),(13 : Int),(13 : Int),(13 : Int),(13 : Int),(14 : Int),(14 : Int),(14 : Int),(14 : Int),(15 : Int),(15 : Int),(15 : Int),(15 : Int),(15 : Int),(15 : Int),(15 : Int),(15 : Int),(15 : Int),(15 : Int),(15 : Int),(15 : Int),(15 : Int),(15 : Int)],
#[(7 : Int),(7 : Int),(7 : Int),(7 : Int),(7 : Int),(7 : Int),(7 : Int),(8 : Int),(8 : Int),(8 : Int),(8 : Int),(8 : Int),(8 : Int),(8 : Int),(8 : Int),(8 : Int),(8 : Int),(8 : Int),(8 : Int),(8 : Int),(8 : Int),(8 : Int),(8 : Int),(8 : Int),(9 : Int),(9 : Int),(10 : Int),(10 : Int),(10 : Int),(10 : Int),(11 : Int),(11 : Int),(11 : Int),(11 : Int),(11 : Int),(11 : Int),(11 : Int),(11 : Int),(11 : Int),(11 : Int),(11 : Int),(11 : Int),(11 : Int),(11 : Int),(12 : Int),(12 : Int),(12 : Int),(12 : Int),(13 : Int),(13 : Int),(13 : Int),(13 : Int),(14 : Int),(14 : Int),(14 : Int),(14 : Int),(14 : Int),(14 : Int),(14 : Int),(14 : Int),(14 : Int),(14 : Int),(14 : Int),(14 : Int),(14 : Int)]]
def suffixes : Array (Array Int) := #[#[(5 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int),(6 : Int),(6 : Int),(6 : Int),(7 : Int),(7 : Int),(7 : Int),(7 : Int),(7 : Int),(7 : Int),(7 : Int),(7 : Int),(7 : Int),(7 : Int),(7 : Int),(7 : Int),(7 : Int),(7 : Int),(8 : Int),(8 : Int),(9 : Int),(9 : Int),(9 : Int),(9 : Int),(10 : Int),(10 : Int),(10 : Int),(10 : Int),(10 : Int),(10 : Int),(10 : Int),(10 : Int),(10 : Int),(10 : Int),(10 : Int),(10 : Int),(10 : Int),(10 : Int),(11 : Int),(11 : Int),(11 : Int),(11 : Int),(12 : Int),(12 : Int),(12 : Int),(12 : Int),(13 : Int),(13 : Int),(13 : Int),(13 : Int),(13 : Int),(13 : Int),(13 : Int),(13 : Int),(13 : Int),(13 : Int),(13 : Int),(13 : Int)],
#[(3 : Int),(3 : Int),(3 : Int),(3 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(5 : Int),(5 : Int),(5 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(7 : Int),(7 : Int),(8 : Int),(8 : Int),(8 : Int),(8 : Int),(9 : Int),(9 : Int),(9 : Int),(9 : Int),(9 : Int),(9 : Int),(9 : Int),(9 : Int),(9 : Int),(9 : Int),(9 : Int),(9 : Int),(9 : Int),(9 : Int),(9 : Int),(9 : Int),(9 : Int),(9 : Int),(10 : Int),(10 : Int),(10 : Int),(10 : Int),(11 : Int),(11 : Int),(11 : Int),(11 : Int),(11 : Int),(11 : Int),(11 : Int),(11 : Int),(11 : Int),(11 : Int),(11 : Int)],
#[(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(4 : Int),(4 : Int),(4 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int),(6 : Int),(6 : Int),(7 : Int),(7 : Int),(7 : Int),(7 : Int),(7 : Int),(7 : Int),(8 : Int),(8 : Int),(8 : Int),(8 : Int),(8 : Int),(8 : Int),(8 : Int),(8 : Int),(8 : Int),(8 : Int),(8 : Int),(8 : Int),(9 : Int),(9 : Int),(9 : Int),(9 : Int),(10 : Int),(10 : Int),(10 : Int),(10 : Int),(10 : Int),(10 : Int),(10 : Int),(10 : Int),(10 : Int),(10 : Int)],
#[(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(3 : Int),(3 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(5 : Int),(5 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(7 : Int),(7 : Int),(7 : Int),(7 : Int),(7 : Int),(7 : Int),(7 : Int),(7 : Int),(7 : Int),(7 : Int),(7 : Int),(7 : Int),(8 : Int),(8 : Int),(8 : Int),(8 : Int),(9 : Int),(9 : Int),(9 : Int),(9 : Int),(9 : Int),(9 : Int),(9 : Int),(9 : Int),(9 : Int)],
#[(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(2 : Int),(2 : Int),(2 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(4 : Int),(4 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(7 : Int),(7 : Int),(7 : Int),(7 : Int),(7 : Int),(7 : Int),(7 : Int),(7 : Int)],
#[(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(1 : Int),(1 : Int),(1 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int)],
#[(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int)],
#[(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int)],
#[(-6 : Int),(-5 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int)],
#[(-7 : Int),(-7 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int)],
#[(-8 : Int),(-8 : Int),(-8 : Int),(-8 : Int),(-8 : Int),(-8 : Int),(-7 : Int),(-7 : Int),(-7 : Int),(-7 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int)],
#[(-6 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(2 : Int),(2 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int)],
#[(-7 : Int),(-7 : Int),(-7 : Int),(-7 : Int),(-7 : Int),(-7 : Int),(-7 : Int),(-7 : Int),(-7 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-2 : Int),(-2 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(1 : Int),(1 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int)],
#[(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(1 : Int),(1 : Int),(1 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(4 : Int),(4 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int)],
#[(-5 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(1 : Int),(1 : Int),(1 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(4 : Int)],
#[(-6 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(0 : Int),(0 : Int),(0 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int)],
#[(-7 : Int),(-7 : Int),(-7 : Int),(-7 : Int),(-7 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-5 : Int),(-5 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int)],
#[(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(0 : Int),(0 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(2 : Int),(2 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(5 : Int),(5 : Int),(5 : Int),(6 : Int),(6 : Int),(6 : Int),(7 : Int),(7 : Int),(7 : Int),(7 : Int),(7 : Int),(7 : Int),(7 : Int),(7 : Int),(7 : Int),(7 : Int),(7 : Int),(7 : Int),(7 : Int),(7 : Int),(7 : Int),(7 : Int),(7 : Int)],
#[(-3 : Int),(-3 : Int),(-3 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-1 : Int),(-1 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(1 : Int),(1 : Int),(1 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int)],
#[(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-2 : Int),(-2 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(1 : Int),(1 : Int),(1 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int)],
#[(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-4 : Int),(-4 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(0 : Int),(0 : Int),(0 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int)],
#[(-6 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(2 : Int),(2 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int)],
#[(-7 : Int),(-7 : Int),(-7 : Int),(-7 : Int),(-7 : Int),(-7 : Int),(-7 : Int),(-7 : Int),(-7 : Int),(-7 : Int),(-7 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(1 : Int),(1 : Int),(1 : Int),(2 : Int),(2 : Int),(2 : Int)],
#[(-8 : Int),(-8 : Int),(-8 : Int),(-8 : Int),(-8 : Int),(-8 : Int),(-8 : Int),(-8 : Int),(-8 : Int),(-8 : Int),(-8 : Int),(-8 : Int),(-8 : Int),(-8 : Int),(-8 : Int),(-8 : Int),(-7 : Int),(-7 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(0 : Int),(0 : Int),(0 : Int),(1 : Int),(1 : Int)],
#[(-9 : Int),(-9 : Int),(-9 : Int),(-8 : Int),(-8 : Int),(-8 : Int),(-8 : Int),(-8 : Int),(-8 : Int),(-8 : Int),(-8 : Int),(-8 : Int),(-8 : Int),(-8 : Int),(-8 : Int),(-8 : Int),(-8 : Int),(-7 : Int),(-7 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(0 : Int)],
#[(2 : Int),(2 : Int),(2 : Int),(2 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(4 : Int),(4 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(7 : Int),(7 : Int),(7 : Int),(7 : Int),(8 : Int),(8 : Int),(9 : Int),(9 : Int),(9 : Int),(9 : Int),(9 : Int),(9 : Int),(9 : Int),(9 : Int),(9 : Int),(9 : Int),(9 : Int),(9 : Int),(9 : Int),(9 : Int),(10 : Int),(10 : Int),(10 : Int)],
#[(0 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(3 : Int),(3 : Int),(3 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(7 : Int),(7 : Int),(8 : Int),(8 : Int),(8 : Int),(8 : Int),(8 : Int),(8 : Int),(8 : Int),(8 : Int),(8 : Int),(8 : Int),(8 : Int),(8 : Int),(8 : Int),(8 : Int),(9 : Int),(9 : Int)],
#[(-1 : Int),(-1 : Int),(-1 : Int),(0 : Int),(0 : Int),(0 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(3 : Int),(3 : Int),(3 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(7 : Int),(7 : Int),(7 : Int),(8 : Int),(8 : Int),(8 : Int),(8 : Int),(8 : Int),(8 : Int),(8 : Int),(8 : Int),(8 : Int),(8 : Int),(8 : Int),(8 : Int),(8 : Int),(8 : Int)],
#[(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int)],
#[(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(2 : Int),(2 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int)],
#[(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-3 : Int),(-3 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(1 : Int),(1 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int)],
#[(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(0 : Int),(0 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int)],
#[(-6 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-2 : Int),(-2 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int)],
#[(-7 : Int),(-7 : Int),(-7 : Int),(-7 : Int),(-7 : Int),(-7 : Int),(-7 : Int),(-7 : Int),(-7 : Int),(-7 : Int),(-7 : Int),(-7 : Int),(-7 : Int),(-7 : Int),(-7 : Int),(-7 : Int),(-7 : Int),(-7 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-3 : Int),(-3 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int)],
#[(-8 : Int),(-8 : Int),(-8 : Int),(-8 : Int),(-8 : Int),(-7 : Int),(-7 : Int),(-7 : Int),(-7 : Int),(-7 : Int),(-7 : Int),(-7 : Int),(-7 : Int),(-7 : Int),(-7 : Int),(-7 : Int),(-7 : Int),(-7 : Int),(-7 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-3 : Int),(-3 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int)],
#[(-9 : Int),(-9 : Int),(-9 : Int),(-9 : Int),(-9 : Int),(-9 : Int),(-8 : Int),(-8 : Int),(-8 : Int),(-8 : Int),(-8 : Int),(-8 : Int),(-8 : Int),(-8 : Int),(-8 : Int),(-8 : Int),(-8 : Int),(-8 : Int),(-8 : Int),(-8 : Int),(-7 : Int),(-7 : Int),(-7 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int)],
#[(-10 : Int),(-10 : Int),(-10 : Int),(-10 : Int),(-10 : Int),(-10 : Int),(-10 : Int),(-9 : Int),(-9 : Int),(-9 : Int),(-9 : Int),(-9 : Int),(-9 : Int),(-9 : Int),(-9 : Int),(-9 : Int),(-9 : Int),(-9 : Int),(-9 : Int),(-9 : Int),(-9 : Int),(-9 : Int),(-9 : Int),(-9 : Int),(-8 : Int),(-8 : Int),(-8 : Int),(-7 : Int),(-7 : Int),(-7 : Int),(-7 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int)],
#[(-12 : Int),(-12 : Int),(-12 : Int),(-12 : Int),(-12 : Int),(-12 : Int),(-12 : Int),(-12 : Int),(-11 : Int),(-11 : Int),(-11 : Int),(-11 : Int),(-10 : Int),(-10 : Int),(-10 : Int),(-10 : Int),(-10 : Int),(-10 : Int),(-10 : Int),(-10 : Int),(-10 : Int),(-10 : Int),(-10 : Int),(-10 : Int),(-10 : Int),(-9 : Int),(-9 : Int),(-9 : Int),(-9 : Int),(-8 : Int),(-8 : Int),(-8 : Int),(-8 : Int),(-8 : Int),(-7 : Int),(-7 : Int),(-7 : Int),(-7 : Int),(-7 : Int),(-7 : Int),(-7 : Int),(-7 : Int),(-7 : Int),(-7 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int)],
#[(-14 : Int),(-14 : Int),(-14 : Int),(-14 : Int),(-13 : Int),(-13 : Int),(-13 : Int),(-13 : Int),(-13 : Int),(-12 : Int),(-12 : Int),(-12 : Int),(-12 : Int),(-11 : Int),(-11 : Int),(-11 : Int),(-11 : Int),(-11 : Int),(-11 : Int),(-11 : Int),(-11 : Int),(-11 : Int),(-11 : Int),(-11 : Int),(-11 : Int),(-11 : Int),(-10 : Int),(-10 : Int),(-10 : Int),(-10 : Int),(-9 : Int),(-9 : Int),(-9 : Int),(-9 : Int),(-9 : Int),(-8 : Int),(-8 : Int),(-8 : Int),(-8 : Int),(-8 : Int),(-8 : Int),(-8 : Int),(-8 : Int),(-8 : Int),(-8 : Int),(-8 : Int),(-8 : Int),(-8 : Int),(-8 : Int),(-8 : Int),(-8 : Int),(-7 : Int),(-7 : Int),(-7 : Int),(-7 : Int),(-6 : Int),(-6 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int)],
#[(-15 : Int),(-15 : Int),(-15 : Int),(-15 : Int),(-15 : Int),(-14 : Int),(-14 : Int),(-14 : Int),(-14 : Int),(-14 : Int),(-13 : Int),(-13 : Int),(-13 : Int),(-13 : Int),(-13 : Int),(-12 : Int),(-12 : Int),(-12 : Int),(-12 : Int),(-12 : Int),(-12 : Int),(-12 : Int),(-12 : Int),(-12 : Int),(-12 : Int),(-12 : Int),(-12 : Int),(-12 : Int),(-12 : Int),(-12 : Int),(-12 : Int),(-12 : Int),(-11 : Int),(-11 : Int),(-11 : Int),(-11 : Int),(-10 : Int),(-10 : Int),(-10 : Int),(-9 : Int),(-9 : Int),(-9 : Int),(-9 : Int),(-9 : Int),(-9 : Int),(-9 : Int),(-9 : Int),(-9 : Int),(-9 : Int),(-9 : Int),(-9 : Int),(-9 : Int),(-8 : Int),(-8 : Int),(-8 : Int),(-8 : Int),(-7 : Int),(-7 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-6 : Int)],
#[(-16 : Int),(-16 : Int),(-16 : Int),(-16 : Int),(-16 : Int),(-16 : Int),(-16 : Int),(-16 : Int),(-16 : Int),(-16 : Int),(-16 : Int),(-15 : Int),(-15 : Int),(-15 : Int),(-15 : Int),(-15 : Int),(-14 : Int),(-14 : Int),(-14 : Int),(-13 : Int),(-13 : Int),(-13 : Int),(-13 : Int),(-13 : Int),(-13 : Int),(-13 : Int),(-13 : Int),(-13 : Int),(-13 : Int),(-13 : Int),(-13 : Int),(-13 : Int),(-13 : Int),(-12 : Int),(-12 : Int),(-12 : Int),(-12 : Int),(-11 : Int),(-11 : Int),(-11 : Int),(-10 : Int),(-10 : Int),(-10 : Int),(-10 : Int),(-10 : Int),(-10 : Int),(-10 : Int),(-10 : Int),(-10 : Int),(-10 : Int),(-10 : Int),(-10 : Int),(-10 : Int),(-9 : Int),(-9 : Int),(-9 : Int),(-9 : Int),(-8 : Int),(-8 : Int),(-7 : Int),(-7 : Int),(-7 : Int),(-7 : Int),(-7 : Int),(-7 : Int)],
#[(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(1 : Int),(1 : Int),(1 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int)],
#[(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(0 : Int),(0 : Int),(0 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int)],
#[(-6 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int)],
#[(-7 : Int),(-7 : Int),(-7 : Int),(-7 : Int),(-7 : Int),(-7 : Int),(-7 : Int),(-7 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int)],
#[(7 : Int),(8 : Int),(8 : Int),(8 : Int),(8 : Int),(9 : Int),(9 : Int),(9 : Int),(9 : Int),(10 : Int),(10 : Int),(10 : Int),(10 : Int),(10 : Int),(10 : Int),(10 : Int),(10 : Int),(10 : Int),(10 : Int),(10 : Int),(10 : Int),(11 : Int),(11 : Int),(11 : Int),(11 : Int),(12 : Int),(12 : Int),(12 : Int),(12 : Int),(13 : Int),(13 : Int),(13 : Int),(13 : Int),(13 : Int),(13 : Int),(13 : Int),(13 : Int),(13 : Int),(13 : Int),(13 : Int),(13 : Int),(13 : Int),(13 : Int),(13 : Int),(13 : Int),(14 : Int),(14 : Int),(14 : Int),(14 : Int),(14 : Int),(15 : Int),(15 : Int),(15 : Int),(16 : Int),(16 : Int),(16 : Int),(16 : Int),(16 : Int),(16 : Int),(16 : Int),(16 : Int),(16 : Int),(16 : Int),(16 : Int),(16 : Int)],
#[(6 : Int),(6 : Int),(7 : Int),(7 : Int),(7 : Int),(7 : Int),(7 : Int),(8 : Int),(8 : Int),(8 : Int),(9 : Int),(9 : Int),(9 : Int),(9 : Int),(9 : Int),(9 : Int),(9 : Int),(9 : Int),(9 : Int),(9 : Int),(9 : Int),(9 : Int),(9 : Int),(9 : Int),(9 : Int),(9 : Int),(9 : Int),(10 : Int),(10 : Int),(10 : Int),(11 : Int),(11 : Int),(11 : Int),(12 : Int),(12 : Int),(12 : Int),(12 : Int),(12 : Int),(12 : Int),(12 : Int),(12 : Int),(12 : Int),(12 : Int),(12 : Int),(12 : Int),(12 : Int),(13 : Int),(13 : Int),(13 : Int),(13 : Int),(13 : Int),(14 : Int),(14 : Int),(14 : Int),(15 : Int),(15 : Int),(15 : Int),(15 : Int),(15 : Int),(15 : Int),(15 : Int),(15 : Int),(15 : Int),(15 : Int),(15 : Int)],
#[(5 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int),(6 : Int),(6 : Int),(6 : Int),(7 : Int),(7 : Int),(7 : Int),(8 : Int),(8 : Int),(8 : Int),(8 : Int),(8 : Int),(8 : Int),(8 : Int),(8 : Int),(8 : Int),(8 : Int),(8 : Int),(8 : Int),(8 : Int),(8 : Int),(9 : Int),(9 : Int),(9 : Int),(10 : Int),(10 : Int),(10 : Int),(11 : Int),(11 : Int),(11 : Int),(11 : Int),(11 : Int),(11 : Int),(11 : Int),(11 : Int),(11 : Int),(11 : Int),(11 : Int),(11 : Int),(11 : Int),(12 : Int),(12 : Int),(12 : Int),(12 : Int),(12 : Int),(13 : Int),(13 : Int),(13 : Int),(14 : Int),(14 : Int),(14 : Int),(14 : Int),(14 : Int),(14 : Int),(14 : Int),(14 : Int),(14 : Int),(14 : Int)],
#[(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(5 : Int),(5 : Int),(5 : Int),(6 : Int),(6 : Int),(6 : Int),(7 : Int),(7 : Int),(7 : Int),(7 : Int),(7 : Int),(7 : Int),(7 : Int),(7 : Int),(7 : Int),(7 : Int),(7 : Int),(7 : Int),(7 : Int),(7 : Int),(8 : Int),(8 : Int),(8 : Int),(9 : Int),(9 : Int),(9 : Int),(10 : Int),(10 : Int),(10 : Int),(10 : Int),(10 : Int),(10 : Int),(10 : Int),(10 : Int),(10 : Int),(10 : Int),(10 : Int),(10 : Int),(10 : Int),(10 : Int),(10 : Int),(10 : Int),(10 : Int),(10 : Int),(11 : Int),(11 : Int),(11 : Int),(11 : Int),(12 : Int),(12 : Int),(13 : Int),(13 : Int),(13 : Int),(13 : Int),(13 : Int),(13 : Int)],
#[(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(5 : Int),(5 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(7 : Int),(7 : Int),(8 : Int),(8 : Int),(8 : Int),(8 : Int),(9 : Int),(9 : Int),(9 : Int),(9 : Int),(9 : Int),(9 : Int),(9 : Int),(9 : Int),(9 : Int),(9 : Int),(9 : Int),(9 : Int),(9 : Int),(9 : Int),(10 : Int),(10 : Int),(10 : Int),(10 : Int),(11 : Int),(11 : Int),(12 : Int),(12 : Int),(12 : Int),(12 : Int),(12 : Int)],
#[(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(3 : Int),(3 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int),(6 : Int),(6 : Int),(7 : Int),(7 : Int),(7 : Int),(7 : Int),(8 : Int),(8 : Int),(8 : Int),(8 : Int),(8 : Int),(8 : Int),(8 : Int),(8 : Int),(8 : Int),(8 : Int),(8 : Int),(8 : Int),(8 : Int),(8 : Int),(9 : Int),(9 : Int),(9 : Int),(9 : Int),(10 : Int),(10 : Int),(10 : Int),(10 : Int),(10 : Int),(10 : Int)],
#[(1 : Int),(1 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(3 : Int),(3 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(7 : Int),(7 : Int),(7 : Int),(8 : Int),(8 : Int),(8 : Int),(8 : Int),(8 : Int),(8 : Int),(8 : Int),(8 : Int),(8 : Int),(8 : Int),(8 : Int),(8 : Int),(8 : Int),(8 : Int),(8 : Int),(8 : Int),(8 : Int),(9 : Int),(9 : Int),(9 : Int),(9 : Int),(9 : Int)],
#[(0 : Int),(0 : Int),(0 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(2 : Int),(2 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(5 : Int),(5 : Int),(5 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(7 : Int),(7 : Int),(7 : Int),(7 : Int),(7 : Int),(7 : Int),(7 : Int),(7 : Int),(7 : Int),(7 : Int),(7 : Int),(7 : Int),(7 : Int),(8 : Int),(8 : Int),(8 : Int),(8 : Int)],
#[(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(2 : Int),(2 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(4 : Int),(4 : Int),(4 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(7 : Int),(7 : Int),(7 : Int)],
#[(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(2 : Int),(2 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(5 : Int),(5 : Int),(5 : Int),(5 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int),(6 : Int)],
#[(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(1 : Int),(1 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int),(4 : Int)],
#[(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-1 : Int),(-1 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int),(3 : Int)],
#[(-6 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-2 : Int),(-2 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int)],
#[(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int),(2 : Int)],
#[(-6 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-5 : Int),(-5 : Int),(-5 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int),(1 : Int)],
#[(-7 : Int),(-7 : Int),(-7 : Int),(-7 : Int),(-7 : Int),(-7 : Int),(-7 : Int),(-7 : Int),(-7 : Int),(-7 : Int),(-7 : Int),(-7 : Int),(-7 : Int),(-7 : Int),(-7 : Int),(-7 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-6 : Int),(-5 : Int),(-5 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-4 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-3 : Int),(-2 : Int),(-2 : Int),(-2 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(-1 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int)],
#[(9 : Int),(9 : Int),(9 : Int),(9 : Int),(9 : Int),(10 : Int),(10 : Int),(10 : Int),(10 : Int),(10 : Int),(10 : Int),(10 : Int),(10 : Int),(10 : Int),(10 : Int),(10 : Int),(10 : Int),(11 : Int),(11 : Int),(11 : Int),(11 : Int),(11 : Int),(12 : Int),(12 : Int),(13 : Int),(13 : Int),(13 : Int),(13 : Int),(13 : Int),(13 : Int),(13 : Int),(13 : Int),(13 : Int),(13 : Int),(13 : Int),(13 : Int),(13 : Int),(13 : Int),(14 : Int),(14 : Int),(14 : Int),(15 : Int),(15 : Int),(15 : Int),(15 : Int),(15 : Int),(16 : Int),(16 : Int),(16 : Int),(16 : Int),(16 : Int),(16 : Int),(16 : Int),(16 : Int),(16 : Int),(16 : Int),(16 : Int),(16 : Int),(16 : Int),(16 : Int),(16 : Int),(16 : Int),(16 : Int),(16 : Int),(16 : Int)],
#[(8 : Int),(8 : Int),(8 : Int),(8 : Int),(8 : Int),(8 : Int),(9 : Int),(9 : Int),(9 : Int),(9 : Int),(9 : Int),(9 : Int),(9 : Int),(9 : Int),(9 : Int),(9 : Int),(9 : Int),(9 : Int),(10 : Int),(10 : Int),(10 : Int),(10 : Int),(10 : Int),(11 : Int),(11 : Int),(12 : Int),(12 : Int),(12 : Int),(12 : Int),(12 : Int),(12 : Int),(12 : Int),(12 : Int),(12 : Int),(12 : Int),(12 : Int),(12 : Int),(12 : Int),(12 : Int),(12 : Int),(12 : Int),(12 : Int),(12 : Int),(13 : Int),(13 : Int),(13 : Int),(13 : Int),(14 : Int),(14 : Int),(14 : Int),(14 : Int),(15 : Int),(15 : Int),(15 : Int),(15 : Int),(15 : Int),(15 : Int),(15 : Int),(15 : Int),(15 : Int),(15 : Int),(15 : Int),(15 : Int),(15 : Int),(15 : Int)],
#[(7 : Int),(7 : Int),(7 : Int),(7 : Int),(7 : Int),(7 : Int),(7 : Int),(8 : Int),(8 : Int),(8 : Int),(8 : Int),(8 : Int),(8 : Int),(8 : Int),(8 : Int),(8 : Int),(8 : Int),(8 : Int),(8 : Int),(8 : Int),(8 : Int),(8 : Int),(8 : Int),(8 : Int),(9 : Int),(9 : Int),(10 : Int),(10 : Int),(10 : Int),(10 : Int),(11 : Int),(11 : Int),(11 : Int),(11 : Int),(11 : Int),(11 : Int),(11 : Int),(11 : Int),(11 : Int),(11 : Int),(11 : Int),(11 : Int),(11 : Int),(11 : Int),(12 : Int),(12 : Int),(12 : Int),(12 : Int),(13 : Int),(13 : Int),(13 : Int),(13 : Int),(14 : Int),(14 : Int),(14 : Int),(14 : Int),(14 : Int),(14 : Int),(14 : Int),(14 : Int),(14 : Int),(14 : Int),(14 : Int),(14 : Int),(14 : Int)]]
def budgets : Array Int := #[(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(3 : Int),(0 : Int),(4 : Int),(0 : Int),(0 : Int),(0 : Int),(7 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(12 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(13 : Int),(0 : Int),(0 : Int),(0 : Int),(17 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(0 : Int),(2 : Int),(0 : Int),(0 : Int),(17 : Int),(0 : Int),(0 : Int)]

def unary (layer height : Nat) : Int :=
  (if (17 * ((64 - (35 * layer) % 64) % 64)) % 64 < height then 1 else 0) +
    (if height ≤ (17 * ((42 + 64 - (35 * layer) % 64) % 64)) % 64 then 1 else 0)

def suffixStepCheck (layer height : Nat) : Bool :=
  if height < 64 then
    decide ((suffixes[layer]!)[height]! =
      min ((potentials[layer]!)[height]!) ((suffixes[layer]!)[height + 1]!))
  else decide ((suffixes[layer]!)[64]! = (potentials[layer]!)[64]!)

def localCheck (layer current : Nat) : Bool :=
  let threshold := if current = 0 then 0 else current - 1
  decide (unary layer current ≤
    budgets[layer]! + (suffixes[(layer + 63) % 64]!)[threshold]! - (potentials[layer]!)[current]!)

def layerCheck (layer : Nat) : Bool :=
  (List.range 65).all (suffixStepCheck layer) &&
  (List.range 65).all (localCheck layer)

theorem certificate_layer_0 : layerCheck 0 = true := by
  unfold layerCheck
  decide

theorem certificate_layer_1 : layerCheck 1 = true := by
  unfold layerCheck
  decide

theorem certificate_layer_2 : layerCheck 2 = true := by
  unfold layerCheck
  decide

theorem certificate_layer_3 : layerCheck 3 = true := by
  unfold layerCheck
  decide

theorem certificate_layer_4 : layerCheck 4 = true := by
  unfold layerCheck
  decide

theorem certificate_layer_5 : layerCheck 5 = true := by
  unfold layerCheck
  decide

theorem certificate_layer_6 : layerCheck 6 = true := by
  unfold layerCheck
  decide

theorem certificate_layer_7 : layerCheck 7 = true := by
  unfold layerCheck
  decide

theorem certificate_layer_8 : layerCheck 8 = true := by
  unfold layerCheck
  decide

theorem certificate_layer_9 : layerCheck 9 = true := by
  unfold layerCheck
  decide

theorem certificate_layer_10 : layerCheck 10 = true := by
  unfold layerCheck
  decide

theorem certificate_layer_11 : layerCheck 11 = true := by
  unfold layerCheck
  decide

theorem certificate_layer_12 : layerCheck 12 = true := by
  unfold layerCheck
  decide

theorem certificate_layer_13 : layerCheck 13 = true := by
  unfold layerCheck
  decide

theorem certificate_layer_14 : layerCheck 14 = true := by
  unfold layerCheck
  decide

theorem certificate_layer_15 : layerCheck 15 = true := by
  unfold layerCheck
  decide

theorem certificate_layer_16 : layerCheck 16 = true := by
  unfold layerCheck
  decide

theorem certificate_layer_17 : layerCheck 17 = true := by
  unfold layerCheck
  decide

theorem certificate_layer_18 : layerCheck 18 = true := by
  unfold layerCheck
  decide

theorem certificate_layer_19 : layerCheck 19 = true := by
  unfold layerCheck
  decide

theorem certificate_layer_20 : layerCheck 20 = true := by
  unfold layerCheck
  decide

theorem certificate_layer_21 : layerCheck 21 = true := by
  unfold layerCheck
  decide

theorem certificate_layer_22 : layerCheck 22 = true := by
  unfold layerCheck
  decide

theorem certificate_layer_23 : layerCheck 23 = true := by
  unfold layerCheck
  decide

theorem certificate_layer_24 : layerCheck 24 = true := by
  unfold layerCheck
  decide

theorem certificate_layer_25 : layerCheck 25 = true := by
  unfold layerCheck
  decide

theorem certificate_layer_26 : layerCheck 26 = true := by
  unfold layerCheck
  decide

theorem certificate_layer_27 : layerCheck 27 = true := by
  unfold layerCheck
  decide

theorem certificate_layer_28 : layerCheck 28 = true := by
  unfold layerCheck
  decide

theorem certificate_layer_29 : layerCheck 29 = true := by
  unfold layerCheck
  decide

theorem certificate_layer_30 : layerCheck 30 = true := by
  unfold layerCheck
  decide

theorem certificate_layer_31 : layerCheck 31 = true := by
  unfold layerCheck
  decide

theorem certificate_layer_32 : layerCheck 32 = true := by
  unfold layerCheck
  decide

theorem certificate_layer_33 : layerCheck 33 = true := by
  unfold layerCheck
  decide

theorem certificate_layer_34 : layerCheck 34 = true := by
  unfold layerCheck
  decide

theorem certificate_layer_35 : layerCheck 35 = true := by
  unfold layerCheck
  decide

theorem certificate_layer_36 : layerCheck 36 = true := by
  unfold layerCheck
  decide

theorem certificate_layer_37 : layerCheck 37 = true := by
  unfold layerCheck
  decide

theorem certificate_layer_38 : layerCheck 38 = true := by
  unfold layerCheck
  decide

theorem certificate_layer_39 : layerCheck 39 = true := by
  unfold layerCheck
  decide

theorem certificate_layer_40 : layerCheck 40 = true := by
  unfold layerCheck
  decide

theorem certificate_layer_41 : layerCheck 41 = true := by
  unfold layerCheck
  decide

theorem certificate_layer_42 : layerCheck 42 = true := by
  unfold layerCheck
  decide

theorem certificate_layer_43 : layerCheck 43 = true := by
  unfold layerCheck
  decide

theorem certificate_layer_44 : layerCheck 44 = true := by
  unfold layerCheck
  decide

theorem certificate_layer_45 : layerCheck 45 = true := by
  unfold layerCheck
  decide

theorem certificate_layer_46 : layerCheck 46 = true := by
  unfold layerCheck
  decide

theorem certificate_layer_47 : layerCheck 47 = true := by
  unfold layerCheck
  decide

theorem certificate_layer_48 : layerCheck 48 = true := by
  unfold layerCheck
  decide

theorem certificate_layer_49 : layerCheck 49 = true := by
  unfold layerCheck
  decide

theorem certificate_layer_50 : layerCheck 50 = true := by
  unfold layerCheck
  decide

theorem certificate_layer_51 : layerCheck 51 = true := by
  unfold layerCheck
  decide

theorem certificate_layer_52 : layerCheck 52 = true := by
  unfold layerCheck
  decide

theorem certificate_layer_53 : layerCheck 53 = true := by
  unfold layerCheck
  decide

theorem certificate_layer_54 : layerCheck 54 = true := by
  unfold layerCheck
  decide

theorem certificate_layer_55 : layerCheck 55 = true := by
  unfold layerCheck
  decide

theorem certificate_layer_56 : layerCheck 56 = true := by
  unfold layerCheck
  decide

theorem certificate_layer_57 : layerCheck 57 = true := by
  unfold layerCheck
  decide

theorem certificate_layer_58 : layerCheck 58 = true := by
  unfold layerCheck
  decide

theorem certificate_layer_59 : layerCheck 59 = true := by
  unfold layerCheck
  decide

theorem certificate_layer_60 : layerCheck 60 = true := by
  unfold layerCheck
  decide

theorem certificate_layer_61 : layerCheck 61 = true := by
  unfold layerCheck
  decide

theorem certificate_layer_62 : layerCheck 62 = true := by
  unfold layerCheck
  decide

theorem certificate_layer_63 : layerCheck 63 = true := by
  unfold layerCheck
  decide

theorem certificate_layer_all (layer : Fin 64) :
    layerCheck layer.val = true := by
  fin_cases layer
  · exact certificate_layer_0
  · exact certificate_layer_1
  · exact certificate_layer_2
  · exact certificate_layer_3
  · exact certificate_layer_4
  · exact certificate_layer_5
  · exact certificate_layer_6
  · exact certificate_layer_7
  · exact certificate_layer_8
  · exact certificate_layer_9
  · exact certificate_layer_10
  · exact certificate_layer_11
  · exact certificate_layer_12
  · exact certificate_layer_13
  · exact certificate_layer_14
  · exact certificate_layer_15
  · exact certificate_layer_16
  · exact certificate_layer_17
  · exact certificate_layer_18
  · exact certificate_layer_19
  · exact certificate_layer_20
  · exact certificate_layer_21
  · exact certificate_layer_22
  · exact certificate_layer_23
  · exact certificate_layer_24
  · exact certificate_layer_25
  · exact certificate_layer_26
  · exact certificate_layer_27
  · exact certificate_layer_28
  · exact certificate_layer_29
  · exact certificate_layer_30
  · exact certificate_layer_31
  · exact certificate_layer_32
  · exact certificate_layer_33
  · exact certificate_layer_34
  · exact certificate_layer_35
  · exact certificate_layer_36
  · exact certificate_layer_37
  · exact certificate_layer_38
  · exact certificate_layer_39
  · exact certificate_layer_40
  · exact certificate_layer_41
  · exact certificate_layer_42
  · exact certificate_layer_43
  · exact certificate_layer_44
  · exact certificate_layer_45
  · exact certificate_layer_46
  · exact certificate_layer_47
  · exact certificate_layer_48
  · exact certificate_layer_49
  · exact certificate_layer_50
  · exact certificate_layer_51
  · exact certificate_layer_52
  · exact certificate_layer_53
  · exact certificate_layer_54
  · exact certificate_layer_55
  · exact certificate_layer_56
  · exact certificate_layer_57
  · exact certificate_layer_58
  · exact certificate_layer_59
  · exact certificate_layer_60
  · exact certificate_layer_61
  · exact certificate_layer_62
  · exact certificate_layer_63

theorem suffix_step_check_all (layer : Fin 64) (height : Fin 65) :
    suffixStepCheck layer.val height.val = true := by
  have h := certificate_layer_all layer
  have hparts :
      (List.range 65).all (suffixStepCheck layer.val) = true ∧
      (List.range 65).all (localCheck layer.val) = true := by
    simpa [layerCheck, Bool.and_eq_true] using h
  have hall := (List.all_eq_true.mp hparts.1) height.val (by simp)
  exact hall

theorem local_check_all (layer : Fin 64) (current : Fin 65) :
    localCheck layer.val current.val = true := by
  have h := certificate_layer_all layer
  have hparts :
      (List.range 65).all (suffixStepCheck layer.val) = true ∧
      (List.range 65).all (localCheck layer.val) = true := by
    simpa [layerCheck, Bool.and_eq_true] using h
  exact (List.all_eq_true.mp hparts.2) current.val (by simp)

theorem suffix_step_eq (layer : Fin 64) (height : Fin 65)
    (hh : height.val < 64) :
    (suffixes[layer.val]!)[height.val]! =
      min ((potentials[layer.val]!)[height.val]!)
        ((suffixes[layer.val]!)[height.val + 1]!) := by
  have h := suffix_step_check_all layer height
  unfold suffixStepCheck at h
  simp only [if_pos hh] at h
  exact of_decide_eq_true h

theorem suffix_terminal_eq (layer : Fin 64) :
    (suffixes[layer.val]!)[64]! = (potentials[layer.val]!)[64]! := by
  have h := suffix_step_check_all layer ⟨64, by omega⟩
  unfold suffixStepCheck at h
  simp only [if_neg (by omega : ¬ 64 < 64)] at h
  exact of_decide_eq_true h

theorem unary_local_ineq (layer : Fin 64) (current : Fin 65) :
    unary layer.val current.val ≤
      budgets[layer.val]! +
        (suffixes[(layer.val + 63) % 64]!)[if current.val = 0 then 0 else current.val - 1]! -
          (potentials[layer.val]!)[current.val]! := by
  have h := local_check_all layer current
  unfold localCheck at h
  exact of_decide_eq_true h

theorem delta_edge_inequality (layer : Fin 64) (current previous : Fin 65)
    (htransition : current.val ≤ previous.val + 1) :
    unary layer.val current.val ≤
      budgets[layer.val]! +
        (potentials[(layer.val + 63) % 64]!)[previous.val]! -
          (potentials[layer.val]!)[current.val]! := by
  let prior : Fin 64 := ⟨(layer.val + 63) % 64, Nat.mod_lt _ (by omega)⟩
  have hstep : ∀ h, h < 64 →
      (suffixes[prior.val]!)[h]! =
        min ((potentials[prior.val]!)[h]!) ((suffixes[prior.val]!)[h + 1]!) := by
    intro h hh
    have hs := suffix_step_eq prior ⟨h, by omega⟩ hh
    simpa using hs
  have hend : (suffixes[prior.val]!)[64]! = (potentials[prior.val]!)[64]! := by
    simpa using suffix_terminal_eq prior
  have hlocal : ∀ t : Fin 65,
      unary layer.val t.val ≤
        budgets[layer.val]! +
          (suffixes[prior.val]!)[if t.val = 0 then 0 else t.val - 1]! -
            (potentials[layer.val]!)[t.val]! := by
    intro t
    simpa using unary_local_ineq layer t
  exact Chvatal.D2Slope49Abstract.dual_edge_of_suffix_certificate
    (fun t => unary layer.val t.val)
    budgets[layer.val]!
    (fun h => (potentials[layer.val]!)[h]!)
    (fun h => (potentials[prior.val]!)[h]!)
    (fun h => (suffixes[prior.val]!)[h]!)
    hstep hend hlocal current previous htransition

end Chvatal.D2Slope49Certificate42
