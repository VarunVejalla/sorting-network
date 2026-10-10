import Lake
open Lake DSL

package expanders where
  packagesDir := "../../../.lake/packages"
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`weak.linter.style.multiGoal, true⟩
  ]

-- Reuse the repository's checked-out Mathlib source; this package does not
-- depend on the root AKS package. Its small AKS source closure lives here.
require "leanprover-community" / "mathlib" @ git "master"

lean_lib AKS where
  globs := #[.one `AKS.Misc.Fin, .one `AKS.Misc.List,
    .one `AKS.Graph.Regular, .one `AKS.ZigZag.RVWBound,
    .one `AKS.ZigZag.RVWInequality]

lean_lib RandomCert where
  roots := #[`Random.Cert]
  precompileModules := true

lean_lib RandomBridge where
  globs := #[.submodules `Random.Bridge]

lean_lib RandomConcrete where
  globs := #[.submodules `Random.Concrete]

lean_lib RandomMisc where
  globs := #[.submodules `Random.Misc]

lean_lib RandomBench where
  globs := #[.submodules `Random.Bench]

extern_lib mmap pkg := do
  let srcJob ← inputBinFile (pkg.dir / "Random" / "Cert" / "mmap_string.c")
  let oJob ← buildO (pkg.buildDir / "Random" / "Cert" / "mmap_string.o") srcJob
    (weakArgs := #["-I", (← getLeanIncludeDir).toString, "-fPIC"])
  buildStaticLib (pkg.buildDir / "lib" / nameToStaticLib "mmap") #[oJob]

lean_exe "cert-bench" where
  root := `Random.Bench.CertBench

lean_exe "cert-test" where
  root := `Random.Bench.CertTest

lean_exe "cert-profile" where
  root := `Random.Bench.CertProfile

lean_exe "test-mmap" where
  root := `Random.Bench.TestMmap

lean_exe "bench-decomp" where
  root := `Random.Bench.BenchDecomp
