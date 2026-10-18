param(
  [Parameter(Mandatory=$true)][string]$LeanExe,
  [Parameter(Mandatory=$true)][string]$BestLib,
  [string]$BuildDir
)

$ErrorActionPreference = 'Stop'
if (-not $BuildDir) {
  $repositoryRoot = Split-Path (Split-Path (Split-Path $PSScriptRoot -Parent) -Parent) -Parent
  $BuildDir = Join-Path $repositoryRoot 'LLM-helpers/ub24-build'
}
& (Join-Path $PSScriptRoot 'check-flow.ps1') -LeanExe $LeanExe -BestLib $BestLib `
  -BuildDir $BuildDir -Endpoint 'FrontierRankAxioms'
exit $LASTEXITCODE
