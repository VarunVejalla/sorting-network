param(
  [Parameter(Mandatory=$true)][string]$LeanExe,
  [Parameter(Mandatory=$true)][string]$BestLib,
  [string]$BuildDir,
  [string]$Endpoint = 'FrontierFlowAxioms'
)

# Focused source rebuild of the UB-23 endpoint and its local dependencies.
# Shared package/best artifacts are read; no cache is deleted or downloaded.
$ErrorActionPreference = 'Stop'
$sourceDir = $PSScriptRoot
$repositoryRoot = Split-Path (Split-Path (Split-Path $sourceDir -Parent) -Parent) -Parent
if (-not $BuildDir) { $BuildDir = Join-Path $repositoryRoot 'LLM-helpers/ub23-build' }
$LeanExe = (Resolve-Path -LiteralPath $LeanExe).Path
$BestLib = (Resolve-Path -LiteralPath $BestLib).Path
New-Item -ItemType Directory -Path $BuildDir -Force | Out-Null
$BuildDir = (Resolve-Path -LiteralPath $BuildDir).Path
$dependencyPaths = Get-ChildItem (Join-Path $repositoryRoot '.lake/packages') -Directory |
  ForEach-Object { Join-Path $_.FullName '.lake/build/lib/lean' }
$env:LEAN_PATH = (@($BuildDir,$sourceDir,$BestLib) + $dependencyPaths) -join ';'

$seenModules = [Collections.Generic.HashSet[string]]::new()
$orderedModules = [Collections.Generic.List[string]]::new()
function Visit-FlowModule([string]$moduleName) {
  if (-not $seenModules.Add($moduleName)) { return }
  foreach ($importLine in [IO.File]::ReadAllLines((Join-Path $sourceDir ($moduleName + '.lean')))) {
    if ($importLine -match '^import\s+([A-Za-z0-9_.]+)') {
      $importName = $Matches[1]
      if (Test-Path -LiteralPath (Join-Path $sourceDir ($importName + '.lean'))) {
        Visit-FlowModule $importName
      }
    }
  }
  $orderedModules.Add($moduleName)
}
Visit-FlowModule $Endpoint

$manifest = @()
$moduleIndex = 0
foreach ($moduleName in $orderedModules) {
  $moduleSource = Join-Path $sourceDir ($moduleName + '.lean')
  $moduleLog = Join-Path $BuildDir ($moduleName + '.log')
  $sourceHash = (Get-FileHash -LiteralPath $moduleSource -Algorithm SHA256).Hash
  & $LeanExe -o (Join-Path $BuildDir ($moduleName + '.olean')) $moduleSource *> $moduleLog
  $moduleExit = $LASTEXITCODE
  if ($moduleExit -ne 0) {
    Get-Content -LiteralPath $moduleLog -Encoding utf8
    Write-Output ($moduleName + ': FAIL ' + $moduleExit)
    exit $moduleExit
  }
  if ((Get-FileHash -LiteralPath $moduleSource -Algorithm SHA256).Hash -ne $sourceHash) {
    throw ('Source changed during check: ' + $moduleName)
  }
  $manifest += [pscustomobject]@{
    module=$moduleName; sha256=$sourceHash; checkedUtc=[DateTime]::UtcNow.ToString('o')
  }
  $manifest | ConvertTo-Json -Depth 4 |
    Set-Content (Join-Path $BuildDir 'manifest.json') -Encoding utf8
  $moduleIndex++
  Write-Output ('[' + $moduleIndex + '/' + $orderedModules.Count + '] ' + $moduleName + ': PASS')
}
Write-Output ($Endpoint + ' dependency chain and axiom guards: PASS')
