param([switch]$InLake,
    [ValidateSet('OddEvenMerge64', 'PacketUnequalMerge', 'PacketMergeTree', 'PacketAlignment', 'PacketRepair64', 'PacketGenMerge', 'PacketMergeTreeGen', 'PacketInduction', 'PacketReceiverResidue', 'PacketRebinning', 'PacketSenderCycle', 'PacketCountBridge', 'PacketProfile', 'PacketHalfProfile', 'PacketMergeAxioms')]
    [string]$From = 'OddEvenMerge64')

$ErrorActionPreference = 'Stop'
$packetSources = $PSScriptRoot
$packetWorkspace = (Resolve-Path (Join-Path $packetSources '../../..')).Path
$packetBest = (Resolve-Path (Join-Path $packetSources '../../best')).Path

if (-not $InLake) {
    Push-Location $packetBest
    try {
        & lake build AKS.Chvatal.StageNet AKS.Chvatal.ExecPlacement AKS.Sort.Untangle
        if ($LASTEXITCODE -ne 0) { exit $LASTEXITCODE }
        & lake env powershell -NoProfile -ExecutionPolicy Bypass -File $PSCommandPath -InLake -From $From
        $packetExit = $LASTEXITCODE
    } finally { Pop-Location }
    exit $packetExit
}

$packetBuild = Join-Path $packetWorkspace 'LLM-helpers/ub25-packets'
New-Item -ItemType Directory -Force $packetBuild | Out-Null
$env:LEAN_PATH = $packetBuild + ';' + $env:LEAN_PATH

$packetStarted = $false
foreach ($packetModule in @('OddEvenMerge64', 'PacketUnequalMerge', 'PacketMergeTree', 'PacketAlignment', 'PacketRepair64', 'PacketGenMerge', 'PacketMergeTreeGen', 'PacketInduction', 'PacketReceiverResidue', 'PacketRebinning', 'PacketSenderCycle', 'PacketCountBridge', 'PacketProfile', 'PacketHalfProfile', 'PacketMergeAxioms')) {
    if ($packetModule -eq $From) { $packetStarted = $true }
    if (-not $packetStarted) { continue }
    $packetSource = Join-Path $packetSources ($packetModule + '.lean')
    $packetObject = Join-Path $packetBuild ($packetModule + '.olean')
    $packetLog = Join-Path $packetBuild ($packetModule + '.log')
    $ErrorActionPreference = 'Continue'
    & lean "--root=$packetSources" -o $packetObject $packetSource *> $packetLog
    $packetCompileExit = $LASTEXITCODE
    $ErrorActionPreference = 'Stop'
    if ($packetCompileExit -ne 0) {
        Get-Content $packetLog
        exit $packetCompileExit
    }
    Write-Output ($packetModule + ': checked')
}
