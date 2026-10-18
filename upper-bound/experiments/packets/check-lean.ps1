param([switch]$InLake,
    [ValidateSet('OddEvenMerge64', 'PacketUnequalMerge', 'PacketMergeTree', 'PacketAlignment', 'PacketRepair64', 'PacketGenMerge', 'PacketMergeTreeGen', 'PacketInduction', 'PacketReceiverResidue', 'PacketRebinning', 'PacketSenderCycle', 'PacketCountBridge', 'PacketProfile', 'PacketHalfProfile', 'PacketReceiverOverlap', 'PacketMergeAxioms', 'RankDriftBound')]
    [string]$From = 'OddEvenMerge64',
    [ValidateSet('OddEvenMerge64', 'PacketUnequalMerge', 'PacketMergeTree', 'PacketAlignment', 'PacketRepair64', 'PacketGenMerge', 'PacketMergeTreeGen', 'PacketInduction', 'PacketReceiverResidue', 'PacketRebinning', 'PacketSenderCycle', 'PacketCountBridge', 'PacketProfile', 'PacketHalfProfile', 'PacketReceiverOverlap', 'PacketMergeAxioms', 'RankDriftBound')]
    [string]$To = 'PacketMergeAxioms')

$ErrorActionPreference = 'Stop'
$packetSources = $PSScriptRoot
$packetWorkspace = (Resolve-Path (Join-Path $packetSources '../../..')).Path
$packetBest = (Resolve-Path (Join-Path $packetSources '../../best')).Path

if (-not $InLake) {
    Push-Location $packetBest
    try {
        $packetDepsDir = Join-Path $packetWorkspace 'LLM-helpers/ub25-packets'
        New-Item -ItemType Directory -Force $packetDepsDir | Out-Null
        $packetDepsLog = Join-Path $packetDepsDir 'lake-deps.log'
        & lake build AKS.Chvatal.StageNet AKS.Chvatal.ExecPlacement AKS.Sort.Untangle *> $packetDepsLog
        if ($LASTEXITCODE -ne 0) { Get-Content $packetDepsLog; exit $LASTEXITCODE }
        & lake env powershell -NoProfile -ExecutionPolicy Bypass -File $PSCommandPath -InLake -From $From -To $To
        $packetExit = $LASTEXITCODE
    } finally { Pop-Location }
    exit $packetExit
}

$packetBuild = Join-Path $packetWorkspace 'LLM-helpers/ub25-packets'
New-Item -ItemType Directory -Force $packetBuild | Out-Null
$env:LEAN_PATH = $packetBuild + ';' + $env:LEAN_PATH
$packetLintOptions = @(
    '-D', 'linter.unusedSimpArgs=false',
    '-D', 'linter.unusedVariables=false',
    '-D', 'linter.unnecessarySimpa=false',
    '-D', 'linter.unusedTactic=false',
    '-D', 'linter.unreachableTactic=false',
    '-D', 'weak.linter.unnecessarySeqFocus=false',
    '-D', 'linter.deprecated=false',
    '-D', 'weak.linter.style.multiGoal=false'
)

$packetStarted = $false
foreach ($packetModule in @('OddEvenMerge64', 'PacketUnequalMerge', 'PacketMergeTree', 'PacketAlignment', 'PacketRepair64', 'PacketGenMerge', 'PacketMergeTreeGen', 'PacketInduction', 'PacketReceiverResidue', 'PacketRebinning', 'PacketSenderCycle', 'PacketCountBridge', 'PacketProfile', 'PacketHalfProfile', 'PacketReceiverOverlap', 'PacketMergeAxioms', 'RankDriftBound')) {
    if ($packetModule -eq $From) { $packetStarted = $true }
    if (-not $packetStarted) { continue }
    $packetSource = Join-Path $packetSources ($packetModule + '.lean')
    $packetObject = Join-Path $packetBuild ($packetModule + '.olean')
    $packetLog = Join-Path $packetBuild ($packetModule + '.log')
    $ErrorActionPreference = 'Continue'
    & lean "--root=$packetSources" @packetLintOptions -o $packetObject $packetSource *> $packetLog
    $packetCompileExit = $LASTEXITCODE
    $ErrorActionPreference = 'Stop'
    if ($packetCompileExit -ne 0) {
        Get-Content $packetLog
        exit $packetCompileExit
    }
    Write-Output ($packetModule + ': checked')
    if ($packetModule -eq $To) { break }
}
