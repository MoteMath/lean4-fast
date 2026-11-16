param(
    [string]$LeanExe = "C:\Users\devin\.elan\toolchains\leanprover--lean4---v4.35.0\bin\lean.exe",
    [string]$AdvDir = "C:\Users\devin\Desktop\lean\benchmarks\downstream_bench\adversarial"
)

$ErrorActionPreference = "Continue"
$passed = 0
$failed = 0

Get-ChildItem "$AdvDir\*.lean" | Sort-Object Name | ForEach-Object {
    $name = $_.Name
    $out = & $LeanExe -E error $_.FullName 2>&1 | Out-String
    $rc = $LASTEXITCODE

    if ($name -eq "sorry_guard.lean") {
        if ($out -match "sorryAx") {
            Write-Output "[PASS-REJECT] $name (detected sorryAx via #print axioms)"
            $passed++
        } else {
            Write-Output "[FAIL] $name was NOT flagged for sorryAx! exit=$rc`n$out"
            $failed++
        }
    } elseif ($name -eq "env_hack_axiom.lean") {
        if ($out -match "fakeUnsoundAxiom") {
            Write-Output "[PASS-REJECT] $name (detected custom axiom fakeUnsoundAxiom)"
            $passed++
        } else {
            Write-Output "[FAIL] $name did NOT expose fakeUnsoundAxiom! exit=$rc`n$out"
            $failed++
        }
    } else {
        if ($rc -ne 0) {
            Write-Output "[PASS-REJECT] $name (rejected with exit=$rc)"
            $passed++
        } else {
            Write-Output "[FAIL] $name was ACCEPTED unexpectedly! exit=$rc`n$out"
            $failed++
        }
    }
}

Write-Output "Adversarial Summary: $passed passed (rejected), $failed failed"
if ($failed -ne 0) { exit 1 }
