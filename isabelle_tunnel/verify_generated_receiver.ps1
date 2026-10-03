param(
    [Parameter(Mandatory=$true)]
    [string]$IsabelleRoot,
    [string]$Python = 'python',
    [string]$PolyML = '',
    [switch]$Smoke
)

$ErrorActionPreference = 'Stop'
$projectDirectory = $PSScriptRoot
$Python = (Get-Command $Python -ErrorAction Stop).Source
$bashExecutable = Join-Path $IsabelleRoot 'contrib\cygwin\bin\bash.exe'
if ($PolyML -eq '') {
    $PolyML = Join-Path $IsabelleRoot 'contrib\polyml-5.9.2-2\x86_64_32-windows\poly.exe'
}

function ConvertTo-CygwinPath([string]$Path) {
    $absolute = [IO.Path]::GetFullPath($Path)
    if ($absolute -notmatch '^([A-Za-z]):[\\/](.*)$') {
        throw "A local Windows drive path is required: $absolute"
    }
    '/cygdrive/' + $Matches[1].ToLowerInvariant() + '/' + $Matches[2].Replace('\', '/')
}

function Quote-BashLiteral([string]$Value) {
    $apostrophe = [string][char]39
    $doubleQuote = [string][char]34
    $escapedQuote = $apostrophe + $doubleQuote + $apostrophe + $doubleQuote + $apostrophe
    $apostrophe + $Value.Replace($apostrophe, $escapedQuote) + $apostrophe
}

function Invoke-Isabelle([string]$Arguments) {
    $tool = Quote-BashLiteral (ConvertTo-CygwinPath (Join-Path $IsabelleRoot 'bin\isabelle'))
    & $bashExecutable -l -c ($tool + ' ' + $Arguments)
    if ($LASTEXITCODE -ne 0) { throw "Isabelle exited with status $LASTEXITCODE" }
}

foreach ($required in @($bashExecutable, $Python, $PolyML)) {
    if (-not (Test-Path -LiteralPath $required -PathType Leaf)) {
        throw "Required executable is missing: $required"
    }
}

$localCore = Join-Path $projectDirectory 'generated\ReceiverGate.ML'
if (-not (Test-Path -LiteralPath $localCore -PathType Leaf)) {
    throw 'generated/ReceiverGate.ML is missing. Extract the named Isabelle export before running this verifier.'
}

$exportDirectory = Join-Path $projectDirectory ('.receiver-export-' + [guid]::NewGuid().ToString('N'))
$null = New-Item -ItemType Directory -Path $exportDirectory
$freshCore = Join-Path $exportDirectory 'ReceiverGate.ML'
$keepExport = $false

try {
    $projectUnix = Quote-BashLiteral (ConvertTo-CygwinPath $projectDirectory)
    Invoke-Isabelle ('build -o timeout=90 -o threads=2 -v -D ' + $projectUnix)
    $exportUnix = Quote-BashLiteral (ConvertTo-CygwinPath $exportDirectory)
    Invoke-Isabelle ('export -n -O ' + $exportUnix +
        ' -p 2 -x ''Tunnel_Knowledge.Receiver_Codegen:code/ReceiverGate.ML'' Tunnel_Knowledge')

    $localBytes = [IO.File]::ReadAllBytes($localCore)
    $freshBytes = [IO.File]::ReadAllBytes($freshCore)
    if ([Convert]::ToBase64String($localBytes) -cne [Convert]::ToBase64String($freshBytes)) {
        $keepExport = $true
        throw "The local core differs from the current session export. Nothing was overwritten. Inspect: $freshCore"
    }
    Write-Output 'PASS: local generated core is byte-for-byte identical to the freshly retrieved session export.'

    $testArguments = @((Join-Path $projectDirectory 'check_generated_receiver.py'), '--polyml', $PolyML)
    if ($Smoke) { $testArguments += '--smoke' }
    & $Python @testArguments
    if ($LASTEXITCODE -ne 0) { throw "Generated receiver tests failed with status $LASTEXITCODE" }

    & $Python (Join-Path $projectDirectory 'check_receiver_negative_controls.py') --polyml $PolyML
    if ($LASTEXITCODE -ne 0) { throw "Receiver negative controls failed with status $LASTEXITCODE" }

    & $Python (Join-Path $projectDirectory 'check_receiver_binding.py')
    if ($LASTEXITCODE -ne 0) { throw "Independent receiver checks failed with status $LASTEXITCODE" }

    Write-Output 'PASS: current proof session, export provenance, generated receiver execution, isolated-copy controls, and independent receiver checks.'
}
finally {
    # These are the exact two objects created for this invocation. No recursive
    # deletion or generated-core overwrite is performed, including on failure.
    if (-not $keepExport) {
        if (Test-Path -LiteralPath $freshCore -PathType Leaf) {
            Remove-Item -LiteralPath $freshCore
        }
        if (Test-Path -LiteralPath $exportDirectory -PathType Container) {
            Remove-Item -LiteralPath $exportDirectory
        }
    }
}
