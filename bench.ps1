stack bench --no-run-benchmarks --profile --executable-profiling --library-profiling
if ($LastExitCode -eq 0) {
  .\.stack-work\dist\ca59d0ab\build\clott-benchmarks\clott-benchmarks.exe +RTS -hc "-i0.5" -L50
  # fix-hp \clott-benchmarks.hp \clott-benchmarks.hp
  hp2ps -e8in -c .\clott-benchmarks.hp
  ps2pdf .\clott-benchmarks.ps
}
