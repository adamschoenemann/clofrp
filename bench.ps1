stack bench --no-run-benchmarks --profile --executable-profiling --library-profiling
if ($LastExitCode -eq 0) {
  .\.stack-work\dist\ca59d0ab\build\clofrp-benchmarks\clofrp-benchmarks.exe +RTS -hc "-i0.5" -L30
  # .\.stack-work\dist\ca59d0ab\build\clofrp-benchmarks\clofrp-benchmarks.exe +RTS -hy
  # fix-hp \clofrp-benchmarks.hp \clofrp-benchmarks.hp
  hp2ps -c .\clofrp-benchmarks.hp
  ps2pdf .\clofrp-benchmarks.ps
}
