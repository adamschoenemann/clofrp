stack build --profile --executable-profiling --library-profiling
if ($LastExitCode -eq 0) {
  stack exec clofrp-profile --RTS -- +RTS -s -p -hc "-i0.5" -L30
  # stack exec clofrp-profile --RTS -- +RTS -s -p -hy
  # .\.stack-work\dist\5c8418a7\build\clofrp-benchmarks\clofrp-benchmarks.exe +RTS -hc "-i0.5" -L30
  # .\.stack-work\dist\ca59d0ab\build\clofrp-benchmarks\clofrp-benchmarks.exe +RTS -hy
  # fix-hp \clofrp-benchmarks.hp \clofrp-benchmarks.hp
  hp2ps -c .\clofrp-profile.EXE.hp
  ps2pdf .\clofrp-profile.EXE.ps
}
