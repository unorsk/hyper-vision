# hyper-vision

Turbo Vision for Lean 4.

![hyper-vision demo](docs/demo.gif)

```sh
lake build && .lake/build/bin/hyper-vision-demo   # proofs are checked by the build
lake test                                         # property tests and fuzzing
```

A command handler (`App.onCommand`) can start background `Job`s: `IO` actions that
run off the event loop so slow work does not freeze the UI. When a job finishes its
result is delivered back on the main loop and dispatched as an ordinary application
command. Press `F7` in the demo to start a fake async scan and watch the spinner
animate while the windows stay live.
