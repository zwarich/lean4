import Std.Internal.Async

open Std.Internal.IO.Async

def assertElapsed (t1 t2 : Nat) (should : Nat) (eps : Nat) : IO Unit := do
  let dur := t2 - t1
  if (Int.ofNat dur - Int.ofNat should).natAbs > eps then
    throw <| .userError s!"elapsed time was too different, measured {dur}, should: {should}, tolerance: {eps}"

def assertDuration (x : IO (AsyncTask α)) (should : Nat) (eps : Nat) : IO Unit := do
  let t1 ← IO.monoMsNow
  discard <| AsyncTask.spawnBlocking <| x
  let t2 ← IO.monoMsNow
  assertElapsed t1 t2 should eps

-- generous tolerance for slow CI systems
def EPS : Nat := 3

section Sleep

def timerSleep : IO Unit := do
  assertDuration go 20 EPS
where
  go : IO (AsyncTask Unit) := do
    let timer ← Sleep.mk 20
    timer.wait

def oneShotSleep : IO Unit := do
  assertDuration (sleep 20) 20 EPS

def promiseBehavior1 : IO Unit := do
  let timer ← Sleep.mk 20
  let prom ← timer.wait
  assert! (← prom.getState) != .finished
  IO.sleep (20 + EPS).toUInt32
  assert! (← prom.getState) == .finished

def promiseBehavior2 : IO Unit := do
  let timer ← Sleep.mk 20
  let prom1 ← timer.wait
  let prom2 ← timer.wait
  assert! (← prom1.getState) != .finished
  assert! (← prom2.getState) != .finished
  IO.sleep (20 + EPS).toUInt32
  assert! (← prom1.getState) == .finished
  assert! (← prom2.getState) == .finished

def promiseBehavior3 : IO Unit := do
  let timer ← Sleep.mk 20
  let prom1 ← timer.wait
  assert! (← prom1.getState) != .finished
  IO.sleep (20 + EPS).toUInt32
  assert! (← prom1.getState) == .finished

  let prom2 ← timer.wait
  -- currently fails
  assert! (← prom2.getState) == .finished

def resetBehavior : IO Unit := do
  let timer ← Sleep.mk 20
  let prom ← timer.wait
  assert! (← prom.getState) != .finished

  IO.sleep 10
  assert! (← prom.getState) != .finished
  timer.reset

  IO.sleep 10
  assert! (← prom.getState) != .finished

  IO.sleep (10 + EPS).toUInt32
  assert! (← prom.getState) == .finished

def parallelSleep : IO Unit := do
  assertDuration go 20 EPS
where
  go : IO (AsyncTask Unit) := do
    let s1 ← sleep 20
    let s2 ← sleep 10
    s1.bindIO fun _ =>
    s2.mapIO fun _ =>
      ()

def sequentialSleep1 : IO Unit := do
  assertDuration go 20 EPS
where
  go : IO (AsyncTask Unit) := do
    (← sleep 10).bindIO fun _ => do
    (← sleep 10).mapIO fun _ =>
      ()

def sequentialSleep2 : IO Unit := do
  assertDuration go 20 EPS
where
  go : IO (AsyncTask Unit) := do
    let s1 ← Sleep.mk 10
    let s2 ← Sleep.mk 10
    (← s1.wait).bindIO fun _ => do
    (← s2.wait).mapIO fun _ =>
      ()

#eval timerSleep
#eval oneShotSleep
#eval promiseBehavior1
#eval promiseBehavior2
#eval promiseBehavior3
#eval resetBehavior
#eval parallelSleep
#eval sequentialSleep1
#eval sequentialSleep2

end Sleep
