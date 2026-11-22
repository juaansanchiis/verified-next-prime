import DeterministicMR

axiom rh_alpoege : RiemannHypothesis
axiom grh_alpoege : DeterministicMR.DirichletGRH

def main (args : List String) : IO Unit := do
  let x : ℕ ← match args with
    | [] => pure (2 ^ 128)
    | s :: _ =>
      match s.toNat? with
      | some n => pure n
      | none =>
        IO.println s!"Error: '{s}' no es un número natural válido."
        IO.Process.exit 1

  if h : 4 ≤ x then
    let bits := Nat.log2 x + 1
    let bound := VerifiedNextPrime.searchBound x
    IO.println s!"Buscando el siguiente primo > x ({bits} bits)..."
    IO.println s!"  x           = {x}"
    IO.println s!"  searchBound = {bound} candidatos máx."

    let t0 ← IO.monoMsNow
    let p := DeterministicMR.nextPrimeFast rh_alpoege grh_alpoege x h
    let t1 ← IO.monoMsNow

    IO.println s!"\n[✓] Primo encontrado en {t1 - t0} ms:"
    IO.println s!"  p           = {p}"
    IO.println s!"  hueco (p-x) = {p - x}"
  else
    IO.println "Error: x debe ser mayor o igual que 4."
    IO.Process.exit 1
