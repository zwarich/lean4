def mkArray3 (a b c : Float32) : Array Float32 := #[a, b, c]

def sumArray (array : Array Float32) : Float32 :=
  array.foldl (init := 0.0) fun sum a => sum + a

#guard (mkArray3 1.0 2.0 4.0 |> sumArray) == 7.0
