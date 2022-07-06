package Elementary_Functions_Wrapper with SPARK_Mode is

   function Sqrt (X : Float) return Float with
     Pre  => X >= 0.0,
     Post => Sqrt'Result >= 0.0
       and then (if X = 0.0 then Sqrt'Result = 0.0)
       and then (if X = 1.0 then Sqrt'Result = 1.0)
       and then (if X >= Float'Succ (0.0) then Sqrt'Result > 0.0);

   function Log (X : Float) return Float with
     Pre  => X > 0.0,
     Post => (if X = 1.0 then Log'Result = 0.0);

   function Log (X, Base : Float) return Float with
     Pre  => X > 0.0 and Base > 0.0 and Base /= 1.0,
     Post => (if X = 1.0 then Log'Result = 0.0);

   function Exp (X : Float) return Float with
     Post => (if X = 0.0 then Exp'Result = 1.0);

   function "**" (Left, Right : Float) return Float with
     Pre  => (if Left = 0.0 then Right > 0.0) and Left >= 0.0,
     Post => "**"'Result >= 0.0
       and then (if Right = 0.0 then "**"'Result = 1.0)
       and then (if Right = 1.0 then "**"'Result = Left)
       and then (if Left  = 1.0 then "**"'Result = 1.0)
       and then (if Left  = 0.0 then "**"'Result = 0.0);

   function Sin (X : Float) return Float with
     Inline,
     Post => Sin'Result in -1.0 .. 1.0
       and then (if X = 0.0 then Sin'Result = 0.0);

   function Sin (X, Cycle : Float) return Float with
     Pre  => Cycle > 0.0,
     Post => Sin'Result in -1.0 .. 1.0
       and then (if X = 0.0 then Sin'Result = 0.0);

   function Cos (X : Float) return Float with
     Inline,
     Post => Cos'Result in -1.0 .. 1.0
       and then (if X = 0.0 then Cos'Result = 1.0);

   function Cos (X, Cycle : Float) return Float with
     Pre  => Cycle > 0.0,
     Post => Cos'Result in -1.0 .. 1.0
       and then (if X = 0.0 then Cos'Result = 1.0);

   function Tan (X : Float) return Float with
     Post => (if X = 0.0 then Tan'Result = 0.0);

   function Tan (X, Cycle : Float) return Float with
     Pre  => Cycle > 0.0
       and then abs Float'Remainder (X, Cycle) /= 0.25 * Cycle,
     Post => (if X = 0.0 then Tan'Result = 0.0);

   function Cot (X : Float) return Float with
     Pre => X /= 0.0;

   function Cot (X, Cycle : Float) return Float with
     Pre => Cycle > 0.0
       and then X /= 0.0
       and then Float'Remainder (X, Cycle) /= 0.0
       and then abs Float'Remainder (X, Cycle) /= 0.5 * Cycle;

   function Arcsin (X : Float) return Float with
     Pre  => abs X <= 1.0,
     Post => (if X = 0.0 then Arcsin'Result = 0.0);

   function Arcsin (X, Cycle : Float) return Float with
     Pre  => Cycle > 0.0 and abs X <= 1.0,
     Post => (if X = 0.0 then Arcsin'Result = 0.0);

   function Arccos (X : Float) return Float with
     Pre  => abs X <= 1.0,
     Post => (if X = 1.0 then Arccos'Result = 0.0);

   function Arccos (X, Cycle : Float) return Float with
     Pre  => Cycle > 0.0 and abs X <= 1.0,
     Post => (if X = 1.0 then Arccos'Result = 0.0);

   function Arctan
     (Y : Float;
      X : Float := 1.0) return Float
   with
     Pre  => X /= 0.0 or Y /= 0.0,
     Post => (if X > 0.0 and then Y = 0.0 then Arctan'Result = 0.0);

   function Arctan
     (Y     : Float;
      X     : Float := 1.0;
      Cycle : Float) return Float
   with
     Pre  => Cycle > 0.0 and (X /= 0.0 or Y /= 0.0),
     Post => (if X > 0.0 and then Y = 0.0 then Arctan'Result = 0.0);

   function Arccot
     (X   : Float;
      Y   : Float := 1.0) return Float
   with
     Pre  => X /= 0.0 or Y /= 0.0,
     Post => (if X > 0.0 and then Y = 0.0 then Arccot'Result = 0.0);

   function Arccot
     (X     : Float;
      Y     : Float := 1.0;
      Cycle : Float) return Float
   with
     Pre  => Cycle > 0.0 and (X /= 0.0 or Y /= 0.0),
     Post => (if X > 0.0 and then Y = 0.0 then Arccot'Result = 0.0);

   function Sinh (X : Float) return Float with
     Post => (if X = 0.0 then Sinh'Result = 0.0);

   function Cosh (X : Float) return Float with
     Post => Cosh'Result >= 1.0
       and then (if X = 0.0 then Cosh'Result = 1.0);

   function Tanh (X : Float) return Float with
     Post => Tanh'Result in -1.0 .. 1.0
       and then (if X = 0.0 then Tanh'Result = 0.0);

   function Coth (X : Float) return Float with
     Pre  => X /= 0.0,
     Post => abs Coth'Result >= 1.0;

   function Arcsinh (X : Float) return Float with
     Post => (if X = 0.0 then Arcsinh'Result = 0.0);

   function Arccosh (X : Float) return Float with
     Pre  => X >= 1.0,
     Post => Arccosh'Result >= 0.0
       and then (if X = 1.0 then Arccosh'Result = 0.0);

   function Arctanh (X : Float) return Float with
     Pre  => abs X < 1.0,
     Post => (if X = 0.0 then Arctanh'Result = 0.0);

   function Arccoth (X : Float) return Float with
     Pre => abs X > 1.0;

end Elementary_Functions_Wrapper;
