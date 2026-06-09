package Inner_Pkg with SPARK_Mode => On is

   type Inner (Cap : Natural) is private;

private

   type Arr is array (Positive range <>) of Natural;

   type Inner (Cap : Natural) is record
      Data : Arr (1 .. Cap);
      N    : Natural := 0;
   end record
   with Dynamic_Predicate => Inner.N <= Inner.Cap;

end Inner_Pkg;
