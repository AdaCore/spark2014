package Sat is

   subtype My_Int is Integer range 0 .. 10_000;

   function Add (X , Y : My_Int) return My_Int with
     Contract_Case => (Name     => "normal operation",
                       Mode     => Nominal,
                       Requires => X + Y < 10_000,
                       Ensures  => Add'Result = X + Y),
     Contract_Case => (Name     => "saturating",
                       Mode     => Nominal,
                       Requires => X + Y >= 10_000,
                       Ensures  => Add'Result = 10_000);

   function Mult (X , Y : My_Int) return My_Int with
     Contract_Case => (Name     => "normal operation",
                       Mode     => Nominal,
                       Requires => X * Y < 10_000,
                       Ensures  => Mult'Result = X * Y),
     Contract_Case => (Name     => "saturating",
                       Mode     => Nominal,
                       Requires => X * Y >= 10_000,
                       Ensures  => Mult'Result = 10_000);

end Sat;
