package Pump is
   subtype Nat_Type is Natural range 0 .. 1_000;

   type Pump_Record is record
      Name      : String (1 .. 10);
      Resevoir  : Nat_Type;
      Price     : Nat_Type;
      Remaining : Nat_Type;
   end record;

end Pump;
