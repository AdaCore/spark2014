package Assign_Aggr is

   type T is record
      X, Y, Z : Integer;
   end record;

   procedure Consume (U : T; Err : out Boolean);

   procedure Compute (V : out Integer);

end Assign_Aggr;
