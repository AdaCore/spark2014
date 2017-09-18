with Ints; use Ints;

procedure Test_Ints
  with SPARK_Mode => Off
is
   I : Int := (Min => 0, Max => 100, Value => 42);
   AI : Approx_Int := (I with Precision => 5);
begin
   I.Display ("initial");
   AI.Display ("initial");

   Bump (I); -- call to Int.Bump
   I.Bump; -- call to Int.Bump (object.method notation)

   Bump (AI); -- call to Approx_Int.Bump
   Bump (Int(AI)); -- call to Int.Bump

   I.Display ("intermediate");
   AI.Display ("intermediate");

   declare
      IC : Int'Class := Int'Class(I);
   begin
      IC.Bump; -- call to Int.Bump
      IC.Display ("temporary");
   end;

   declare
      IC : Int'Class := Int'Class(AI);
   begin
      IC.Bump; -- call to Approx_Int.Bump
      IC.Display ("temporary");
   end;

   Call_Bump (Int'Class(I)); -- calls Int.Bump(I)
   Call_Bump (Int'Class(AI)); -- calls Approx_Int.Bump(AI)

   I.Display ("final");
   AI.Display ("final");
end Test_Ints;
