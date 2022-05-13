pragma SPARK_Mode(On);

with Ada.Numerics.Big_Numbers.Big_Integers;
use Ada.Numerics.Big_Numbers.Big_Integers;

procedure Bigint_Generic is
   procedure Plane is
      type Point1D is record X : Big_Integer; end record;
   begin
      pragma Assert (Point1D'(X => 0) = Point1D'(X => 0));
   end;

   generic
      type T (<>) is private;
   package P is
      function Identity (X:T) return T
        with Post => Identity'Result = X;
   end P;
   package body P is
      function Identity (X:T) return T is
      begin
         return X;
      end;
   end P;
   package PI is new P(Big_Integer);
   X : Big_Integer := PI.Identity(0);
begin
   pragma Assert(X = 0);
end;
