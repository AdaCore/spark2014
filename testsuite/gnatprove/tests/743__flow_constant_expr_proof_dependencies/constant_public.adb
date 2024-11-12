procedure Constant_Public with SPARK_Mode is
   type F is not null access function return Integer;
   function Z return Integer with
     Post => Z'Result = 0;

   C : constant F := Z'Access;

   type G is record
      B : Integer;
   end record with Predicate =>
     B /= C.all;

   function Z return Integer is
      V : G := (B => 1);
   begin
      return V.B - 1;
   end Z;

   V : Integer := Z;
begin
   pragma Assert (V = 0);
end;
