procedure Test with SPARK_Mode is

   type Root is tagged record
      F : Integer;
   end record;

   type Child is new Root with record
      G : Integer;
   end record;

   procedure Bad is
      C1 : Child := (1, 1);
      C2 : Child := (2, 2);
   begin
      Root (C1) := Root (C2);
      pragma Assert (C1.G = 2); -- @ASSERT:FAIL
   end Bad;

   procedure OK is
      C1 : Child := (1, 1);
      C2 : Child := (2, 2);
   begin
      Root (C1) := Root (C2);
      pragma Assert (C1.G = 1); -- @ASSERT:PASS
   end OK;

begin
   null;
end Test;
