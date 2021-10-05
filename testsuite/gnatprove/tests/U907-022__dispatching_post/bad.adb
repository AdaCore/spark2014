procedure Bad with SPARK_Mode is
   package P is
      type Object is tagged null record;

      function Real_Eq (O1, O2 : Object) return Boolean with
        Import,
        Ghost,
        Post'Class => Real_Eq'Result = (O1 = O2);
   end P;
   use P;

   procedure Dummy (X, Y : Object'Class)
   is
   begin
      pragma Assert (not Real_Eq (X, Y)); --@ASSERT:FAIL
   end Dummy;
begin
   null;
end Bad;
