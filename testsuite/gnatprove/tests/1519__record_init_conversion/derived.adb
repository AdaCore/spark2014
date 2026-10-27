procedure Derived (Fully : Boolean) with SPARK_Mode is
   subtype Size is Positive range 1 .. 4;
   type Root (D : Size := 2) is record
      Data : String (1 .. D);
   end record;
   type Child is new Root;
   X : Child with Relaxed_Initialization;
begin
   pragma Assert (X.D = 2);
   X.Data (1) := 'a';
   pragma Assert (X.Data (1) = 'a');
   if Fully then
      X.Data (2) := 'b';
      pragma Assert (X'Initialized);
   else
      --  The other component must remain uninitialized.
      pragma Assert (X.Data (2)'Initialized); --@ASSERT:FAIL
   end if;
end Derived;
