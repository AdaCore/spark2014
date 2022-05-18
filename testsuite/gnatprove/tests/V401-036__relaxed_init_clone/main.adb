procedure Main (B : Boolean) with SPARK_Mode is
   package Nested is
      type T is private;
      C : constant T;
   private
      pragma SPARK_Mode (Off);
      type T is null record;
      C : constant T := (others => <>);
   end Nested;
   type T is new Nested.T;
   type Rel_T is record
      V : T;
   end record with Relaxed_Initialization;

   X : Rel_T;
begin
   if B then
      X.V := T (Nested.C);
   end if;
   pragma Assert (X'Initialized); --@ASSERT:FAIL
end;
