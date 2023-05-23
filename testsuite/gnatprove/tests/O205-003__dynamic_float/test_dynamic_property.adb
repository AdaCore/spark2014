procedure Test_Dynamic_Property (D : Float) with SPARK_Mode,
  Pre => D in 1.0 .. 100.0 is
   subtype Pos_Static_Float is Float range 1.0 .. 100.0;
   C : constant Pos_Static_Float := D; -- This indirection to D is needed so that we know D's range to check Nested
   subtype Pos_Dynamic_Float is Float range 1.0 .. C;
   X : Pos_Dynamic_Float := C;

   package Nested with Initializes => (Y => X)
   is
      subtype Dynamic_Float is Float range 0.0 .. C;
      Y : Dynamic_Float := X; --@RANGE_CHECK:PASS

      procedure Dyn_Param (X : in out Dynamic_Float) with
        Pre  => True,
        Post => X >= 1.0;
   end Nested;

   package body Nested is
      procedure Dyn_Param (X : in out Dynamic_Float) is
      begin
         if X + 1.0 <= C then
            X := X + 1.0;
         else
            X := 1.0;
         end if;
      end Dyn_Param;
   end Nested;

   function Dyn_Return (X : Float) return Pos_Dynamic_Float with
     Pre => True
   is
   begin
      if X > C or else X < 1.0 then
         return C;
      else
         return X;
      end if;
   end Dyn_Return;

   procedure Dyn_Param (X : in out Pos_Dynamic_Float) with
     Pre  => True
   is
   begin
      if X + 1.0 <= C then
         X := X + 1.0;
      else
         X := 1.0;
      end if;
   end Dyn_Param;
begin
   X := Dyn_Return (30.0);
   pragma Assert (X <= C); --@ASSERT:PASS
   pragma Assert (Dyn_Return (40.0) <= C); -- assert might fail because of cycle avoidance for VC modules
   Dyn_Param (X);
   pragma Assert (X <= C); --@ASSERT:PASS
   if Nested.Y >= 1.0 then
      Dyn_Param (Nested.Y); --@RANGE_CHECK:PASS
      pragma Assert (Nested.Y <= C); --@ASSERT:PASS
   end if;
   Nested.Dyn_Param (X); --@RANGE_CHECK:PASS
   pragma Assert (X <= C); --@ASSERT:PASS
end Test_Dynamic_Property;
