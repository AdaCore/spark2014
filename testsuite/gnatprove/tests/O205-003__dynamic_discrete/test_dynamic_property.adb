procedure Test_Dynamic_Property (C : Positive) with SPARK_Mode is
   subtype Pos_Dynamic_Discrete is Positive range 1 .. C;
   X : Pos_Dynamic_Discrete := C;

   package Nested with Initializes => (Y => X)
   is
      subtype Dynamic_Discrete is Natural range 0 .. C;
      Y : Dynamic_Discrete := X; --@RANGE_CHECK:PASS

      procedure Dyn_Param (X : in out Dynamic_Discrete) with
        Post => X > 0;
   end Nested;

   package body Nested is
      procedure Dyn_Param (X : in out Dynamic_Discrete) is
      begin
         if X < C then
            X := X + 1;
         end if;
      end Dyn_Param;
   end Nested;

   function Dyn_Return (X : Positive) return Pos_Dynamic_Discrete with
     Pre => True
   is
   begin
      if X > C then
         return C;
      else
         return X;
      end if;
   end Dyn_Return;

   procedure Dyn_Param (X : in out Pos_Dynamic_Discrete) with
     Pre => True
   is
   begin
      if X < C then
         X := X + 1;
      end if;
   end Dyn_Param;
begin
   X := Dyn_Return (30);
   pragma Assert (X <= C); --@ASSERT:PASS
   pragma Assert (Dyn_Return (40) <= C); -- assert might fail due to avoidance of cycles between VC modules
   Dyn_Param (X);
   pragma Assert (X <= C); --@ASSERT:PASS
   if Nested.Y > 0 then
      Dyn_Param (Nested.Y); --@RANGE_CHECK:PASS
      pragma Assert (Nested.Y <= C); --@ASSERT:PASS
   end if;
   Nested.Dyn_Param (X); --@RANGE_CHECK:PASS
   pragma Assert (X <= C); --@ASSERT:PASS
end Test_Dynamic_Property;
