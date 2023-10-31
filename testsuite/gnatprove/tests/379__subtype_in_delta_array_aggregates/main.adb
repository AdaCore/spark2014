procedure Main with SPARK_Mode is
   type A is array (Natural range <>) of Integer;
   subtype T is Natural range 0 .. 42;
   subtype U is Natural range 43 .. 52;
   X : constant A := (T => 0, U => 1);
   Y : constant A := (X with delta T => 2);
   Z : constant A := (X with delta T => 2, U => 3, T => 4);
begin
   pragma Assert (X'First = 0 and X'Last = 52);
   pragma Assert (for all I in 0 .. 42 => X (I) = 0);
   pragma Assert (for all I in 43 .. 52 => X (I) = 1);
   pragma Assert (Y'First = 0 and Y'Last = 52);
   pragma Assert (for all I in 0 .. 42 => Y (I) = 2);
   pragma Assert (for all I in 43 .. 52 => Y (I) = 1);
   pragma Assert (Z'First = 0 and Z'Last = 52);
   pragma Assert (for all I in 0 .. 42 => Z (I) = 4);
   pragma Assert (for all I in 43 .. 52 => Z (I) = 3);
   pragma Assert (for all I in T => Z (I) = 4);
   pragma Assert (for all I in U => Z (I) = 3);
   pragma Assert (False); --@ASSERT:FAIL
end Main;
