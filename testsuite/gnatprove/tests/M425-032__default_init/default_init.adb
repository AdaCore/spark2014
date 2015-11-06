procedure Default_Init (C : Integer) with
  SPARK_Mode
is
   Default : constant := 100;

   type T1 is new Integer with Default_Value => Default;
   X1 : T1;

   type T2 is record
      A : Integer := Default;
   end record;
   X2 : T2;

   type T3 is array (1 .. 10) of Integer with
     Default_Component_Value => Default;
   X3 : T3;

begin
   pragma Assert (X1 = Default);
   pragma Assert (X2.A = Default);
   pragma Assert (for all J in T3'Range => X3(J) = Default);
end Default_Init;
