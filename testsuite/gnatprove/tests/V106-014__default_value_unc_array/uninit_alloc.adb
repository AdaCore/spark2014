procedure Uninit_Alloc (C : Positive) with
   SPARK_Mode
is
   type A is array (Positive range <>) of Integer with
      Default_Component_Value => 0;
   type AP is access A;
   pragma Assert (new A (1 .. C) /= null);

   type R (D : Integer) is record
      C : Integer := 0;
   end record;
   type RP is access R;
   pragma Assert (new R (C) /= null);

begin
   null;
end;
