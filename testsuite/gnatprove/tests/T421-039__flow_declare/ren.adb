procedure Ren with SPARK_Mode is
   type T is array (Positive range <>) of Boolean;
   Z : T (1 .. 10) := (others => False);

   V : Integer := 5; --  variable input

   R1 : T renames Z (1 .. V);  --  slice with variable input
   Y1 : Boolean := R1 (1);

   Y2 : Boolean :=
     (declare
        R2 : T renames Z (1 .. 10);  --  slice with variable input
      begin
        R2 (1));
begin
   pragma Assert (Y1 = Y2);
end;
