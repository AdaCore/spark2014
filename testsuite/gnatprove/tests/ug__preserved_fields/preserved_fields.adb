procedure Preserved_Fields with SPARK_Mode is
   type R is record
      F1 : Integer := 0;
      F2 : Integer := 0;
   end record;

   type R_Array is array (1 .. 100) of R;

   type R_Array_Record is record
      F3 : R_Array;
      F4 : R_Array;
   end record;

   D : R_Array_Record;

begin
   for I in 1 .. 100 loop
      D.F3 (I).F1 := 0;
      pragma Assert (for all J in 1 .. 100 =>
                       D.F3 (J).F2 = D.F3'Loop_Entry (J).F2);
      pragma Assert (D.F4 = D.F4'Loop_Entry);
   end loop;

end Preserved_Fields;
