procedure Empty_Range_In_Loop (C : Natural) with SPARK_Mode is
   Max : constant Natural := 100;
   subtype May_Be_Empty1 is Natural range C .. 100;
   subtype May_Be_Empty2 is Natural range C + 1 .. 100; --@OVERFLOW_CHECK:FAIL
   E : May_Be_Empty1;
begin
   for J in 0 .. Max loop
      E := C; --@RANGE_CHECK:FAIL
   end loop;
   for J in 0 .. Max loop
      declare
         D : May_Be_Empty2 := C + 1; --@RANGE_CHECK:FAIL
      begin
         null;
      end;
   end loop;
end;
