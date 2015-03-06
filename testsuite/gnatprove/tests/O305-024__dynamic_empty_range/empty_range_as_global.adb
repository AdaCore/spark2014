procedure Empty_Range_AS_Global (C : Natural) with SPARK_Mode is
   Max : constant Natural := 100;
   subtype May_Be_Empty is Natural range C .. 100;
   E : May_Be_Empty;

   procedure Init_E with
     Pre => True
   is
   begin
      E := C; --@RANGE_CHECK:FAIL
   end Init_E;
begin
   Init_E;
end;
