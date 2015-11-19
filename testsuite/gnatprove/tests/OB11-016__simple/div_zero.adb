procedure Div_Zero
  with SPARK_Mode
is
   C : Integer := 0;
begin
   C := C / C;
end Div_Zero;
