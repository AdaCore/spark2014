with Deep_Vectors; use Deep_Vectors;
procedure Main with SPARK_Mode is
   X : Vector := [(V => new Integer'(1)), (V => new Integer'(2))]; --  Memory leak, elements are copied in Add
begin
   Clear (X);
end Main;
