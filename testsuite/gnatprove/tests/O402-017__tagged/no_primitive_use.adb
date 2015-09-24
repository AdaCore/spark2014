with No_Primitive; use No_Primitive;
procedure No_Primitive_Use
  with SPARK_Mode
is
   X : Root;
begin
   Init (X, 0);
end No_Primitive_Use;
