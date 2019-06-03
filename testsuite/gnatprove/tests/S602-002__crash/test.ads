package Test
with SPARK_Mode => On
is

   type FP_Type is private;

   C1 : constant FP_Type;
   C2 : constant FP_Type;
   C3 : constant FP_Type;

   C4 : constant FP_Type;
   C5 : constant FP_Type;

private

   type FP_Type is delta 0.1
   range 0.0 .. 1.0;

   C1 : constant FP_Type := FP_Type'Delta + 0.0; --  Ok
   C2 : constant FP_Type := 0.0 + 0.0;           --  Ok
   C3 : constant FP_Type := FP_Type'First;       --  Ok

   C4 : constant FP_Type := 0.0;                 --  Error
   C5 : constant FP_Type := FP_Type'Delta;       --  Error

end Test;
