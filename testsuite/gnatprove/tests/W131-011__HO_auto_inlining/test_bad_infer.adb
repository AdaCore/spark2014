procedure Test_Bad_Infer
  with
    SPARK_Mode => On
is
   --  The body of an expression function might contain unsupported uses of
   --  the specializable parameters. It shall not implicitly be used for
   --  inlining.

   function Bad (F : access function return Integer) return Integer
   with
     Annotate => (GNATprove, Always_Return),
     Annotate => (GNATprove, Higher_Order_Specialization);

   function Bad (F : access function return Integer) return Integer is
     (if F = null then 0 else 1);

   V : Integer := 0;
   function Read_V return Integer is (V);
   I : Integer := Bad (Read_V'Access);
   pragma Assert (I = 1); --@ASSERT:FAIL
begin
   null;
end Test_Bad_Infer;
