procedure Test_Bad
  with
    SPARK_Mode => On
is
   --  The body of an expression function might contain unsupported uses of
   --  the specializable parameters. It cannot be used for inlining.

   function Non_Specializable_Call (F : not null access function return Integer) return Integer is
     (F.all);

   function Bad_Call_1 (F : not null access function return Integer) return Integer;
   pragma Annotate (GNATprove, Higher_Order_Specialization, Bad_Call_1);
   pragma Annotate (GNATprove, Inline_For_Proof, Bad_Call_1);

   function Bad_Call_1 (F : not null access function return Integer) return Integer is
     (Non_Specializable_Call (F));

   function Bad_Call_2 (F : not null access function return Integer) return Integer;
   pragma Annotate (GNATprove, Inline_For_Proof, Bad_Call_2);
   pragma Annotate (GNATprove, Higher_Order_Specialization, Bad_Call_2);

   function Bad_Call_2 (F : not null access function return Integer) return Integer is
     (Non_Specializable_Call (F));

   V : Integer := 0;
   function Read_V return Integer is (V);
   I : Integer;
begin
   I := Bad_Call_1 (Read_V'Access);
   pragma Assert (I = 0);
   I := Bad_Call_2 (Read_V'Access);
   pragma Assert (I = 0);
end Test_Bad;
