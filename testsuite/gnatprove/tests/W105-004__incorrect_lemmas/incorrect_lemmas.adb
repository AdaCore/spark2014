procedure Incorrect_Lemmas
  with
    SPARK_Mode => On
is

   --  Function with incorrect axioms with Automatic_Instantiation. The
   --  specialization of these axioms should not be used to prove each others
   --  or themselves.

   function Call (F : not null access function return Integer) return Integer is
     (F.all)
   with
     Post => Call'Result = F.all,
     Annotate => (GNATprove, Higher_Order_Specialization),
     Annotate => (GNATprove, Always_Return);

   procedure Bad_Lemma_1 (F : not null access function return Integer) with
     Ghost,
     Annotate => (GNATprove, Higher_Order_Specialization),
     Annotate => (GNATprove, Automatic_Instantiation),
     Annotate => (GNATprove, Always_Return),
     Post => Call (F) = 1; --@POSTCONDITION:FAIL

   procedure Bad_Lemma_2 (F : not null access function return Integer) with
     Ghost,
     Annotate => (GNATprove, Higher_Order_Specialization),
     Annotate => (GNATprove, Automatic_Instantiation),
     Annotate => (GNATprove, Always_Return),
     Post => Call (F) = 1; --@POSTCONDITION:FAIL

   procedure Bad_Lemma_1 (F : not null access function return Integer) is
      V : Integer := 0;
      function Read_V return Integer is (V);
   begin
      pragma Assert (Call (Read_V'Access) = 0);
   end Bad_Lemma_1;

   procedure Bad_Lemma_2 (F : not null access function return Integer) is
      V : Integer := 0;
      function Read_V return Integer is (V);
   begin
      pragma Assert (Call (Read_V'Access) = 0);
   end Bad_Lemma_2;

begin
   null;
end Incorrect_Lemmas;
