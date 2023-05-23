procedure Main_Call
  with
    SPARK_Mode => On
is

   function Call (F : not null access function return Integer) return Integer with
     Annotate => (GNATprove, Higher_Order_Specialization),
     Annotate => (GNATprove, Always_Return),
     Depends => (Call'Result => F),
     Post => Call'Result = F.all;

   function Call (F : not null access function return Integer) return Integer is
   begin
      return F.all;
   end Call;

   function Call_Call (F : not null access function return Integer) return Integer with
     Annotate => (GNATprove, Higher_Order_Specialization),
     Depends => (Call_Call'Result => F),
     Post => Call_Call'Result = Call (F);

   function Call_Call (F : not null access function return Integer) return Integer is
   begin
      return F.all;
   end Call_Call;

   V : Integer := 0;

   function Read_V return Integer is (V);
   function Cst_1 return Integer is (1);

   I : Integer;
begin
   I := Call_Call (Cst_1'Access);
   pragma Assert (I = 1);
   I := Call_Call (Read_V'Access);
   pragma Assert (I = 0);
end Main_Call;
