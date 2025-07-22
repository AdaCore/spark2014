procedure Main2 is
   V : Integer := 0;
   function Read_V return Integer is (V);

   function Call (F : not null access function return Integer) return
Integer with
     Annotate => (GNATprove, Higher_Order_Specialization),
     Post => Call'Result = F.all;

   function Call (F : not null access function return Integer) return
Integer is
     (F.all);

   function Call_Read_V return Integer is
     (Call (Read_V'Access));

   function Check return Integer is (Call_Read_V) with Global => V;
begin
   null;
end;
