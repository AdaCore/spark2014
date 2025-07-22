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

   function Call_Read_V return Integer with
     Depends => (Call_Read_V'Result => V);

   function Call_Read_V return Integer is
     (Call (F => Read_V'Access));
begin
   null;
end;
