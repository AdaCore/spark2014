with Entities;

procedure Main
with
   SPARK_Mode
is
begin
   Entities.Init;

   pragma Assert (Entities.Get_Current_ID = Entities.ID_Index'First);
   pragma Assert (Entities.Get_Current_Cycles = Positive'Last);

   Entities.Set_Current_ID (Value => 9);
   pragma Assert (Entities.Get_Current_ID = 9);
   pragma Assert (Entities.Get_Current_Cycles = Positive'Last);
end Main;
