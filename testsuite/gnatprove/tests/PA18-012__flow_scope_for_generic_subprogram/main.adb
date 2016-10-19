with Memregions;

procedure Main
with
   SPARK_Mode
is
   procedure Memory_Has_Index is new Memregions.Memory_Has_Index
     (Process => Memregions.Default_Process);
begin
   null;
end Main;
