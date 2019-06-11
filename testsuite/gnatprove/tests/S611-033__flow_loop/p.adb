package body P with SPARK_Mode is

   type Dummy_Enum_Type is (Dummy);

   type Dummy_To_Boolean is array (Dummy_Enum_Type) of Boolean;

   procedure Update (Noise : in out Dummy_To_Boolean) is
   begin
      for Index in Integer'Range loop
         declare
            Local_Avg : Dummy_To_Boolean := (others => False);
         begin
            for Index in Dummy_Enum_Type'Range loop
               Local_Avg (Index) := Noise (Index);
            end loop;
         end;
      end loop;
   end Update;

end P;
