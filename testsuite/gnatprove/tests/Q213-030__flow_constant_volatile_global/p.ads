package P with SPARK_Mode
is

   type Info_Context is record
      String_Address : Integer;
   end record;
   pragma Volatile (Info_Context);

   procedure Clear_Context (Context : out Info_Context);

end;
