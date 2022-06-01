procedure P with SPARK_Mode => On is
   type Buffer_Acc is access all String;

   type Buffer (First, Last : Integer) is record
      Data : Buffer_Acc (First .. Last);
   end record;

   function To_Access return Buffer with Import;

   Buf : Buffer := To_Access;
begin
   for C of Buf.Data.all loop
      null;
   end loop;
end;
