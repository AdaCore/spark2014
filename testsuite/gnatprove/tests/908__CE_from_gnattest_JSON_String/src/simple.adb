package body Simple
with SPARK_Mode
is

   procedure Not_Michel (Name : String) is
   begin
      pragma Assert (Name /= "Michèle");
   end;

end Simple;
