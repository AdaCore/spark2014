pragma Warnings (Off, "subprogram * has no effect");

procedure NoReturn
   with SPARK_Mode
is
   function Success return Boolean
   is
   begin
      return False;
   end Success;

   procedure Stop with No_Return
   is
   begin
      loop
         null;
      end loop;
   end Stop;
begin
   if Success then
      null;
   else
      Stop;
   end if;
end NoReturn;
