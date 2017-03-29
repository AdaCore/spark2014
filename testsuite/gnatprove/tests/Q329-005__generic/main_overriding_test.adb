
with Types;
with This_Instance;

procedure Main_Overriding_Test is

   Thing: This_Instance.Object := This_Instance.Create;
begin
   for I in Types.Digit_Range loop
       Thing.Print;
   end loop;
end Main_Overriding_Test;
