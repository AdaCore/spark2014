with Aida;
with Ada.Text_IO;

procedure Main is
   use Aida.Int32;
   use Aida.String;

   S : Aida.String.T := "6";
   I : Aida.Int32.T;
   Has_Failed : Boolean;
begin
   To_Int32 (S, I, Has_Failed);
   if Has_Failed then
      Ada.Text_IO.Put ("Failed to do the conversion of ");
      Ada.Text_IO.Put_Line (String(S));
   else
      Ada.Text_IO.Put_Line ("Value:" & I'Img);
   end if;
end Main;
