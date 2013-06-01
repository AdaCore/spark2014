package body Test is

   function Ident_Str (X : String) return String is
   begin
       return "";
   end Ident_Str;

   procedure Do_It is
   begin
    if Ident_Str ("") /= "" then
       null;
    end if;

   end Do_It;
end Test;
