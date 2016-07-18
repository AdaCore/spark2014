with Aida.Containers;
with Aida.Text_IO;
with Vk;
with Extension;
with Aida.Strings;

-- This application should print "Hello" onto standard out but prints "Bye".
-- It is not what is intended.
procedure Main with SPARK_Mode is
   Tag_V : Vk.Tag.T;

   use all type Aida.Containers.Count_Type;
   use all type Vk.Tag.T;
   use all type Vk.Tag.Fs.Name.T;

   N : Vk.Tag.Fs.Name.T;
begin
   Vk.Tag.Set_Name (This  => Tag_V,
                    Value => "Hello");

   N := Name (Tag_V);

   -- By changing the value of N one changes the value of "Tag_V.Name",
   -- and that is bad. "Tag_V.Name" should be read-only.
   -- Thus, the following command should not be ok by either the compiler or the SPARK tools:
   Extension.Mutable_Tag_Name.Initialize (This => Extension.Mutable_Tag_Name.Mutable_T (N),
                                          Text => "Bye");

   if Length (Name (Tag_V)) < Aida.Strings.MAX_LENGTH then
      Aida.Text_IO.Put_Line (To_String (Name (Tag_V)));
   end if;
end Main;
