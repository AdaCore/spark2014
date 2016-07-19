with Aida.Containers;
with Aida.Text_IO;
with Vk;
with Extension;
with Aida.Strings;

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

   -- By making the type Aida.Strings.Generic_Immutable_Unbounded_String_Shared_Ptr.T
   -- tagged instead of non-tagged the following command is no longer OK which is good:
   --Extension.Mutable_Tag_Name.Initialize (This => Extension.Mutable_Tag_Name.Mutable_T (N),
   --                                       Text => "Bye");

   if Length (Name (Tag_V)) < Aida.Strings.MAX_LENGTH then
      Aida.Text_IO.Put_Line (To_String (Name (Tag_V)));
   end if;
end Main;
