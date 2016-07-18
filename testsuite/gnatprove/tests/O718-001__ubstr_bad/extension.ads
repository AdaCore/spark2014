with Vk;

with Aida.Strings.Generic_Immutable_Unbounded_String_Shared_Ptr.Mutable;

pragma Elaborate_All (Aida.Strings.Generic_Immutable_Unbounded_String_Shared_Ptr.Mutable);

package Extension with SPARK_Mode is

   package Mutable_Tag_Name is new Vk.Tag.Fs.Name.Mutable;

end Extension;
