with Aida.Strings.Generic_Immutable_Unbounded_String_Shared_Ptr.Mutable;

pragma Elaborate_All (Aida.Strings.Generic_Immutable_Unbounded_String_Shared_Ptr.Mutable);

package Vk with SPARK_Mode is

   package Tag with SPARK_Mode is

      package Fs is
         package Name is new Aida.Strings.Generic_Immutable_Unbounded_String_Shared_Ptr (100);

      end Fs;

      type T is limited private;

      function Name (This : T) return Fs.Name.T;

      procedure Set_Name (This  : in out T;
                          Value : String);

   private

      package Name_P is new Fs.Name.Mutable;

      type T is limited
         record
            My_Name    : Name_P.Mutable_T;
         end record;

      function Name (This : T) return Fs.Name.T is (Fs.Name.T (This.My_Name));

   end Tag;

end Vk;
