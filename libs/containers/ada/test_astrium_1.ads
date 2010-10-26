with Ada.Containers.Doubly_Linked_Lists;

generic
   type Element_Type is private;

   with function Detects_Failure (E : Element_Type) return Boolean;

package Test_Astrium_1 is
   package DLL is new Ada.Containers.Doubly_Linked_Lists
     (Element_Type => Element_Type);

   use DLL;

   type Recovery_T  is (None, Reboot);

   function Test_Recovery (L : List) return Recovery_T
   with Post => (if (for all Cu in L => Detects_Failure (Element(Cu)) = False) then
                 Test_Recovery'Result = None);

end Test_Astrium_1;
