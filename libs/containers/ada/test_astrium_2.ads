with Ada.Containers.Ordered_Sets;

generic
   type Element_Type is private;

   with function "<" (Left, Right : Element_Type) return Boolean is <>;
   with function "=" (Left, Right : Element_Type) return Boolean is <>;

package Test_Astrium_2 is
   package OS is new Ada.Containers.Ordered_Sets
     (Element_Type => Element_Type,
      "<" => "<", "=" => "=");

   use OS;

   function Test_Recovery_Highest (S : Set) return Element_Type
   with Pre => not Is_Empty(S),
   Post => (for all Cu in S =>
            not Test_Recovery_Highest'Result < Element(Cu));

end Test_Astrium_2;
