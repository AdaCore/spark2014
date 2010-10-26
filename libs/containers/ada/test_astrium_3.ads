with Ada.Containers.Doubly_Linked_Lists;
with Sum_Of_Weight;

package Test_Astrium_3 is

   package DLL is new Ada.Containers.Doubly_Linked_Lists
  (Element_Type => Boolean);

   use DLL;

   function Is_Active (E : Boolean) return Boolean;

   function Activate (E : Boolean) return Boolean
   with Post => Is_Active(Activate'Result);

   function Weight (E : Boolean) return Integer;

   function Num_Of_Active is new Sum_Of_Weight(DLL, Weight);

   procedure Activate_First_Non_Active (L : in out List)
   with Post => Num_Of_Active (L'Old) <= Num_Of_Active(L);

end Test_Astrium_3;
