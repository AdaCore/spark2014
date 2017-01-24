with Ada.Containers.Formal_Doubly_Linked_Lists;

package body Foo with SPARK_Mode
is

   type T is mod 2 ** 8;

   function Eq (Left, Right : T) return Boolean is (Left = Right);

   package Lists is new Ada.Containers.Formal_Doubly_Linked_Lists
     (Element_Type => T);
   use Lists;


   procedure Test_01 (X : out T)
   is
      L : List (5);
   begin
      X := 0;
      Append (L, 1);
   end Test_01;

end Foo;
