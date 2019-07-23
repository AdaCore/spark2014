with Update_Lists;
with Linked_List_Types_Types; use Linked_List_Types_Types;
procedure Driver is

   function Make
     (V : String) return List is
     (if V = "" then null
      else
        new List_Node'
          (Key => V (V'First), Next => Make (V (V'First + 1 .. V'Last))));

   function Convert
     (L : List) return String is
     (if L = null then "" else L.Key & Convert (L.Next));

   procedure Check (Pre1, Pre2, Post1, Post2 : String; Key : Character) is
      -- A tighter check would be possible. Instead of viewing list nodes
      -- with equal key values as being essentially interchangeable, we
      -- We could add a Unique_Id field to the List_Node record and then
      -- check that too.
      L1 : List := Make (Pre1);
      L2 : List := Make (Pre2);
   begin
      Update_Lists (L1, L2, Key);
      pragma Assert (Convert (L1) = Post1);
      pragma Assert (Convert (L2) = Post2);
   end Check;

begin
   Check ("123", "", "13", "2", '2');

   Check ("123123123", "123", "232323", "111123", '1');
   Check ("123123123", "123", "131313", "222123", '2');
   Check ("123123123", "123", "121212", "333123", '3');

   Check ("445566445566445566", "445566", "556655665566", "444444445566", '4');
   Check ("445566445566445566", "445566", "446644664466", "555555445566", '5');
   Check ("445566445566445566", "445566", "445544554455", "666666445566", '6');

   Check ("123", "456", "123", "456", '7');
   Check ("111111", "111", "", "111111111", '1');
end Driver;
