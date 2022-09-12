with SPARK.Containers.Formal.Doubly_Linked_Lists;

package Cursors is

   package L is new SPARK.Containers.Formal.Doubly_Linked_Lists (Integer);
   use L;

   type R (B : Boolean) is record
      case B is
         when True =>
            C : Cursor;
         when False =>
            null;
      end case;
   end record;

   X : R(False);

   function Get return R is (X);

end Cursors;
