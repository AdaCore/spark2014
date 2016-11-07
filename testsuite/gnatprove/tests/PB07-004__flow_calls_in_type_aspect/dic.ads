with Blocking_True;

package Dic is

   type T is private with Predicate => Blocking_True;

   protected type PT is
      procedure Dummy;
   end;

   PO : PT;

private
   type T is new Integer;

end;
