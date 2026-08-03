--  Original reproducer from the ticket: the predicate check on the generic
--  actual of a locally instantiated generic function was proved, but failed at
--  run time.

package Orig
  with SPARK_Mode
is

   type T is record
      X : Integer;
   end record
   with Predicate => X = 1;

   generic
      Default_T : T;
   function Generic_Make_T return T;

   function Make_T return T;

end Orig;
