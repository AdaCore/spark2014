with Root.Child; use Root.Child;
with Root.Child.Grand_Child; use Root.Child.Grand_Child;
package body Root with SPARK_Mode is
   X : Child_T;
   Y : Grand_Child_T;
   Z : Root_T;

   procedure P is
   begin
      X := OK;
      Y := OK;
   end P;

   procedure Q is
   begin
      Z := OK;
   end Q;
end Root;
