with Parent_14.Private_Child_B_14;

package body Parent_14.Public_Child_B_14
  with SPARK_Mode
is
   function H (X : Integer) return Integer is
     (Parent_14.Private_Child_B_14.H (X));
end Parent_14.Public_Child_B_14;
