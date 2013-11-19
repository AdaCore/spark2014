with Parent_14.Private_Child_A_14,   -- OK
     Parent_14.Public_Child_A_14;    -- OK

package body Parent_14
  with SPARK_Mode
is
   function F (X : Integer) return Integer is (Private_Child_A_14.F (X));

   function G (X : Integer) return Integer is (Public_Child_A_14.G (X));
end Parent_14;
