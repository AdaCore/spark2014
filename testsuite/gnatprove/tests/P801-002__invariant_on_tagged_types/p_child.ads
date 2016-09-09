with P_Root; use P_Root;
package P_Child with SPARK_Mode is
   type Child is tagged private;

   function F (X : Child) return Natural;

   function Test (X : Child) return Natural;
private
   type Child is new Root with record
      G : Natural := 1;
   end record
     with Type_Invariant => Child.G /= 0;

   function F (X : Child) return Natural is (100 / X.G); --@DIVISION_CHECK:PASS
end P_Child;
