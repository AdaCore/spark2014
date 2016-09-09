with P_Root; use P_Root;
package P_Child with SPARK_Mode is
   type My_Positive is private;

   type Child is tagged private;

   function F (X : Child) return Natural;

   function Test (X : Child) return Natural;
private
   type My_Positive is new Natural with
     Default_Value  => 1,
     Type_Invariant => My_Positive /= 0;

   type Child is new Root with record
      G : My_Positive;
   end record;

   function F (X : Child) return Natural is (100 / Natural (X.G)); --@DIVISION_CHECK:PASS
end P_Child;
