package P with SPARK_Mode is
   type T is private;

   type U is private;

   function F (X : U) return Boolean;
private

   function G (X : T) return U;

   type T is record
      B : Integer;
   end record
     with Type_Invariant => F (G (T)); --  No boundary function calls

   type U is new Integer;
end P;
