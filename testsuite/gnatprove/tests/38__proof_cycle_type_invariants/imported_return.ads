package Imported_Return with SPARK_Mode is
   type T is private;
private

   function F (X : T) return Boolean with Post => False;

   type T is record
      A : Boolean;
   end record
     with Type_Invariant => F (T);

end;
