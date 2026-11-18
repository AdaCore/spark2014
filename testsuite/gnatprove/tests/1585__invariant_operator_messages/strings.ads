package Strings with SPARK_Mode is
   type T is private;

   function "&" (Left, Right : T) return T;

private
   type T is record
      Length : Integer := 0;
   end record with Type_Invariant => Length >= 0;
end Strings;
