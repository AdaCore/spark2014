package body Strings with SPARK_Mode is

   ---------
   -- "&" --
   ---------

   function "&" (Left, Right : T) return T is
   begin
      return (Length => Integer'Max (Left.Length, Right.Length));
   end "&";

end Strings;
