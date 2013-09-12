package body Simple_Exceptions
is
   procedure In_SPARK (X : in out Integer) is
   begin
      if X = Integer'Last then
         raise Program_Error;
      end if;

      X := X + 1;
   end In_SPARK;


   function In_SPARK_2 (X, Y : Integer) return Integer is
   begin
      if X < Y then
         return X;
      elsif X >= Y then
         return Y;
      end if;

      raise Program_Error;
   end In_SPARK_2;


   procedure Not_In_SPARK_1 (X : in out Integer) is
      pragma SPARK_Mode (Off);
   begin
      if X = Integer'Last then
        raise Program_Error;
      else
         X := X + 1;
      end if;
   end Not_In_SPARK_1;


   function Not_In_SPARK_2 return Boolean is
      pragma SPARK_Mode (Off);
   begin
      raise Program_Error;

      return True;
   end Not_In_SPARK_2;
end Simple_Exceptions;
