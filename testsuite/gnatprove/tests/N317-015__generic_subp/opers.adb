package body Opers with
  SPARK_Mode
is

   function Apply_To_Self (X : T) return T is
   begin
      return X + X;
   end Apply_To_Self;

   function Double1 is new Apply_To_Self (Integer);

   procedure Test (A : in out Integer) is
   begin
      A := Double1 (A);
   end Test;

end Opers;
