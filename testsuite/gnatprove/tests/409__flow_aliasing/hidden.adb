package body Hidden is

   X : Integer := 0;

   function Get_X return Integer is
   begin
      return X;
   end;

   procedure Set_X (Value : Integer) is
   begin
      X := Value;
   end;

end;
