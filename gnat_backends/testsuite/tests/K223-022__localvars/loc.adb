package body Loc is
   function Local (Z : Integer) return Integer
   is
      X : Integer := 1 / Z;
      Y : Integer := 1 / X;
      K : Integer;
   begin
      K := 1;
      return K;
   end Local;

end Loc;
