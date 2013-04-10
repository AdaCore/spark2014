package body Other
is

   X : Integer;
   Y : Integer;

   procedure Initialise
   is
   begin
      X := 0;
      Y := 0;
   end Initialise;

   function Get_X return Integer
   is
   begin
      return X;
   end Get_X;

   function Get_Y return Integer
   is
   begin
      return Y;
   end Get_Y;

end Other;
