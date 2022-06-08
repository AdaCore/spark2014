procedure Main with SPARK_Mode is
   function Rand (X : Integer) return Boolean with Import;

   type Int_Acc is access Integer;
   type R is record
      X : Integer;
      Y : Int_Acc;
   end record;

   X : R := (X => 12, Y => new Integer'(1));
   Y : R := (X => 12, Y => new Integer'(1));

begin
   if Rand (0) then
      pragma Assert (X'Image = Y'Image); --  Incorrect
   elsif Rand (1) then
      pragma Assert (X'Img = Y'Img); --  Incorrect
   elsif Rand (2) then
      pragma Assert (R'Image (X) = R'Image (Y)); --  Incorrect
   end if;
end Main;
