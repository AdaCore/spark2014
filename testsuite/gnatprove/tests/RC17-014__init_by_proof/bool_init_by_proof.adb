procedure Bool_Init_By_Proof with SPARK_Mode is
   subtype My_Bool is Boolean;
   pragma Annotate (GNATprove, Init_By_Proof, My_Bool);
   type Color is (Red, Blue, Yellow);
   pragma Annotate (GNATprove, Init_By_Proof, Color);

   type Bool_Array is array (Color) of My_Bool;
   type Color_Array is array (My_Bool) of Color;

   procedure Init_One (X : in out Bool_Array; Y : Color)
     with Post =>
       (for all I in Color =>
          (if I /= Y then X (I)'Valid_Scalars = X'Old (I)'Valid_Scalars))
     and then X (Y)'Valid_Scalars
   is
   begin
      X (Y) := True;
   end Init_One;

   X : Bool_Array;
   Y : Bool_Array;
   C : Color_Array;
begin
   C (True) := Yellow;
   C (False) := Red;
   pragma Assert (C'Valid_Scalars);
   X := (others => True);
   Init_One (Y, Red);
   Init_One (Y, Blue);
   Init_One (Y, Yellow);
   X := X and Y;
end Bool_Init_By_Proof;
