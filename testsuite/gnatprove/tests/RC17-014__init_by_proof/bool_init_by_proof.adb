procedure Bool_Init_By_Proof with SPARK_Mode is
   type Color is (Red, Blue, Yellow);

   type Bool_Array is array (Color) of Boolean with
     Relaxed_Initialization;
   type Color_Array is array (Boolean) of Color with
     Relaxed_Initialization;

   procedure Init_One (X : in out Bool_Array; Y : Color)
     with Post =>
       (for all I in Color =>
          (if I /= Y then X (I)'Initialized = X'Old (I)'Initialized))
     and then X (Y)'Initialized
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
   pragma Assert (C'Initialized);
   X := (others => True);
   Init_One (Y, Red);
   Init_One (Y, Blue);
   Init_One (Y, Yellow);
   X := X and Y;
end Bool_Init_By_Proof;
