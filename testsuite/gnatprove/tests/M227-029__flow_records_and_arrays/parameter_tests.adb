package body Parameter_Tests
is

   type Coordinate is record
      X : Float;
      Y : Float;
   end record;

   type Index_T is range 1 .. 10;
   type Array_T is array (Index_T) of Coordinate;

   G : Coordinate;
   H : Array_T;

   procedure Clear_Float (F : out Float)
   is
   begin
      F := 0.0;
   end Clear_Float;

   procedure Clear_Coordinate (C : out Coordinate)
   is
   begin
      Clear_Float (C.X);
      Clear_Float (C.Y);
   end Clear_Coordinate;

   procedure Clear_Position (A : in out Array_T;
                             I : Index_T)
   is
   begin
      Clear_Coordinate (A (I));
   end Clear_Position;

   procedure Set_Global_X (F : Float)
     with Global => (Output => G)
   is
   begin
      G.X := F;
   end Set_Global_X;

   procedure Set_Global_Y (F : Float)
     with Global => (In_Out => G)
   is
   begin
      G.Y := F;
   end Set_Global_Y;

   procedure Copy_Position (I : Index_T)
     with Global => (In_Out => (G, H))
   is
   begin
      Set_Global_X (H (I).X);
      Set_Global_Y (H (I).Y);
   end Copy_Position;

end Parameter_Tests;
