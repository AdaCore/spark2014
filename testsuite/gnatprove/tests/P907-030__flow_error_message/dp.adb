package body Dp
with SPARK_Mode,
  Refined_State => (T => The_T)
is

   type T_The_T is record
      X : Integer;
      Y : Integer;
   end record;

   The_T : T_The_T := T_The_T'(X => 0,
                               Y => 0);


   function Get_X return Integer is
     (The_T.X);

   procedure Set_Y (Y : in Integer) is
   begin
      The_T.Y := Y;
   end Set_Y;

end Dp;
