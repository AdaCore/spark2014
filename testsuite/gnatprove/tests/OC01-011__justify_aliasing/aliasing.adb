package body Aliasing
with SPARK_Mode => On
is
   procedure Swap (X, Y : in out Positive) is
      Temp : constant Positive := X;
   begin
      X := Y;
      Y := Temp;
   end Swap;

   procedure Swap_Indexes (A : in out P_Array; I, J : Natural) is
   begin
      Swap (A (I), A (J));
      pragma Annotate (GNATprove, False_Positive, "aliased", "I /= J");
   end Swap_Indexes;
end Aliasing;
