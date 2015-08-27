package body Pck is
   procedure Exchange_No_Post (X, Y : in out Integer) with SPARK_Mode => On
   is
      T : Integer;
   begin
      T := X;
      X := Y;
      Y := T;
   end Exchange_No_Post;
end Pck;
