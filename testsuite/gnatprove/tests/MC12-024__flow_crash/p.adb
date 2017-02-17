package body P
  with SPARK_Mode => On
is
   procedure Sync_Raw_S_With_Full_S
     with Global => (Output => Raw_S,
                     Input  => Full_S),
          Depends => (Raw_S => Full_S);


   procedure Sync_Raw_S_With_Full_S
     with SPARK_Mode => Off
   is
   begin
      --  Full_S and Raw_S are actually aliased in memory
      --  so no action required here.
      null;
   end Sync_Raw_S_With_Full_S;


   procedure Initialize
   is
   begin
      Full_S := Null_R;
      Sync_Raw_S_With_Full_S;
   end Initialize;

   procedure Update_R (X : in Integer;
                       Y : in Float)
   is
   begin
      Full_S.A := Full_S.A + X;
      Full_S.B := Full_S.B + Y;
      Sync_Raw_S_With_Full_S;
   end Update_R;

end P;

