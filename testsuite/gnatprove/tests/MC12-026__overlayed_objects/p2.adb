package body P2
  with SPARK_Mode => On
is
   --  As package P, but this subprogram has as distinct
   --  specification, and the SPARK_Mode => Off appears
   --  on the body only.
   procedure Sync_Raw_S_With_Full_S
     with Global => (Output => Raw_S,
                     Input  => Full_S),
          Depends => (Raw_S => Full_S);



   procedure Sync_Raw_S_With_Full_S
     with SPARK_Mode => Off
   is
   begin
      --  Full_S and Raw_S are actually aliased in memory
      --  so no action required here.  SPARK_Mode is Off so
      --  I expect the mis-match between contract and body
      --  to be ignored.
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

end P2;

