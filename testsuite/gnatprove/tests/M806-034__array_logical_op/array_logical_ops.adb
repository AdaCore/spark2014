package body Array_Logical_Ops is
   pragma SPARK_Mode (On);

   procedure Test_Ok is
      W  : constant True_Array := (1 .. 20 => True);
      Z  : constant True_Array := (6 .. 25 => True);
      V  : constant Bool_Array := (6 .. 15 => False, 16 .. 35 => True,
                                  36 .. 45 => False);
      X  : constant Bool_Array := (1 .. 10 => True,  11 .. 20 => False,
                                   21 .. 30 => True, 31 .. 40 => False);
      Y  : constant Bool_Array := (1 .. 10 => False, 11 .. 30 => True,
                                   31 .. 40 => False);
      R1 : constant Bool_Array := X and Y;
      R2 : constant Bool_Array := X or V;
      R3 : constant Bool_Array := V xor X;
      R4 : constant True_Array := Z and W;
      R5 : constant Bool_Array := not Y;
   begin
      pragma Assert (R1'First = 1);
      pragma Assert (R2'First = 1);
      pragma Assert (R3'First = 6);
      pragma Assert (R5'First = 1);
      pragma Assert (for all I in R1'Range =>
                       (if not (I in 21 .. 30) then not R1 (I)));
      pragma Assert (for all I in 21 .. 30 => R1 (I));
      pragma Assert (for all I in R2'First .. 30 => R2 (I));
      pragma Assert (for all I in 31 .. R2'Last => not R2 (I));
      pragma Assert (for all I in R3'First .. 25 => R3 (I));
      pragma Assert (for all I in 26 .. R3'Last => not R3 (I));
      pragma Assert (for all I in R5'Range =>
                       (if not (I in 11 .. 30) then R5 (I)));
      pragma Assert (for all I in 11 .. 30 => not R5 (I));
   end Test_Ok;

   procedure Failing_Length_Check (Z: Bool_Array) is
      Y : constant Bool_Array := (1 .. 10 => False, 11 .. 20 => True);
      R : constant Bool_Array := Y and Z;
   begin
      null;
   end Failing_Length_Check;

   procedure Failing_Content_Check is
      W  : constant True_Array := (1 .. 20 => True);
      V  : constant True_Array := (6 .. 25 => True);
      R1 : constant True_Array := V xor W;
      R2 : constant True_Array := not V;
   begin
      null;
   end Failing_Content_Check;

   procedure P is
      Z : constant Bool_Array := (1 .. 10 => False);
   begin
      Test_Ok;
      Failing_Content_Check;
      Failing_Length_Check (Z);
   end P;

end Array_Logical_Ops;
