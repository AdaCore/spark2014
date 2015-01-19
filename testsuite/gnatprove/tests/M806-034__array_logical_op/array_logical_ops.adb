package body Array_Logical_Ops is
   pragma SPARK_Mode (On);

   procedure Test_Ok1 is
      X  : constant Bool_Array := (1 .. 10 => True,  11 .. 20 => False,
                                   21 .. 30 => True, 31 .. 40 => False);
      Y  : constant Bool_Array := (1 .. 10 => False, 11 .. 30 => True,
                                   31 .. 40 => False);
      R1 : constant Bool_Array := X and Y;
   begin
      pragma Assert (R1'First = 1);
      pragma Assert (for all I in 1 .. 20 => not R1 (I));
      pragma Assert (for all I in 31 .. 40 => not R1 (I));
      pragma Assert (for all I in 21 .. 30 => R1 (I));
   end Test_Ok1;

   procedure Test_Ok2 is
      V  : constant Bool_Array := (6 .. 15 => False, 16 .. 35 => True,
                                  36 .. 45 => False);
      X  : constant Bool_Array := (1 .. 10 => True,  11 .. 20 => False,
                                   21 .. 30 => True, 31 .. 40 => False);
      R2 : constant Bool_Array := X or V;
   begin
      pragma Assert (R2'First = 1);
      pragma Assert (for all I in R2'First .. 30 => R2 (I));
      pragma Assert (for all I in 31 .. R2'Last => not R2 (I));
   end Test_Ok2;

   procedure Test_Ok3 is
      V  : constant Bool_Array := (6 .. 15 => False, 16 .. 35 => True,
                                  36 .. 45 => False);
      X  : constant Bool_Array := (1 .. 10 => True,  11 .. 20 => False,
                                   21 .. 30 => True, 31 .. 40 => False);
      R3 : constant Bool_Array := V xor X;
   begin
      pragma Assert (R3'First = 6);
      pragma Assert (for all I in R3'First .. 25 => R3 (I));
      pragma Assert (for all I in 26 .. R3'Last => not R3 (I));
   end Test_Ok3;

   procedure Test_Ok4 is
      W  : constant True_Array := (1 .. 20 => True);
      Z  : constant True_Array := (6 .. 25 => True);
      R4 : constant True_Array := Z and W;
   begin
      pragma Assert (R4'First = 6);
      pragma Assert (for all I in R4'Range => R4 (I));
   end Test_Ok4;

   procedure Test_Ok5 is
      Y  : constant Bool_Array := (1 .. 10 => False, 11 .. 30 => True,
                                   31 .. 40 => False);
      R5 : constant Bool_Array := not Y;
   begin
      pragma Assert (R5'First = 1);
      pragma Assert (for all I in 1 .. 10 => R5 (I));
      pragma Assert (for all I in 31 .. 40 => R5 (I));
      pragma Assert (for all I in R5'Range =>
                       (if not (I in 11 .. 30) then R5 (I)));
      pragma Assert (for all I in 11 .. 30 => not R5 (I));
   end Test_Ok5;

   procedure Failing_Length_Check (Z: Bool_Array) is
      Y : constant Bool_Array := (1 .. 10 => False, 11 .. 20 => True);
      R : constant Bool_Array := Y and Z; --@LENGTH_CHECK:FAIL
   begin
      null;
   end Failing_Length_Check;

   procedure Failing_Content_Check is
      W  : constant True_Array := (1 .. 20 => True);
      V  : constant True_Array := (6 .. 25 => True);
      R1 : constant True_Array := V xor W;--@RANGE_CHECK:FAIL
      R2 : constant True_Array := not V;--@RANGE_CHECK:FAIL
   begin
      null;
   end Failing_Content_Check;

end Array_Logical_Ops;
