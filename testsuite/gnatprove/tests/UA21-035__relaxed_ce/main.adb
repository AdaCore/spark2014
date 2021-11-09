procedure Main with SPARK_Mode is
   package P1 is
      type R (D : Integer := 1) is record
         X : Integer;
         Y : Integer;
      end record;
      V : R := (1, 1, 1);
      pragma Assert (V.D = 0 or V.X = 14); --@ASSERT:FAIL
   end P1;
   package P2 is
      type My_Pos is new Positive with Relaxed_Initialization;
      type H is record
         X : My_Pos;
      end record;
      C : H;
      type R (D : My_Pos := 1) is record
         X : H;
         Y : H;
      end record;
      V : R := (1, C, (X => 1));
      pragma Assert (V.D = 0 or V.X.X = 14); --@ASSERT:FAIL @INIT_BY_PROOF:FAIL
   end P2;
   package P3 is
      type H is record
         X : Integer;
      end record;
      C : H with Relaxed_Initialization;
      type R (D : Integer := 1) is record
         X : H;
         Y : H;
      end record;
      V : R := (1, C, (X => 1)) with Relaxed_Initialization;
      pragma Assert (V.D = 0 or V.X.X = 14); --@ASSERT:FAIL @INIT_BY_PROOF:FAIL
   end P3;
begin
   null;
end;
