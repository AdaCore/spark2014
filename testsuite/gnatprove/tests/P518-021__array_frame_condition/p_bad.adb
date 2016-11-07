procedure P_Bad with SPARK_Mode is
   Last : constant := 3;
   subtype Index is Integer range 1 .. Last;
   type T1 is array (Index) of Integer;
   type T2 is array (Index, Index) of T1;
   type T3 is array (Index) of T2;

   X : T3 := (others => (others => (others => (others => 0))));
   Y : constant T3 := X;
begin
   L1 : for I3 in Index loop
      L2 : for I21 in Index loop
         L3 : for I22 in Index loop
            L4 : for I1 in Index loop
               X (I3) (I21, I22) (I1) := 1;
            end loop L4;
         end loop L3;
      end loop L2;
      pragma Assert
        (X (I3 .. Last) = Y (I3 .. Last)); --@ASSERT:FAIL
   end loop L1;
end P_Bad;
