procedure P is
   Last : constant := 3;
   subtype Index is Integer range 1 .. Last;
   type T1 is array (Index) of Integer;
   type T2 is array (Index, Index) of T1;
   type T3 is array (Index) of T2;

   X : T3 := (others => (others => (others => (others => 0))));
begin
   L1 : for I3 in Index loop
      pragma Loop_Invariant
        (X (I3 + 1 .. Last) = X'Loop_Entry (I3 + 1 .. Last));
      L2 : for I21 in Index loop
         pragma Loop_Invariant
           (X (I3 + 1 .. Last) = X'Loop_Entry (I3 + 1 .. Last));
         L3 : for I22 in Index loop
            pragma Loop_Invariant
              (X (I3 + 1 .. Last) = X'Loop_Entry (I3 + 1 .. Last));
            L4 : for I1 in Index loop
               X (I3) (I21, I22) (I1) := 1;
               pragma Loop_Invariant
                 (X (I3 + 1 .. Last) = X'Loop_Entry (I3 + 1 .. Last)
--                      and then
--                    X (I3) (I21, I22) (I1 + 1  .. Last) =
--                      X'Loop_Entry (I3) (I21, I22) (I1 + 1 .. Last)
--                      and then
--                    X (I3)'Loop_Entry (I21, I22) (I1 + 1  .. Last) =
--                      X (I3) (I21, I22)'Loop_Entry (I1 + 1 .. Last)
--                      and then
--                    X (I3)'Loop_Entry (L4) (I21, I22) (I1 + 1  .. Last) =
--                      X (I3) (I21, I22)'Loop_Entry (L4) (I1 + 1 .. Last)
                 );
            end loop L4;
         end loop L3;
      end loop L2;
   end loop L1;
end P;
