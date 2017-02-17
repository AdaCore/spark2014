package body Const is

   procedure Test is
   begin
      --  logic constants. assertions should be proved.

      pragma Assert (A = 1);
      pragma Assert (B = 1);

      pragma Assert (C(1) = 1);
      pragma Assert (C(2) = 1);
      pragma Assert (C2(1) = 1);
      pragma Assert (C2(2) = 1);
      --  pragma Assert (C3(1) = 1);
      --  pragma Assert (C3(2) = 1);
      pragma Assert (D(1) = 1);
      pragma Assert (D(2) = 1);
      pragma Assert (D2(1) = 1);
      pragma Assert (D2(2) = 1);
      --  pragma Assert (D3(1) = 1);
      --  pragma Assert (D3(2) = 1);

      pragma Assert (E.X = 1);
      pragma Assert (E.Y = 1);
      pragma Assert (F.X = 1);
      pragma Assert (F.Y = 1);
      pragma Assert (G.X = 1);
      pragma Assert (G.Y = 1);
      --  pragma Assert (H.X = 1);
      --  pragma Assert (H.Y = 1);

      pragma Assert (I = 1);
      pragma Assert (J = 1);
      pragma Assert (K = 1);
      pragma Assert (L = 1);
      pragma Assert (M = 1);
      pragma Assert (N = 1);

      --  not logic constants. assertions should not be provable.

      pragma Assert (O = 1); -- @ASSERT:FAIL
      pragma Assert (P = 1); -- This one is a logic constant...
   end Test;

end Const;
