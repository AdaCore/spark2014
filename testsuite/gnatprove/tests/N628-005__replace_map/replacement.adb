package body Replacement with
  SPARK_Mode
is
   procedure Refine (A : Set; D : in out Inverse_Set; K : Integer) is
      D_Old : constant Inverse_Set := D;
   begin
      pragma Assert (for all C in D => (if Key (D, C) /= K then A (Element (D, C)) = Key (D, C)));
      Replace_Element (D, Find (D, K), 0);
      -- assertion should still be provable
      pragma Assert (for all C in D => (if Key (D, C) /= K then A (Element (D, C)) = Key (D, C)));
   end Refine;
end Replacement;
