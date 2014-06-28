package body Replacement with
  SPARK_Mode
is
   procedure Refine (D : in out Inverse_Set; K : Integer) is
      D_Old : constant Inverse_Set := D;
   begin
      Replace (D, K, 0);
      pragma Assert (for all C in D_Old => Has_Element (D, C));
      pragma Assert (for all C in D_Old => Key (D_Old, C) = Key (D, C));
   end Refine;
end Replacement;
