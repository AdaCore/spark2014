package body Update_Illegal_3
  with SPARK_Mode
is
   procedure P1 (Discr_Rec : in out Discr_Record_T) is
   begin
      Discr_Rec := Discr_Rec'Update (C => 0, D => 1);
      --  Each selector_name of each record_component_name
      --  shall denote a distinct non discriminant record
      --  component.

      --  This should raise a "constraint error" since
      --  we cannot have fields C and D at the same time.
   end P1;
end Update_Illegal_3;
