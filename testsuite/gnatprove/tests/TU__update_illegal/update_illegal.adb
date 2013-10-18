package body Update_Illegal
  with SPARK_Mode
is
   type Discr_Record_T (Discr : Boolean := True) is record
      A, B : Integer;
      case Discr is
         when True =>
            C : Integer;
         when others =>
            D : Integer;
      end case;
   end record;

   type Array_T is array (Integer range 1 .. 100) of Boolean;


   procedure P1 (Discr_Rec : in out Discr_Record_T) is
   begin
      Discr_Rec := Discr_Rec'Update (A => 0, B => 1, A => 1);
      Discr_Rec := Discr_Rec'Update (Discr => True);
      --  Each selector_name of each record_component_name
      --  shall denote a distinct non discriminant record
      --  component.
   end P1;


   procedure P2 (Arr : in out Array_T) is
   begin
      Arr := Arr'Update (others => True);
      --  A discrete_choice cannot be others
   end P2;
end Update_Illegal;
