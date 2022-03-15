package body Exprold is

   function Same (I : in Natural) return Natural is (I);

   procedure Old_On_Call (I : in out Natural) is
   begin
      I := I + 1;
   end Old_On_Call;

   procedure Old_On_Record_Field (R : in out Int_Record) is
   begin
      R.X := R.X + 1;
   end Old_On_Record_Field;

   procedure Old_On_Array_Elt (A : in out Int_Array) is
   begin
      A(1) := A(1) + 1;
   end Old_On_Array_Elt;

   procedure Old_On_Record_Field_In_Array (A : in out Record_Array) is
   begin
      A(1).X := A(1).X + 1;
   end Old_On_Record_Field_In_Array;

   procedure Old_On_Integer (I : in out Integer) is
   begin
      I := I + 1;
   end Old_On_Integer;

   procedure Old_In_Loop_Spec (R : in out Rec) is begin
      R.A(R.A'First) := R.A(R.A'First) + 1 - 1;   --  Do nothing
   end Old_In_Loop_Spec;

end;
