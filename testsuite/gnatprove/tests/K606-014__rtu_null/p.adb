procedure P is
   pragma SPARK_Mode (Off);  --  attribute Width
   function Ident_Int (X : Integer) return Integer is
   begin
      return X;
   end Ident_Int;

   type Parent is (
      E1,
      E2,
      E3,
      E4,
      E5,
      E6);

   subtype Subparent is Parent range
      Parent'Val (Ident_Int (Parent'Pos (E2))) ..
      Parent'Val (Ident_Int (Parent'Pos (E5)));

   I : Integer := Subparent'Width;
begin
   null;
end P;
