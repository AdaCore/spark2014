pragma SPARK_Mode;
procedure Bad_Constant is
   function Ident (X : Integer) return Integer is (X);
   X : constant Natural := Ident (Integer'Last) + 1;
begin
   null;
end Bad_Constant;
