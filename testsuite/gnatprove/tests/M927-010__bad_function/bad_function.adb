pragma SPARK_Mode;
procedure Bad_Function is
   function Ident (X : Integer) return Integer is (X);
   function Bad return Integer is (Ident (Integer'Last) + 1);
begin
   null;
end Bad_Function;
