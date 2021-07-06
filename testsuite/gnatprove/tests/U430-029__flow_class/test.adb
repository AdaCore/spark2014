procedure Test with SPARK_Mode, Global => null is
   type Root is tagged record
      A : Integer;
   end record;
   type Child is new Root with record
      B : Integer;
   end record;

   X : Root'Class := Root'Class (Child'(1, 2));
begin
   if X in Child'Class then
      Child'Class (X).B := 0;
   end if;
end Test;
