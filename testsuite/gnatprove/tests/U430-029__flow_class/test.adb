procedure Test with SPARK_Mode, Global => null is
   type Root is tagged record
      F : Integer;
      I : Integer;
   end record;
   type Child is new Root with record
      G : Integer;
      J : Integer;
   end record;

   X : Root'Class := Root'Class (Child'(1, 2, 3, 4));
begin
   if X in Child'Class then
      Child'Class (X).G := 0;
   end if;
end Test;
