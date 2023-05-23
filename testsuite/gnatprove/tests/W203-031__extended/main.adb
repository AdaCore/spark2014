procedure Main is
   package P1 is
      type Root is tagged null record;
      function G (X : Root) return Integer is (1);
   end P1;
   use P1;

   package P2 is
      type Child is new Root with record
         F : Integer;
      end record;
      function G (X : Child) return Integer with Post => False;
   end P2;

   package body P2 is
      function G (X : Child) return Integer is
         V : Root'Class := Root'(null record);
         I : Integer := G (V);
      begin
         return I;
      end G;
   end P2;
begin
   null;
end Main;
