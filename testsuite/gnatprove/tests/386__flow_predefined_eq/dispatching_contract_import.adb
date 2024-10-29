with Ada.Text_IO;
procedure Dispatching_Contract_Import with SPARK_Mode is

   package Nested is

      type Root is tagged record
         F : Integer;
      end record;

      function F (X, Y : Root) return Boolean;

      type Child is new Root with null record;

      function "=" (X, Y : Child) return Boolean
      with Post => "="'Result = F (X, Y),
           Import;

      type Grandchild is new Child with null record;

      function N return Grandchild'Class with Import;

   end Nested;

  package body Nested is
      function F (X, Y : Root) return Boolean is
         XX, YY : Grandchild'Class := N;
      begin
         return XX = YY;
      end F;
   end Nested;
   use Nested;

   G1, G2 : Grandchild := (F => 3);
begin
   if G1 = G2 then
      Ada.Text_IO.Put_Line ("ok");
   end if;
end Dispatching_Contract_Import;
