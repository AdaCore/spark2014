with Ada.text_IO;
procedure Primitive_Dispatching with SPARK_Mode is

   package Nested is

      type Root is tagged record
         F : Integer;
      end record;

      function F (X, Y : Root'Class) return Boolean;

      type Child is new Root with null record;

      function "=" (X, Y : Child) return Boolean is
         (F (X, Y));

      function F (X, Y : Root'Class) return Boolean is
         (X = Y);

   end Nested;
   use Nested;

   C1, C2 : Child := (F => 3);
begin
   if C1 = C2 then
      Ada.Text_IO.Put_Line ("ok");
   end if;
end Primitive_Dispatching;
