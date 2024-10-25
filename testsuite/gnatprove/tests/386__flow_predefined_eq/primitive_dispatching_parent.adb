with Ada.text_IO;
procedure Primitive_Dispatching_Parent with SPARK_Mode is

   package Nested is

      type Parent is tagged record F : Integer; end record;

      type Root is new Parent with null record;

      function F (X, Y : Root'Class) return Boolean;

      type Child is new Root with null record;

      function "=" (X, Y : Parent) return Boolean is
         (F (Root'(F => X.F), Root'(F => Y.F)));

      function F (X, Y : Root'Class) return Boolean is
         (X = Y);

   end Nested;
   use Nested;

   C1, C2 : Child := (F => 3);
begin
   if C1 = C2 then
      Ada.Text_IO.Put_Line ("ok");
   end if;
end Primitive_Dispatching_Parent;
