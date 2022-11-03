procedure Main
  with
    SPARK_Mode => On
is
   package Nested is
      type T is private;
      procedure Set_To_Zero_1 (X : T);
      procedure Set_To_Zero_2 (X : T);
   private
      type T is not null access Integer;
   end Nested;
   package body Nested is
      procedure Set_To_Zero_1 (X : T) is
      begin
         X.all := 0;
      end Set_To_Zero_1;
      procedure Set_To_Zero_2 (X : T) is
         B : access Integer := X;
      begin
         B.all := 0;
      end Set_To_Zero_2;
   end Nested;
begin
   null;
end Main;
