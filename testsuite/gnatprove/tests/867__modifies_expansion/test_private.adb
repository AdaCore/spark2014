pragma Ada_2022;

procedure Test_Private with SPARK_Mode is
   package Nested is
      type T is private;
      procedure P (X : in out T);
   private
      type T is record
         F, G : Integer;
      end record;
   end Nested;
   package body Nested is
      procedure P_Internal (X : in out T) with
        Modifies => X.F;
      procedure P_Internal (X : in out T) is
      begin
         X.F := 0;
      end P_Internal;
      procedure P (X : in out T) is
      begin
         P_Internal (X);
      end P;
   end Nested;

begin
   null;
end;
