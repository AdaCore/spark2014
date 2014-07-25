package Discriminants with SPARK_Mode is
   type Integer_Ptr is access all Integer;

   type OK_1 (D : Integer) is null record;
   type Error_1 (D : access Integer) is null record;
   type Error_2 (D : Integer_Ptr) is null record;

   type Parent_1 (D  : Integer) is tagged null record;
   type Error_4  (D2 : Integer) is new Parent_1 (1) with null record;

   type Parent_2 (D  : Integer := 2) is tagged limited null record;
   type Error_5  (D2 : Integer) is limited new Parent_2 (2) with null record;

   type Parent_3 (D  : Integer) is null record;
end Discriminants;
