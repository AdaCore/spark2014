package Dispatch with SPARK_Mode is

   pragma Elaborate_Body;

   type T1 is tagged null record;
   procedure P (X : in out T1; B : out Boolean) with Post'Class => B;
   function FF (X : T1) return Boolean with Post'Class => FF'Result;
   function F (X : in out T1) return Boolean
     with Side_Effects,
          Post'Class => F'Result;

   type T2 is new T1 with null record;
   procedure P (X : in out T2; B : out Boolean);
   function FF (X : T2) return Boolean;
   function F (X : in out T2) return Boolean;

end Dispatch;
