with Illegal_Hide_Private; use Illegal_Hide_Private;
with Illegal_Hide_Private.Child;
procedure Use_Generics with SPARK_Mode is

   package Inst is new Nested;

   procedure P_Inst is new Proc;
begin
   null;
end Use_Generics;
