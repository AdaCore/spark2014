procedure Unrelated with SPARK_Mode is

   -- There is no LSP checking between procedures not visibly related in SPARK

   package P is
      type T is tagged private;
      procedure P (X : T) with Pre'Class => True, Post'Class => True; --@STRONGER_CLASSWIDE_POST:NONE
      type U is tagged private;
      procedure P (X : U) with Pre'Class => False, Post'Class => False; --@WEAKER_CLASSWIDE_PRE:NONE
      type V is new T with private;
      procedure P (X : V) with Pre'Class => False, Post'Class => True; --@WEAKER_CLASSWIDE_PRE:FAIL
   private
      pragma SPARK_Mode (Off);
      type T is tagged null record;
      type U is new T with null record;
      type V is new U with null record;
   end P;
   package body P with SPARK_Mode => Off is
      procedure P (X : T) is null;
      procedure P (X : U) is null;
      procedure P (X : V) is null;
   end P;
begin
   null;
end Unrelated;
