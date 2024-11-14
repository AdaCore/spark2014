procedure See_Through with SPARK_Mode is
   package A is
      type Root is tagged null record;
      procedure P (X : Root) is null with Pre'Class => True;
   end A;
   package B is
      type GrandChild is new A.Root with private;
      procedure P (X : GrandChild);
      package Inner is
         function Witness return GrandChild;
      end Inner;
   private
      pragma SPARK_Mode (Off);
      type Child is new A.Root with null record;
      procedure P (X : Child) is null with Pre'Class => False;
      type GrandChild is new Child with null record;
   end B;
   package body B with SPARK_Mode => Off is
      procedure P (X : GrandChild) is null;
      package body Inner is
         function Witness return GrandChild is (null record);
      end Inner;
   end B;
   package C is
      type Descendant is new B.GrandChild with null record;
      --  Procedure must not be able to see Child's pre-condition.
      procedure P (X : Descendant) is null with Post'Class => False; --@POSTCONDITION:FAIL
   end C;
   X : A.Root'Class := C.Descendant'(B.Inner.Witness with null record);
begin
   null;
end See_Through;
