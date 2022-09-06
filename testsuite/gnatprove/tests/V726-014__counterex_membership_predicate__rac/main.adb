with Ada.Text_IO; use Ada.Text_IO;

procedure Main with SPARK_Mode is

   type A is array (0 .. 1) of Integer;
   subtype B is A with Predicate => B(0) > 0 and then B(1) = 42;

   subtype I is Integer with Predicate => I in 5 | 8 .. 10 | 40 + 2;

   type R is record
      A : Integer;
      B : Integer;
   end record;

   subtype S is R with Predicate => S.A /= 0 and then S.B in I;

   function Array_Predicate (X : A) return Boolean is (X in B);

   function Record_Predicate (X : R) return Boolean is (X in S);

   function Int_Predicate (X : Integer) return Boolean is (X in I);

begin

  Put_Line ("-- Array --");
  Put_Line ("");

  Put_Line ("Expect True:"  & Boolean'Image (Array_Predicate ((42, 42))));
  Put_Line ("Expect False:" & Boolean'Image (Array_Predicate ((0, 0))));


  Put_Line ("-- Record --");
  Put_Line ("");

  Put_Line ("Expect True:"  & Boolean'Image (Record_Predicate ((42, 42))));
  Put_Line ("Expect False:" & Boolean'Image (Record_Predicate ((0, 0))));

  Put_Line ("-- Integer --");
  Put_Line ("");

  Put_Line ("Expect True:"  & Boolean'Image (Int_Predicate (8)));
  Put_Line ("Expect False:" & Boolean'Image (Int_Predicate (9)));
end Main;
