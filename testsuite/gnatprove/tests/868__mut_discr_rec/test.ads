package Test is

   type My_Base_Rec
     (D1 : Boolean := False;
      D2 : Boolean := False)
   is record
      F : Integer := 12345;
   end record;

   type My_Rec is new My_Base_Rec;

   subtype T0 is My_Rec;

   subtype T1 is T0;

   subtype T2 is T1 (True, False);

   type Nested_U is record
      R : T1;  --  Unconstrained component
   end record;

   type Nested_C is record
      R : T2;  --  Constrained component
   end record;

   procedure P (I : Positive; X : T1)
   with Pre => True;

end Test;
