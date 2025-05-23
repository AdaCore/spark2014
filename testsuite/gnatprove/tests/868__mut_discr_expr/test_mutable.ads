package Test_Mutable is

   --  Record type with mutable discriminants
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

   procedure P (I : Positive)
   with Pre => True;

end Test_Mutable;
