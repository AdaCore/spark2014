package P with Initializes => X is
   pragma Elaborate_Body;
   type T is record
      C : Integer;
   end record;

   X : T := (C => 0) with Constant_After_Elaboration;

   procedure Swap (A, B : in out T)
   with Post => A.C = B.C'Old and B.C = A.C'Old;

end P;
