package Deep is

   type Int_Acc is not null access Positive;

   type R1 is record
      F, G, H : Int_Acc;
   end record;

   type R2 is record
      A, B : R1;
   end record;

   procedure Test1 (X : in out R2) with
     Post => X.A.F.all = 1 and X.B.G.all = 2;

end Deep;
