package P_Int_Acc is

   type T (K : Integer := 555) is record
      null;
   end record;

   type T_Acc is access all T;

   procedure Proc1 (Rec : not null access T; B : Boolean);

   procedure Proc2 (Rec : not null access constant T; B : Boolean);

   procedure Proc3 (Rec : not null T_Acc; B : Boolean);

end P_Int_Acc;
