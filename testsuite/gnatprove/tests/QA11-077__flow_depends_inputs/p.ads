package P with SPARK_Mode,
  Initializes => R
is
   type Mut_Rec (D : Boolean) is record
      I : Integer;
   end record;

   R : Mut_Rec (True);

   procedure Proc with Global => (Output => R);

end P;
