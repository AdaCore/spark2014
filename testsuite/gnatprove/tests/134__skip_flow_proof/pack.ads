package Pack is

   function F return Boolean with Import;

   X : Boolean;

   procedure Skip_Entirely
      with Annotate => (Gnatprove, Skip_Flow_And_Proof),
           Global => null;

   procedure Skip_Proof
      with Annotate => (Gnatprove, Skip_Proof),
           Global => null;

   procedure Process_Normally;

end Pack;
