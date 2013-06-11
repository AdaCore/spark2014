procedure Illegal_Update (X : in out Integer)
is
   Tmp : Integer := 0;

   procedure Do_Stuff
     with Global => (Input  => X,
                     Output => Tmp)
   is
   begin
      X   := X + 1;
      Tmp := X;
   end Do_Stuff;
begin
   Do_Stuff;
end Illegal_Update;
