package body P is
   procedure Proc (S : out My_Rec) is
   begin
      S.A := (others => ' ');
   end Proc;

   X : My_Rec := (Len => 5, A => "12345");

   procedure Proc with Depends => (X => null) is
   begin
      X.A := (others => ' ');
   end;

end P;
