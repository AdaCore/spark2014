package body P is
   function Empty_Set return Set_Type is
   begin
      return (C => 0);
   end;

   procedure Include (S : in out Set_Type; N : in Integer) is
      Foo : Set_Type := [1, 2, 3]; --@TERMINATION:FAIL
      --  The above declaration triggers recursive call
   begin
      S.C := S.C + N;
   end;

   function Model (S : Set_Type) return Sequence is
      Seq  : Sequence;
      My_S : Set_Type;
   begin
      Include (My_S, 0);
      return Seq;
   end;

end;
