package body Bar is

   function F return T2 is
      Tmp_1 : Foo.T1;
      Tmp_2 : T2;
   begin
      return Tmp_2;
   end F;

end Bar;
