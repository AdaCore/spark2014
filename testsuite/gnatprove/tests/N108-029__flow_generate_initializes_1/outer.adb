package body Outer is
   procedure P is
   begin
      null;
   end P;

   package Inner is
      Visible : Integer;

      function Foo return Integer;
   end Inner;

   package body Inner is
      Hidden : Integer;

      function Foo return Integer is (Visible + Hidden);

      procedure Init;

      procedure Init is
         Tmp : Integer;
      begin
         Tmp     := 10;
         Visible := Tmp;
         Hidden  := Tmp;
      end Init;

   begin
      Init;
   end Inner;

end Outer;
