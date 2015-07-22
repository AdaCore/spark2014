--  This test explores where we will find "Actions" in the AST. See
--  sinfo.ads for some more information.

package body Foo
is
   pragma Warnings (Off, "analyzing unreferenced procedure *");

   New_Str : String (1 .. 5) := "12345";
   New_Sub : String (1 .. 5) := New_Str;

   procedure Test_01 (B : out Boolean)
   is
      Pos : Integer := 1;
   begin
      --  action in n_iteration_scheme
      while New_Str (Pos .. 5) /= New_Sub loop
         Pos := Pos + 1;
      end loop;
      B := Pos = 10;
   end Test_01;

   procedure Test_02 (B : out Boolean)
   is
      Pos : Integer := 1;
   begin
      --  no action, instead we get a declaration in front of the statement
      B := New_Str (Pos .. 5) /= New_Sub;
   end Test_02;

   procedure Test_03 (B : out Boolean)
   is
      Pos : Integer := 5;
   begin
      --  not an action, instead we get a declaration in front of the loop
      for I in Integer range 1 .. Pos loop
         Pos := Pos + 1;
      end loop;
      B := Pos = 10;
   end Test_03;

   procedure Test_04 (B : out Boolean)
   is
      Pos : Integer := 1;
   begin
      B := True;

      --  not an action for the if part, but there is an action in the
      --  n_and_then expression
      if B and then New_Str (Pos .. 5) /= New_Sub then
         Pos := Pos + 1;
      elsif New_Str (Pos .. 5) /= New_Sub then
         --  Action in the n_elsif_part
         Pos := Pos - 1;
      else
         Pos := Pos;
      end if;

      B := Pos > 10;
   end Test_04;

   procedure Test_05 (B : out Boolean)
   is
      X, Y, Z : Integer := 1;
   begin
      -- no action for the if (preceeding declaration)
      -- in n_if_expression, we have then_actions and else_actions
      B := (if New_Str (X .. 5) /= New_Sub
            then New_Str (Y .. 5) /= New_Sub
            else New_Str (Z .. 5) /= New_Sub);
   end Test_05;

   procedure Test_06 (N : Natural;
                      B : out Boolean)
   is
      Pos  : Integer := N;
      X, Y : Integer := 1;
   begin
      --  no action for pos (prepended by compiler)
      --  actions for each alternative
      B := (case New_Str (N .. Pos) (1) is
            when 'a'    => New_Str (X .. 5) /= New_Sub,
            when others => New_Str (Y .. 5) /= New_Sub);
   end Test_06;

   procedure Test_07 (N : Natural;
                      B : out Boolean)
   is
      Pos  : Integer := N;

      procedure Set (X : Boolean)
      with Global => (Output => B)
      is
      begin
         B := X;
      end Set;
   begin
      --  no action, prepended by the compiler
      Set ((if New_Str (Pos .. 5) /= New_Sub
            then True else False));
   end Test_07;

end Foo;
