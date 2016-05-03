with Bitsets;

procedure Test_Main is
   pragma Assertion_Policy (Assert => Check);
   package My_Sets is new Bitsets (10);

   S : My_Sets.Set := My_Sets.Empty;
begin
   My_Sets.Add (S, 8);
   My_Sets.Add (S, 3);
   pragma Assert (My_Sets.Mem (S, 3));
   pragma Assert (My_Sets.Mem (S, 8));
   pragma Assert (not My_Sets.Mem (S, 1));
   pragma Assert (not My_Sets.Mem (S, 2));
   pragma Assert (not My_Sets.Mem (S, 4));
   pragma Assert (not My_Sets.Mem (S, 5));
   pragma Assert (not My_Sets.Mem (S, 6));
   pragma Assert (not My_Sets.Mem (S, 7));
   pragma Assert (not My_Sets.Mem (S, 9));
   pragma Assert (not My_Sets.Mem (S, 10));
   --  failed assertion to get some output
   pragma Assert (not My_Sets.Mem (S, 3));
end Test_Main;
