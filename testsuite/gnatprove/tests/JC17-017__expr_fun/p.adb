package body P is
   Y : Boolean;
   function G_True return Boolean is (True);
   function G_X return Boolean is (Y);

   function G_False return Boolean
     with Post => not G_False'Result;

   function G_False return Boolean is (False);

   function G_Y return Boolean
     with Post => G_Y'Result = Y;

   function G_Y return Boolean is (Y);

   procedure Sub is
      Z : Boolean;
      function H_True return Boolean is (True);
      function H_X return Boolean is (Z);

      function H_False return Boolean
	with Post => not H_False'Result;

      function H_False return Boolean is (False);

      function H_Y return Boolean
	with Post => H_Y'Result = Z;

      function H_Y return Boolean is (Z);
   begin
      Z := H_True;
      pragma Assert (Z);
      Z := H_X;
      pragma Assert (Z);
      Z := H_False;
      pragma Assert (not Z);
      Z := H_Y;
      pragma Assert (not Z);
   end;
end;
