package body P2
is
   procedure E (Y : out Integer) is
      -- Case 5 - initializes depends on local initialized
      -- variable.  Should be legal.
      L : Integer := 1;

      package N
        with Initializes => (S => L) -- legal
      is
         S : Integer := L; -- OK
      end N;

   begin
      Y := N.S;
   end E;

   procedure F (Y : out Integer) is
      -- Case 6 - initializes depends on local uninitialized
      -- variable.  Should be legal, but flow analysis
      -- should report data flow error
      L : Integer;

      package N
        with Initializes => (S => L) -- legal
      is
         S : Integer := L; -- data flow error here
      end N;

   begin
      Y := N.S;
   end F;

end P2;
