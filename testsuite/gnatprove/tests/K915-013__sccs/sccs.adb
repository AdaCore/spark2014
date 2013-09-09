procedure Sccs (B : in out Boolean) is

   procedure Set_True is
   begin
      B := True;
   end Set_True;

   procedure F2;
   procedure G2 is begin if B then F2; end if; Set_True; end G2;
   procedure F2 is begin if not B then G2; end if; end F2;

   procedure F5;
   procedure G5 is begin if B then F5; end if; Set_True; end G5;
   procedure H5 is begin if not B then G5; end if; end H5;
   procedure I5 is begin if B then H5; end if; end I5;
   procedure J5 is begin if not B then I5; end if; end J5;
   procedure F5 is begin if not B then J5; end if; end F5;


begin
   pragma Assert (B);
   F2;
   pragma Assert (B); -- unprovable
   F5;
   pragma Assert (B); -- unprovable
end Sccs;
