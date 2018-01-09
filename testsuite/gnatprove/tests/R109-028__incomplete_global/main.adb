with P;

procedure Main is
begin
   pragma Assert (P.F and not P.F);
   --  This assertion can't be satisfied, no matter what

end;
