package body P is
  procedure Op (A, B : in Positive; Z : out Character)
  is
  begin
     if A > 100 then
	 declare
	    subtype S1 is Integer range 0 .. A;
	 begin
	    if B > S1'Last then
	       Z := 'a';
	    else
	       Z := 'b';
	    end if;
	 end;
     else
	 declare
	    subtype S1 is Integer range 0 .. A;
	 begin
	    if B < S1'Last then
	       Z := 'c';
            else
               Z := 'd';
	    end if;
	 end;
     end if;
  end Op;
end P;
