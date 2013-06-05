package body Parent_05.Public_Child_A_05
is
  procedure Proc(I : in out Integer)
  --#derives I from I;
  is
  begin
   I := I + Parent_05.F;  -- OK
  end Proc;
end Parent_05.Public_Child_A_05;
