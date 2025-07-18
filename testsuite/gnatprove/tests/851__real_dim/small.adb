function Small (C : Boolean; T : Float) return Float is
begin
   if C then
      return 0.0 / 2.0**1;
   else
      return T * 1.0;  --  dummy operation, to force VC generation
   end if;
end;
