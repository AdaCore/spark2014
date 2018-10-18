with GP;
with GP.GC;

procedure Main (Dummy : Float) is
   package P is new GP;
   package C is new P.GC;
begin
   C.Test;
end;
