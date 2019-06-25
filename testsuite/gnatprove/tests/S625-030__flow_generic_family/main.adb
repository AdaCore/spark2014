with GP;     --  generic parent
with GP.GC;  --  generic child

procedure Main (Dummy : Float) is
   package P is new GP;      -- instance parent
   procedure C is new P.GC;  -- instance child
begin
   C;
end;
