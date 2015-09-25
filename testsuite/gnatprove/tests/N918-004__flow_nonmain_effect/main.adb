with Non_Main;
with Very_Non_Main;

procedure Main is
begin
   Non_Main;          --  has no effect, should trigger a warning
   Very_Non_Main (0); --  just like this one
end;
