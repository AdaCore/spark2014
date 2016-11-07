with Ada.Dispatching;

function Blocking_True return Boolean is
begin
   Ada.Dispatching.Yield;
   return True;
end;
