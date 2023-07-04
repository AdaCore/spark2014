with System;
procedure P (A : System.Address) is
   pragma Warnings (GNATprove, Off,
     "address specification on ""Y"" is imprecisely supported: assuming no concurrent accesses to non-atomic object and no writes to or through a potential alias");
   Y : Integer with Address => A;
   pragma Warnings (GNATprove, On,
     "address specification on ""Y"" is imprecisely supported: assuming no concurrent accesses to non-atomic object and no writes to or through a potential alias");
begin
   null;
end P;
