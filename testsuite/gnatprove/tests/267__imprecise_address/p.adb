with System;
procedure P (A : System.Address) is
   pragma Warnings (GNATprove, Off,
     "address specification on ""Y"" is imprecisely supported");
   Y : Integer with Address => A;
   pragma Warnings (GNATprove, On,
     "address specification on ""Y"" is imprecisely supported");
begin
   null;
end P;
