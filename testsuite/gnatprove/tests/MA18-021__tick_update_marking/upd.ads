package Upd is

   pragma Elaborate_Body;

   type R1 is record
      X, Y : Integer;
   end record;

   type R2 is record
      U, V : R1;
   end record;

end Upd;
