package body Sub is
   procedure P (X : Dir) is
      Y : Ext_Dir := X;
      Z : Dir := Y;
   begin
      null;
   end P;
end Sub;
