package body Ext_Aggr is
   Ob : Base;

   procedure Reset (This : out Derived)
   is
   begin
      This := (Ob with B => <>);
   end Reset;
end Ext_Aggr;
