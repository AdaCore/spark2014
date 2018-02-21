package body P is

   -----------
   -- Empty --
   -----------

   function Empty (This : Stack) return Boolean is
     (This.Top = 0);

   -----------
   -- Reset --
   -----------

   procedure Reset (This : out Stack) is
   begin
      This := (This.Capacity, Top => 0, others => <>);   --  bug
   end Reset;

end P;
