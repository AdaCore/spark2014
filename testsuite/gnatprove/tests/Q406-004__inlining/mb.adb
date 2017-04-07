package body MB is
   function Item_Count return Integer;

   procedure Install_Message (N : in Integer)
     with Post => Item_Count > 0;

   function Item_Count return Integer is (10);

   procedure Install_Message (N : in Integer) is
   begin
      null;
   end Install_Message;

end MB;
