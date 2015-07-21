package Remote is

   pragma Remote_Call_Interface;
   pragma All_Calls_Remote;

   --  Potentially blocking if executed from another partition
   procedure Remote_Call;

end;
