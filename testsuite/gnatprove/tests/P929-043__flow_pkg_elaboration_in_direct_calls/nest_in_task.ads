package Nest_In_Task is
   protected type PT is
      entry E;
      procedure Proc with Always_Terminates;
   private
      Flag : Boolean := True;
   end PT;

   task type TT;
end Nest_In_Task ;
