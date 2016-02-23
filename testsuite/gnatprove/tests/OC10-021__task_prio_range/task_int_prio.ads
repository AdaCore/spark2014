package Task_Int_Prio is

   X : Integer := -1;

   task type TT is
   private
      pragma Interrupt_Priority (X);
   end;

   T : TT;

end;
