package body Initial_Condition_Illegal_2 is
   package body State_Not_Denoted_By_Initializes
     with Refined_State => (State => Flag)
   is
      Flag : Boolean := True;

      function F1 return Boolean is (Flag)
        with Refined_Global => Flag;
   end State_Not_Denoted_By_Initializes;


   package body Initial_Condition_Acts_As_Post is
      procedure Init is
      begin
         Var := 1;
      end Init;
   begin
      Init;  --  Var is now set to 1. That makes
             --  the Initial_Condition false
   end Initial_Condition_Acts_As_Post;
end Initial_Condition_Illegal_2;
