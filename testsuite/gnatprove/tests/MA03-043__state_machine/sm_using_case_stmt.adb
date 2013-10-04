package body SM_Using_Case_Stmt is

   State : States_T;

   procedure Initialise is
   begin
      State := States_T'First;
   end Initialise;

   procedure Progress_SM(Trigger : in Triggers_T) is
   begin
      case State is
         when Start =>
            case Trigger is
               when Btn_Pressed =>
                  State := Progress;
               when Btn_Released =>
                  null;
            end case;

         when Progress =>
            case Trigger is
               when Btn_Pressed =>
                  State := Finish;
               when Btn_Released =>
                  null;
            end case;

         when Finish =>
            case Trigger is
               when Btn_Pressed =>
                  null;
               when Btn_Released =>
                  null;
            end case;

      end case;
   end Progress_SM;

   function Is_Final_State return Boolean is
   begin
      return State = States_T'Last;
   end Is_Final_State;

end Sm_Using_Case_Stmt;
