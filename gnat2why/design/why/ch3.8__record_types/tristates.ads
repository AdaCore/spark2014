package Tristates is

   type Tristate is (T_True, T_False, T_Unknown);

   function T_Not (Op : Tristate) return Tristate;
   pragma Postcondition ((Op = T_True and T_Not'Result = T_False)
                         or (Op = T_False and T_Not'Result = T_True));

   function T_Or (Left, Right : Tristate) return Tristate;
   pragma Postcondition ((Left = T_True and T_Or'Result = T_True)
                         or (Left = T_False and T_Or'Result = Right)
                         or (Left = T_Unknown and T_Or'Result = T_Unknown));

   function T_And (Left, Right : Tristate) return Tristate;
   pragma Postcondition ((Left = T_False and T_And'Result = T_False)
                         or (Left = T_True and T_And'Result = Right)
                         or (Left = T_Unknown and T_And'Result = T_Unknown));

end Tristates;
