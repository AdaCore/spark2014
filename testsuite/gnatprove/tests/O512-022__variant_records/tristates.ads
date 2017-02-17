package Tristates is

   type Tristate is (T_True, T_False, T_Unknown);

   function T_Not (Op : Tristate) return Tristate is
      (if Op = T_True then T_False else T_True);

   function T_Or (Left, Right : Tristate) return Tristate is
      (case Left is
        when T_True => T_True,
        when T_False => Right,
        when T_Unknown => T_Unknown);

   function T_And (Left, Right : Tristate) return Tristate is
      (case Left is
         when T_False => T_False,
         when T_True  => Right,
         when T_Unknown => T_Unknown);

end Tristates;
