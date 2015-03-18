with Refs;

generic
   Inner : Integer;

function Gen_Func_Pragmas (Formal : Integer) return Integer;
pragma Global
         ((Input =>
            (Refs.External,
             Inner)));

pragma Depends
         ((Gen_Func_Pragmas'Result =>
            (Refs.External,
             Inner,
             Formal)));
