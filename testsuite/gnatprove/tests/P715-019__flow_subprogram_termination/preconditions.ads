package Preconditions is
   function  Returning_Precondition (A, B : Integer)
                                     return Boolean
   is (A = B);

   function Nonreturning_Precondition (A, B : Integer) return Boolean;

end;
