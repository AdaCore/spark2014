package A is
   function F return Integer;
      pragma Postcondition (F'Result = 2);
end A;
