package S is

   procedure Plus_Two  (N : in out Integer);
   pragma Precondition (N > 0 and N < Integer'Last - 1);
   pragma Postcondition (N = N'Old + 2);

end S;
