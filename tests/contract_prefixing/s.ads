with T; use T;

package S is

   procedure Plus_Two  (N : in out Signed);
   pragma Precondition (N > 0 and N < Signed'Last - 1);
   pragma Postcondition (N = N'Old + 2);

   function Plus_Two_F (N : Signed) return Signed;
   pragma Precondition (N > 0 and N < Signed'Last - 1);
   pragma Postcondition (Plus_Two_F'Result = N + 2);

end S;
