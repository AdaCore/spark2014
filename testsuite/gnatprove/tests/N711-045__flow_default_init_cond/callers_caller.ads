with Caller; use Caller;

package Callers_Caller is
   type Pr_Record_TTT is private;

   function Add3 (R : Pr_Record_TTT) return Integer;

   procedure Test2;
private
   type Pr_Record_TTT is new Pr_Record_TT;
end Callers_Caller;
