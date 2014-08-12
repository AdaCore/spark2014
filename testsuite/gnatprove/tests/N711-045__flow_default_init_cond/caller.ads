with Dic; use Dic;

package Caller is
   type Pr_TT is private
     with Default_Initial_Condition;  --  Problem!!

   type Pr_Record_TT is private;

   function Add2 (R : Pr_Record_TT) return Integer;

   procedure Test;
private
   type Pr_TT is new Pr_T;  --  I need to issue something here!

   type Pr_Record_TT is new Pr_Record_T;
end Caller;
