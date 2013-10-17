with Abstract_State_Illegal_4.Pr_Child;

package body Abstract_State_Illegal_4
   with Refined_State => (State => Abstract_State_Illegal_4.Pr_Child.Pr_State)
is
   procedure P is begin null; end P;
end Abstract_State_Illegal_4;
