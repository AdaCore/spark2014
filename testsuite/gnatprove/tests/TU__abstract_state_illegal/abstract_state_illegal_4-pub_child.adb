with Abstract_State_Illegal_4.Pr_Child;

package body Abstract_State_Illegal_4.Pub_Child
  with Refined_State =>
         (Pub_State => Abstract_State_Illegal_4.Pr_Child.Pr_State)
is
   procedure Pub_P is begin null; end Pub_P;
end Abstract_State_Illegal_4.Pub_Child;
