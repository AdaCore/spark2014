with P.Child;

package body P with Refined_State => (State => P.Child.X) is
   function Read_Secret return Boolean is (P.Child.X) with Refined_Global => P.Child.X;
end;
