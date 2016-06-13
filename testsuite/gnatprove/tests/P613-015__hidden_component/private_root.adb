with Child_Of_Private; use Child_Of_Private;
package body Private_Root with SPARK_Mode is
   procedure P is
      C : Child;
   begin
      Root'Class (C).Hidden_F := 1;
   end P;
end Private_Root;
