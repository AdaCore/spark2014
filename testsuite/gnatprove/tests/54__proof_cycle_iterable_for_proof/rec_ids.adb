with P;
with Contains_Through_Model;
with Element_Through_Model;
with Has_Element_Through_Model;

package body Rec_Ids with SPARK_Mode is

   function P_Rec_Id (X : Positive) return Positive with SPARK_Mode is
      C : P.P2.T;
   begin
      pragma Assert (for all F of C => True);
      return X;
   end P_Rec_Id;

   function Contains_Through_Model_Id (X : Integer) return Integer is
      C : Contains_Through_Model.P3.T;
   begin
      pragma Assert (for all F of C => True);
      return X;
   end Contains_Through_Model_Id;

   function Element_Through_Model_Id (X : Integer) return Integer is
      C : Element_Through_Model.P3.T;
   begin
      pragma Assert (for all F of C => True);
      return X;
   end Element_Through_Model_Id;

   function Has_Element_Through_Model_Id (X : Positive) return Positive is
      C : Has_Element_Through_Model.P3.T;
   begin
      pragma Assert (for all F of C => True);
      return X;
   end Has_Element_Through_Model_Id;
end Rec_Ids;
