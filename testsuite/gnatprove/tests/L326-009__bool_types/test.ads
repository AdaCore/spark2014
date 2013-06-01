with Pack; use Pack;

package Test is

   procedure Test_For_Loop
     with Pre => B2;
   procedure Test_While_Loop;
   procedure Test_Case_Stmt;
   procedure Test_If;

   function My_B1 return Boolean is (Bool_Subtype (B1));
   function My_B2 return Boolean is (B2);

end Test;
