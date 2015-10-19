with Types; use Types;

package Update_Checks_1 is

   procedure P1 (A: in out Array_U; I : in Index; New_Val : in Integer)
     with Post => A = A'Old'Update (I => New_Val);

   procedure P2 (A: in out Array_U; I : in Index; New_Val : in Integer)
     with Post => A = A'Old'Update (I + 1 => New_Val);

   procedure P4 (A: in out Array_U; I : in Index; New_Val : in Integer)
     with Post => A = A'Old'Update (1 .. I => New_Val);

   procedure P5 (A: in out Array_U; I, J, K, L : in Index; New_Val : in Integer)
     with Post => A = A'Old'Update (1 .. I => 0, J .. K | L => New_Val);

   procedure P8 (A: in out Array_U; I : in Index; New_Val : in Integer)
     with Pre  => I in A'Range,
     Post => A = A'Old'Update (I => New_Val);

   --  Reference tests, to compare generated why and avoid regressions

   procedure Ref_Test_0 (A: in out Array_U; I : in Index; New_Val : in Integer)
     with Post => A (I) = New_Val;

   procedure Ref_Test_1 (A: in out Array_U; I : in Index; New_Val : in Integer)
     with Post => A (1 .. I) = (1 .. I => New_Val); -- missing checks

   procedure Ref_Test_2 (A: in out Array_C; I : in Index; New_Val : in Integer)
     with Post => A = A'Old'Update (I => New_Val);

   procedure Ref_Test_3 (A: in out Array_C2; I : in Index; New_Val : in Integer)
     with Post => A = A'Old'Update (I => New_Val);

end Update_Checks_1;
