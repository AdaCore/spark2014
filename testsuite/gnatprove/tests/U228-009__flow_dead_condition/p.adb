procedure P with SPARK_Mode is
   type Int_Ptr is access Integer;

   --  Y is immutable; X can be changed
   procedure Ptr_Compare (X     : access Integer;
                          Y     : access constant Integer;
                          MyOut : out Boolean)
     with Pre => (X /= null and Y /= null)
   is
   begin
      X.all := 0;
      MyOut :=  X.all = Y.all;
   end Ptr_Compare;

   procedure Ptr_Compare2 (X     : access constant Integer;
                           Y     : access constant Integer;
                           MyOut : out Boolean)
     with Pre => (X /= null and Y /= null)
   is
   begin
      MyOut :=  X.all = Y.all;
   end Ptr_Compare2;

   A : Int_Ptr := new Integer'(1);
   Tmp : Boolean;

   procedure Glob_Compare (X     : access Integer;
                           MyOut : out Boolean)
     with Global => (Input => A)
   is
   begin
      X.all := 0;
      MyOut := X.all = A.all;
   end Glob_Compare;

   --  X is immutable
   procedure Glob_Compare2 (X     : access constant Integer;
                            MyOut : out Boolean)
     with Global => (Input => A)
   is
   begin
      MyOut := X.all = A.all;
   end Glob_Compare2;

begin
   Ptr_Compare (A, A, Tmp);  -- Aliasing hazard
   Glob_Compare (A, Tmp);  -- Aliasing hazard

   --  These calls are *not* at risk of aliasing
   Ptr_Compare2 (A, A, Tmp);
   Glob_Compare2 (A, Tmp);
end P;
