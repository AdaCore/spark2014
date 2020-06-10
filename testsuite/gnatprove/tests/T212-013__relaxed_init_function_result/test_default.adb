procedure Test_Default with SPARK_Mode is
   type My_Rec is record
      X, Y : Integer;
   end record;

   type My_Rec_2 is new My_Rec with Relaxed_Initialization;

   function C return My_Rec_2 with Import;

   type Holder is record
      F : My_Rec := My_Rec (C); -- @INIT_BY_PROOF:FAIL
   end record;

   X : Holder;

   type Res is record
      C : Integer;
   end record with Relaxed_Initialization;

   type My_Arr is array (Integer range <>) of Natural;

   function Search (A : My_Arr; V : Natural) return Res with
     Post =>
       (if (for some E of A => E = V)
        then Search'Result'Initialized
        and then Search'Result.C in A'Range
        and then A (Search'Result.C) = V)
   is
      R : Res;
   begin
      for I in A'Range loop
         if A (I) = V then
            R.C := I;
            exit;
         end if;
         pragma Loop_Invariant (for all K in A'First .. I => A (K) /= V);
      end loop;
      return R;
   end Search;

   type My_Int is new Integer with Relaxed_Initialization;

   function Search_Bad (A : My_Arr; V : Natural) return My_Int with
     Post =>
       (if (for some E of A => E = V)
        then Search_Bad'Result'Initialized
        and then Integer (Search_Bad'Result) in A'Range
        and then A (Integer (Search_Bad'Result)) = V)
   is
      R : My_Int;
   begin
      for I in A'Range loop
         if A (I) = V then
            R := My_Int (I);
            exit;
         end if;
         pragma Loop_Invariant (for all K in A'First .. I => A (K) /= V);
      end loop;
      return R; -- @INIT_BY_PROOF:FAIL
   end Search_Bad;

   procedure Test_Search (A : My_Arr; B : Boolean) with Global => null is
      R : constant Res := Search (A, 0);
   begin
      if B then
         pragma Assert (R.C in A'Range); -- @INIT_BY_PROOF:FAIL
      elsif (for some E of A => E = 0) then
         pragma Assert (R.C in A'Range);
      end if;
   end Test_Search;

begin
   null;
end Test_Default;
