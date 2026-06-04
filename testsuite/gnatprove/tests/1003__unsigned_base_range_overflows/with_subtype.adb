pragma Extensions_Allowed (All_Extensions);
procedure With_Subtype with SPARK_Mode is
   type U_Base is range 0 .. 2 ** 32 - 1 with Unsigned_Base_Range, Size => 32;
   function Id0 (X : U_Base) return U_Base is (X);
   subtype U is U_Base range Id0 (0) .. Id0 (2 ** 16  - 1);

   function Id (X : U) return U is (X);

   procedure Self_Difference (X : U) is
      A : constant U := X - X; --@OVERFLOW_CHECK:PASS
   begin
      null;
   end Self_Difference;

   procedure Sub_Ok is
      X : constant U := Id (3);
      Y : constant U := Id (2);
      Z : constant U := X - Y; --@OVERFLOW_CHECK:PASS
   begin
      null;
   end Sub_Ok;

   procedure Sub_Underflow is
      X : constant U := Id (2);
      Y : constant U := Id (3);


      Z : constant U := X - Y; --@OVERFLOW_CHECK:FAIL
   begin
      null;
   end Sub_Underflow;

   procedure Add_Ok is
      X : constant U := Id (36);
      Y : constant U := Id (57);
      Z : constant U := X + Y; --@RANGE_CHECK:PASS
   begin
      null;
   end Add_Ok;

   procedure Add_Overflow is
      X : constant U := Id (65535);
      Y : constant U := Id (32767);
      Z : constant U := X + Y; --@RANGE_CHECK:FAIL
   begin
      null;
   end Add_Overflow;

   procedure Mul_Ok is
      X : constant U := Id (34);
      Y : constant U := Id (89);
      Z : constant U := X * Y; --@RANGE_CHECK:PASS
   begin
      null;
   end Mul_Ok;

   procedure Mul_Overflow is
      X : constant U := Id (65535);
      Y : constant U := Id (32767);
      Z : constant U := X * Y; --@RANGE_CHECK:FAIL
   begin
      null;
   end Mul_Overflow;

   procedure Pred_Underflow is
      X : U := Id (0);
   begin
      X := U'Pred (X); --@OVERFLOW_CHECK:FAIL
   end Pred_Underflow;

   procedure Succ_Ok is
      X : U := Id (10);
   begin
      X := U'Succ (X); --@OVERFLOW_CHECK:PASS
   end Succ_Ok;

   procedure Expon_KO is
      X : U := Id (10);
   begin
      X := X ** 100; --@OVERFLOW_CHECK:FAIL
   end Expon_KO;

   function Is_Prime (X : U) return Boolean
     with Pre => X >= 2,
     Post =>
       Is_Prime'Result
         = (for all I in U =>
              (for all J in U => (if I * J = X then I = 1 or J = 1)));

   function Is_Prime (X : U) return Boolean is
      Test : U := 2;
   begin
      loop
         pragma Loop_Invariant (Test in 2 .. X);
         pragma Loop_Invariant
           (for all I in U =>
              (for all J in U => (if I * J = X then I = 1 or I >= Test)));
         pragma Loop_Variant (Increases => Test);
         exit when Test > X/Test;
         if X mod Test = 0 then
            return False;
         end if;
         Test := Test + 1;
      end loop;
      return True;
   end Is_Prime;

   type Arr is array (U range <>) of U;

   procedure Bad_Empty_Aggregate is
      X : Arr := []; --@RANGE_CHECK:FAIL
   begin
      null;
   end Bad_Empty_Aggregate;

   Not_Found : exception;

   function Binary_Search (A : Arr; Low, High : U) return U
     with Global => null, Always_Terminates => True, Side_Effects,
     Pre => (if A'Last > A'First then
               (for all I in A'First .. A'Last - 1 => A (I) <= A (I+1))),
     Post => A (Binary_Search'Result) in Low .. High,
     Exceptional_Cases =>
       (Not_Found =>
          (for all I in A'First .. A'Last => A (I) not in Low .. High));

   function Binary_Search (A : Arr; Low, High : U) return U
   is

      procedure Exceed_High (Loc : U)
        with Ghost,
        Global => (Input => A, Proof_In => High),
        Always_Terminates => True,
        Pre =>
          Loc in A'Range
          and then
          (if A'Last > A'First then
             (for all I in A'First .. A'Last - 1 => A (I) <= A (I+1)))
          and then A (Loc) > High,
        Post => (for all I in Loc .. A'Last => A (I) > High);

      procedure Exceed_High (Loc : U) is
      begin
         for I in Loc .. A'Last loop
            pragma Loop_Invariant (for all J in Loc .. I => A (J) > High);
            pragma Assert (if I /= A'Last then A (I) <= A (I+1));
         end loop;
      end Exceed_High;

      procedure Under_Low (Loc : U)
        with Ghost,
        Global => (Input => A, Proof_In => Low),
        Always_Terminates => True,
        Pre =>
          Loc in A'Range
          and then
          (if A'Last > A'First then
             (for all I in A'First .. A'Last - 1 => A (I) <= A (I+1)))
          and then A (Loc) < Low,
        Post => (for all I in A'First .. Loc => A (I) < Low);

      procedure Under_Low (Loc : U) is
      begin
         for I in reverse A'First .. Loc loop
            pragma Loop_Invariant (for all J in I .. Loc => A (J) < Low);
            pragma Assert (if I /= A'First then A (I-1) <= A (I));
         end loop;
      end Under_Low;

      Low_Index : U;
      High_Index : U;
   begin
      if A'Last < A'First then
         raise Not_Found;
      end if;
      Low_Index := A'First;
      High_Index := A'Last;
      loop
         pragma Loop_Invariant (A'First <= Low_Index);
         pragma Loop_Invariant (Low_Index <= High_Index);
         pragma Loop_Invariant (High_Index <= A'Last);
         pragma Loop_Invariant
           (for all J in A'First .. Low_Index =>
              (if J /= Low_Index then A (J) < Low));
         pragma Loop_Invariant
           (for all J in High_Index .. A'Last =>
              (if J /= High_Index then A (J) > High));
         pragma Loop_Variant (Decreases => (High_Index - Low_Index));
         declare
            Mid : U := Low_Index + (High_Index - Low_Index) / 2;
         begin
            if A (Mid) < Low then
               Under_Low (Mid);
               exit when Mid = High_Index;
               Low_Index := Mid + 1;
            elsif A (Mid) > High then
               Exceed_High (Mid);
               exit when Mid = Low_Index;
               High_Index := Mid - 1;
            else
               return Mid;
            end if;
         end;
      end loop;
      raise Not_Found;
   end Binary_Search;

begin
   null;
end With_Subtype;
