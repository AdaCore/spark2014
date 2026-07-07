
--  Proof support tests

procedure Test_Proof with SPARK_Mode is
   function Test_Exit_OK (N : Natural) return Natural
     with Pre => N > 0 and then N <= Natural'Last / N,
       Post => 2 * Test_Exit_OK'Result = N * (N-1);
   function Test_Exit_OK (N : Natural) return Natural is
      function Increment (Index : in out Natural) return Boolean
        with Pre => Index < N,
        Side_Effects,
        Post => Index = Index'Old + 1 and then Increment'Result = (Index = N);
      function Increment (Index : in out Natural) return Boolean is
      begin
         Index := Index + 1;
         return (Index = N);
      end Increment;
      I : Natural := 0;
      Acc : Natural := 0;
   begin
      loop
         pragma Loop_Invariant (I < N);
         pragma Loop_Invariant (I * (I-1) = 2 * Acc);
         pragma Loop_Variant (Decreases => (N - I));
         Acc := Acc + I;
         exit when Increment (I);
      end loop;
      return Acc;
   end Test_Exit_OK;

   function Test_Exit_KO (N : Natural) return Natural
     with Pre => N > 0 and then N <= Natural'Last / N,
       Post => 2 * Test_Exit_KO'Result = N * (N-1);
   function Test_Exit_KO (N : Natural) return Natural is
      function Increment (Index : in out Natural) return Boolean
        with Pre => Index < N,
        Side_Effects,
        Post => Index = Index'Old + 1 and then Increment'Result = (Index = N);
      function Increment (Index : in out Natural) return Boolean is
      begin
         Index := Index + 1;
         return (Index = N);
      end Increment;
      I : Natural := 0;
      Acc : Natural := 0;
   begin
      loop
         pragma Loop_Invariant (I < N);
         pragma Loop_Invariant (I = 0); --@LOOP_INVARIANT_PRESERV:FAIL
         pragma Loop_Variant (Decreases => (N - I));
         Acc := Acc + I;
         exit when Increment (I);
      end loop;
      return Acc;
   end Test_Exit_KO;

   type IArray is array (Natural range <>) of Integer;

   function Test_Continue (A : in out IArray) return Integer
     with Side_Effects,
     Post => (for all I in A'Range => A (I) = (if A'Old (I) < 0 then 0 else A'Old (I)))
     and then (if Test_Continue'Result >= 0
                 then Test_Continue'Result in A'Range
                   and then A'Old (Test_Continue'Result) = 0
                 else (for all I in A'Range => A'Old (I) /= 0));
   function Test_Continue (A : in out IArray) return Integer is
      function Skip (I : Integer) return Boolean
        with Pre => I in A'Range,
        Side_Effects,
        Global => (In_Out => A),
        Modifies => (A (I) when A (I) < 0),
        Post => Skip'Result = (A'Old (I) < 0)
        and then (if Skip'Result then A (I) = 0);
      function Skip (I : Integer) return Boolean is
      begin
         return B : Boolean := A (I) < 0 do
            if B then
               A (I) := 0;
            end if;
         end return;
      end Skip;
      Found : Integer := -1;
   begin
      for I in A'Range loop
         pragma Loop_Invariant (for all J in I .. A'Last => A (J) = A'Loop_Entry (J));
         pragma Loop_Invariant (for all J in A'First .. (I - 1) =>
                                  A (J) = (if A'Loop_Entry (J) < 0 then 0 else A'Loop_Entry (J)));
         pragma Loop_Invariant
           (if Found >= 0 then Found in A'First .. (I-1) and then A'Loop_Entry (Found) = 0);
         pragma Loop_Invariant (if Found < 0 then (for all J in A'First .. (I-1) =>
                                  A'Loop_Entry (J) /= 0));
         continue when Skip (I);
         if Found < 0 and then A (I) = 0 then
            Found := I;
         end if;
      end loop;
      return Found;
   end Test_Continue;

   function Test_Return (I : in out Integer) return Integer
     with Pre => I /= Integer'Last,
       Side_Effects,
     Post => Test_Return'Result = I and then I = I'Old + 1;
   function Test_Return (I : in out Integer) return Integer is
      function Wrapped (J : in out Integer) return Integer
        with Pre => J /= Integer'Last,
          Side_Effects,
        Post => Wrapped'Result = J and then J = J'Old + 1;
      function Wrapped (J : in out Integer) return Integer is
      begin
         J := J + 1;
         return J;
      end Wrapped;
   begin
      return Wrapped (I);
   end Test_Return;

   function Test_Interrupted_Return return Integer with Post =>
     Test_Interrupted_Return'Result = 42;
   function Test_Interrupted_Return return Integer is
      E : exception;
      function Raise_E return Integer with Side_Effects, Exceptional_Cases => (E => True), Exit_Cases => (True => (Exception_Raised => E));
      function Raise_E return Integer is
      begin
         raise E;
         return 0;
      end Raise_E;
   begin
      return Raise_E;
   exception
      when E =>
         return 42;
   end Test_Interrupted_Return;

   function Test_Interrupted_Return_KO return Integer
     with Post => Test_Interrupted_Return_KO'Result = 43; --@POSTCONDITION:FAIL
   function Test_Interrupted_Return_KO return Integer is
      E : exception;
      function Raise_E return Integer with Side_Effects, Exceptional_Cases => (E => True), Exit_Cases => (True => (Exception_Raised => E));
      function Raise_E return Integer is
      begin
         raise E;
         return 0;
      end Raise_E;
   begin
      return Raise_E;
   exception
      when E =>
         return 42;
   end Test_Interrupted_Return_KO;

   function Test_Split_Case (X : Integer) return Integer
     with Post => Test_Split_Case'Result =
       (if X < 0
        then (-1)
        elsif X = 1
        then 0
        elsif X >= 3
        then 2
        else 1);
   function Test_Split_Case (X : Integer) return Integer is
      CE : exception;
      function To_Natural (X : Integer) return Natural
        with Post => To_Natural'Result = X,
        Side_Effects,
        Exceptional_Cases => (CE => X not in Natural);
      function To_Natural (X : Integer) return Natural is
      begin
         if X < 0 then
            raise CE;
         end if;
         return X;
      end To_Natural;
   begin
      case To_Natural (X) is
         when 0 =>
            return 1;
         when 1 =>
            return 0;
         when 2 =>
            return 1;
         when others => return 2;
      end case;
   exception
      when CE =>
         return -1;
   end Test_Split_Case;

   function Test_Split_Case_KO (X : Integer) return Integer
     with Post => Test_Split_Case_KO'Result = (if X < 0 then (-1) elsif X = 1 then 0 elsif X >= 3 then 2 else 1); --@POSTCONDITION:FAIL
   function Test_Split_Case_KO (X : Integer) return Integer is
      CE : exception;
      function To_Natural (X : Integer) return Natural
        with Post => To_Natural'Result = X,
        Side_Effects,
        Exceptional_Cases => (CE => X not in Natural);
      function To_Natural (X : Integer) return Natural is
      begin
         if X < 0 then
            raise CE;
         end if;
         return X;
      end To_Natural;
   begin
      case To_Natural (X) is
         when 0 =>
            return 1;
         when 1 =>
            return 0;
         when 2 =>
            return 1;
         when others => return 2;
      end case;
   exception
      when CE =>
         return -2;
   end Test_Split_Case_KO;

   function Test_If (A : in out IArray; I, J : Natural) return Integer
     with Side_Effects,
     Post => (if Test_If'Result >= 0
             then Test_If'Result in A'Range
                 and then Test_If'Result in I .. J
                 and then A'Old (Test_If'Result) = Integer'Last
             elsif Test_If'Result = -1
             then (for all K in A'Range =>
                       (if K in I .. J then A (K) = A'Old (K) + 1))
              else I < A'First or else A'Last < J);
   function Test_If (A : in out IArray; I, J : Natural) return Integer is
      Out_Of_Bounds : exception;
      function Found (K : Natural) return Boolean
        with Side_Effects,
        Global => (In_Out => A),
        Exceptional_Cases => (Out_Of_Bounds => True),
        Exit_Cases => ((K in A'Range) => Normal_Return, others => (Exception_Raised => Out_Of_Bounds)),
        Modifies => (A (K) when K in A'Range),
        Post => (if Found'Result
                 then A'Old (K) = Integer'Last
                 else A (K) = A'Old (K) + 1);
      function Found (K : Natural) return Boolean is
      begin
         if K not in A'Range then
            raise Out_Of_Bounds;
         end if;
         return B : Boolean := A (K) = Integer'Last do
            if not B then
               A (K) := A (K) + 1;
            end if;
         end return;
      end Found;
   begin
      for K in I .. J loop
         pragma Loop_Invariant (for all L in K .. J => (if L in A'Range then A (L) = A'Loop_Entry (L)));
         pragma Loop_Invariant (for all L in I .. K - 1 => L in A'Range and then A (L) = A'Loop_Entry (L) + 1);
         if Found (K) then
            return K;
         end if;
      end loop;
      return -1;
   exception
      when Out_Of_bounds =>
         return -2;
   end Test_If;

   function Test_If_KO (A : in out IArray; I, J : Natural) return Integer
     with Side_Effects,
     Post => (if Test_If_KO'Result >= -1
             then Test_If_KO'Result in A'Range --@POSTCONDITION:FAIL
                 and then Test_If_KO'Result in I .. J
                 and then A'Old (Test_If_KO'Result) = Integer'Last
                 and then (for all K in A'Range =>
                       (if K in I .. J then A (K) = A'Old (K) + 1))
              else I < A'First or else A'Last < J);
   function Test_If_KO (A : in out IArray; I, J : Natural) return Integer is
      Out_Of_Bounds : exception;
      function Found (K : Natural) return Boolean
        with Side_Effects,
        Global => (In_Out => A),
        Exceptional_Cases => (Out_Of_Bounds => True),
        Exit_Cases => ((K in A'Range) => Normal_Return, others => (Exception_Raised => Out_Of_Bounds)),
        Modifies => (A (K) when K in A'Range),
        Post => (if Found'Result
                 then A'Old (K) = Integer'Last
                 else A (K) = A'Old (K) + 1);
      function Found (K : Natural) return Boolean is
      begin
         if K not in A'Range then
            raise Out_Of_Bounds;
         end if;
         return B : Boolean := A (K) = Integer'Last do
            if not B then
               A (K) := A (K) + 1;
            end if;
         end return;
      end Found;
   begin
      for K in I .. J loop
         pragma Loop_Invariant (for all L in K .. J => (if L in A'Range then A (L) = A'Loop_Entry (L)));
         pragma Loop_Invariant (for all L in I .. K - 1 => L in A'Range and then A (L) = A'Loop_Entry (L) + 1);
         if Found (K) then
            return K;
         end if;
      end loop;
      return -1;
   exception
      when Out_Of_bounds =>
         return -2;
   end Test_If_KO;

   procedure Test_Deeply_Nested (X : Integer);
   procedure Test_Deeply_Nested (X : Integer) is
      E : exception;
      F : exception;
      function Err_E (X : Integer; Err_Value : Integer) return Integer
        with Side_Effects, Exceptional_Cases => (E => True),
        Exit_Cases => (X = Err_Value => (Exception_Raised => E), others => Normal_Return),
        Post => Err_E'Result = X;
      function Err_F (X : Integer; Err_Value : Integer) return Integer
        with Side_Effects, Exceptional_Cases => (F => True),
        Exit_Cases => (X = Err_Value => (Exception_Raised => F), others => Normal_Return),
        Post => Err_F'Result = X;
      function Err_E (X : Integer; Err_Value : Integer) return Integer is
      begin
         if X = Err_Value then
            raise E;
         end if;
         return X;
      end Err_E;
      function Err_F (X : Integer; Err_Value : Integer) return Integer is
      begin
         if X = Err_Value then
            raise F;
         end if;
         return X;
      end Err_F;
      Y : Integer;
   begin
      Y := (if X < 42
            then (case X is
                 when 0 .. 3 => Err_E (X, 2),
                 when 6 .. 10 => 7,
                 when 11 .. 13 => Err_F (X, 12),
                 when others =>
                (declare
                   Z : constant Integer := (if X >= 36 then 36 else X);
                 begin
                   Err_E (X, Z)
                ))
              else Err_F (X, 89));
      pragma Assert (Y = 7
                     or else Y in 0 .. 1
                     or else Y = 3
                     or else (Y in 42 .. Integer'Last and then Y /= 89)
                     or else Y = 11
                     or else Y = 13
                     or else Y in 37 .. 41
                     or else Y in Integer'First .. (-1));
   exception
      when E =>
         pragma Assert (X = 2
                        or else
                          ((X not in 0 .. 3)
                           and then (X not in 6 .. 10)
                           and then (X not in 11 .. 13)
                           and then (X <= 36)));
      when F =>
         pragma Assert (X = 89 or else X = 12);
   end Test_Deeply_Nested;

   procedure Test_Deeply_Nested_KO (X : Integer);
   procedure Test_Deeply_Nested_KO (X : Integer) is
      E : exception;
      F : exception;
      function Err_E (X : Integer; Err_Value : Integer) return Integer
        with Side_Effects, Exceptional_Cases => (E => True),
        Exit_Cases => (X = Err_Value => (Exception_Raised => E), others => Normal_Return),
        Post => Err_E'Result = X;
      function Err_F (X : Integer; Err_Value : Integer) return Integer
        with Side_Effects, Exceptional_Cases => (F => True),
        Exit_Cases => (X = Err_Value => (Exception_Raised => F), others => Normal_Return),
        Post => Err_F'Result = X;
      function Err_E (X : Integer; Err_Value : Integer) return Integer is
      begin
         if X = Err_Value then
            raise E;
         end if;
         return X;
      end Err_E;
      function Err_F (X : Integer; Err_Value : Integer) return Integer is
      begin
         if X = Err_Value then
            raise F;
         end if;
         return X;
      end Err_F;
      Y : Integer;
   begin
      Y := (if X < 42
            then (case X is
                 when 0 .. 3 => Err_E (X, 2),
                 when 6 .. 10 => 7,
                 when 11 .. 13 => Err_F (X, 12),
                 when others =>
                (declare
                   Z : constant Integer := (if X >= 36 then 36 else X);
                 begin
                   Err_E (X, Z)
                ))
              else Err_F (X, 89));
      pragma Assert (Y = 7 --@ASSERT:FAIL
                     or else Y in 0 .. 1
                     or else Y = 3
                     or else (Y in 42 .. Integer'Last and then Y /= 89)
                     or else Y = 11
                     or else Y = 13
                     or else Y in 37 .. 40
                     or else Y in Integer'First .. (-1));
   exception
      when E =>
         pragma Assert (X = 2 --@ASSERT:FAIL
                        or else
                          ((X not in 0 .. 4)
                           and then (X not in 6 .. 10)
                           and then (X not in 11 .. 13)
                           and then (X <= 36)));
      when F =>
         pragma Assert (X = 89 or else X = 12);
   end Test_Deeply_Nested_KO;

   procedure Test_Nested (X : Integer);
   procedure Test_Nested (X : Integer) is
      E : exception;
      F : exception;
      U, V, W : Integer := 0;
      function Random (Y : Integer) return Boolean
        with Global => null, Import;
      function Err_E (Z : Integer) return Integer
        with Side_Effects, Global => (In_Out => U),
        Exceptional_Cases => (E => True),
        Post => U = U'Old,
        Import;
      function Err_F (Z : Integer) return Integer
        with Side_Effects, Global => (In_Out => V),
        Exceptional_Cases => (F => True),
        Post => V = V'Old,
        Import;
   begin
      while Random (W) loop
         pragma Loop_Invariant (U = U'Loop_Entry);
         pragma Loop_Invariant (V = V'Loop_Entry);
         W := (declare
               T : constant Integer := (if Random (W + X) then W + X else W - X);
               begin
               (case T is
                  when 2 | 5 =>
                    Err_E (T),
                  when others =>
                    Err_F (T)));
      end loop;
      pragma Assert (U = 0 and then V = 0); --@ASSERT:PASS
      pragma Assert (W = 0); --@ASSERT:FAIL
   exception
      when E =>
         pragma Assert (V = 0); --@ASSERT:PASS
         pragma Assert (U = 0); --@ASSERT:FAIL
      when F =>
         pragma Assert (U = 0); --@ASSERT:PASS
         pragma Assert (V = 0); --@ASSERT:FAIL
   end Test_Nested;

begin
   null;
end Test_Proof;
