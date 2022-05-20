package body My_Map with SPARK_Mode is
   pragma Unevaluated_Use_Of_Old (Allow);

   function Contains (M : access constant Map; K : Positive) return Boolean is
      C : access constant Map := M;
      --  C is used to traverse M

   begin

      while C /= null loop
         pragma Loop_Variant (Structural => C);

         --  K is in M iff it is in C

         pragma Loop_Invariant (Model_Contains (C, K) = Model_Contains (M, K));
         if C.Key = K then
            return True;
         end if;
         C := C.Next;
      end loop;
      return False;
   end Contains;

   procedure Replace_Element (M : access Map; K : Positive; V : Integer) is
      X : access Map := M;
      --  X is used to traverse M

   begin
      while X /= null loop
         pragma Loop_Variant (Structural => X);

         --  K is in X

         pragma Loop_Invariant (Model_Contains (X, K));

         --  M maps K to the same value as X

         pragma Loop_Invariant
           (if Model_Contains (At_End (X), K) then Model_Contains (At_End (M), K)
            and then Model_Value (At_End (M), K) = Model_Value (At_End (X), K));

         if X.Key = K then
            X.Value.all := V;
            return;
         end if;
         X := X.Next;
      end loop;
   end Replace_Element;

   function Constant_Access (M : access constant Map; K : Positive) return not null access constant Integer is
      C : access constant Map := M;
      --  C is used to traverse M

   begin
      while C /= null loop
         pragma Loop_Variant (Structural => C);

         --  K is in C

         pragma Loop_Invariant (Model_Contains (C, K));

         --  M maps K to the same value as X

         pragma Loop_Invariant (Model_Value (C, K) = Model_Value (M, K));

         if C.Key = K then
            return C.Value;
         end if;
         C := C.Next;
      end loop;
      raise Program_Error;
   end Constant_Access;

   function Reference (M : access Map; K : Positive) return not null access Integer is
      X : access Map := M;
   begin
      while X /= null loop
         pragma Loop_Variant (Structural => X);

         --  K is in X

         pragma Loop_Invariant (Model_Contains (X, K));

         --  M maps K to the same value as X

         pragma Loop_Invariant (Model_Value (X, K) = Model_Value (M, K));

         --  M will always map K to the same value as X

         pragma Loop_Invariant
           (if Model_Contains (At_End (X), K) then Model_Contains (At_End (M), K)
            and then Model_Value (At_End (M), K) = Model_Value (At_End (X), K));

         if X.Key = K then
            return X.Value;
         end if;
         X := X.Next;
      end loop;
      raise Program_Error;
   end Reference;

end My_Map;
