with Ada.Unchecked_Deallocation;

package body My_Map with SPARK_Mode is
   pragma Unevaluated_Use_Of_Old (Allow);

   procedure Free is new Ada.Unchecked_Deallocation(Integer, Nullable_Int_Acc);
   procedure Free is new Ada.Unchecked_Deallocation(Map, Map_Acc);

   function Deep_Copy (M : access constant Map) return Map_Acc with SPARK_Mode => Off is
   begin
      if M = null then
         return null;
      else
         declare
            Value : constant Int_Acc := new Integer'(M.Value.all);
            Res   : constant Map_Acc :=
              new Map'(Key   => M.Key,
                       Value => Value,
                       Next  => Deep_Copy (M.Next));
         begin
            return Res;
         end;
      end if;
   end Deep_Copy;

   procedure Deep_Free (M : in out Map_Acc) is
   begin
      if M = null then
         return;
      else
         declare
            C : Map_Acc := M;
         begin
            M := null;
            while C /= null loop
               declare
                  N : Map_Acc := C;
                  I : Nullable_Int_Acc := N.Value;
               begin
                  C := N.Next;
                  N.Next := null;
                  Free (I);
                  Free (N);
               end;
            end loop;
         end;
      end if;
   end Deep_Free;

   function Contains (M : access constant Map; K : Positive) return Boolean is
      C : access constant Map := M;
   begin
      while C /= null loop
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
   begin
      while X /= null loop
         pragma Loop_Invariant (Model_Contains (X, K));
      pragma Loop_Invariant
        (Pledge (X, (if Model_Contains (X, K) then Model_Contains (M, K)
         and then Model_Value (M, K) = Model_Value (X, K))));

         if X.Key = K then
            X.Value.all := V;
            return;
         end if;
         X := X.Next;
      end loop;
   end Replace_Element;

   procedure Replace_Element_Ext (M : access Map; K : Positive; V : Integer) is

      --  Ghost procedure used to copy the first mapping of X to R

      procedure Update_R (R : in out Map_Acc; X : access constant Map) with Ghost,
        Pre  => X /= null,
        Post => Model_Contains (R, X.Key)
        and then
          (declare
             Old_R : constant Map_Acc := Deep_Copy (R)'Old;
           begin
             (if Old_R /= null
                  then (for all K in Old_R.all => Model_Contains (R, K)
                        and then Model_Value (R, K) = Model_Value (Old_R, K)))
           and then (for all K in R.all => Model_Contains (Old_R, K)
                     or K = X.Key)
           and then (if not Model_Contains (Old_R, X.Key) then
                       Model_Value (R, X.Key) = X.Value.all))
      is
      begin
         if not Model_Contains (R, X.Key) then
            declare
               C : constant Int_Acc := new Integer'(X.Value.all) with Ghost;
            begin
               R := new Map'(Key   => X.Key,
                             Value => C,
                             Next  => R);
            end;
         end if;
      end Update_R;

      M_Copy : constant Map_Acc := Deep_Copy (M) with Ghost;
      R      : Map_Acc with Ghost;
      X      : access Map := M;
   begin
      while X /= null loop
         pragma Loop_Invariant (Model_Contains (X, K));
         pragma Loop_Invariant (not Model_Contains (R, K));

         --  Invariants at the time of pledge

         pragma Loop_Invariant
           (Pledge (X, (for all K in X.all => Model_Contains (M, K))));
         pragma Loop_Invariant
           (Pledge (X, (if R /= null then
              (for all K in R.all => Model_Contains (M, K)))));
         pragma Loop_Invariant
           (Pledge (X, (for all K in M.all => Model_Contains (R, K) or Model_Contains (X, K))));
         pragma Loop_Invariant
           (Pledge (X, (for all K in M.all =>
                          (if Model_Contains (R, K) then Model_Value (M, K) = Model_Value (R, K)
                           else Model_Value (M, K) = Model_Value (X, K)))));

         --  Invariants at current time

         pragma Loop_Invariant
           (for all K in X.all => Model_Contains (M_Copy, K));
         pragma Loop_Invariant
           (if R /= null then
              (for all K in R.all => Model_Contains (M_Copy, K)));
         pragma Loop_Invariant
           (for all K in M_Copy.all => Model_Contains (R, K) or Model_Contains (X, K));
         pragma Loop_Invariant
           (for all K in M_Copy.all =>
              (if Model_Contains (R, K) then Model_Value (M_Copy, K) = Model_Value (R, K)
               else Model_Value (M_Copy, K) = Model_Value (X, K)));

         Update_R (R, X);

         if X.Key = K then
            X.Value.all := V;
            return;
         end if;
         X := X.Next;
      end loop;
      pragma Assert (False);
   end Replace_Element_Ext;

   function Constant_Access (M : access constant Map; K : Positive) return not null access constant Integer is
      C : access constant Map := M;
   begin
      while C /= null loop
         pragma Loop_Invariant (Model_Contains (C, K) = Model_Contains (M, K));
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
         pragma Loop_Invariant (Model_Contains (X, K));
         pragma Loop_Invariant (Model_Value (X, K) = Model_Value (M, K));
         pragma Loop_Invariant
           (Pledge (X, (if Model_Contains (X, K) then Model_Contains (M, K)
            and then Model_Value (M, K) = Model_Value (X, K))));

         if X.Key = K then
            return X.Value;
         end if;
         X := X.Next;
      end loop;
      raise Program_Error;
   end Reference;

end My_Map;
