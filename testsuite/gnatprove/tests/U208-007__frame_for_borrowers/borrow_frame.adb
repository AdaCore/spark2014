procedure Borrow_Frame with SPARK_Mode is
   type List_Cell;
   type List is access List_Cell;
   type List_Cell is record
      V : Integer;
      N : List;
   end record;

   function At_End (X : access constant List_Cell)
                    return access constant List_Cell
   is (X)
   with Ghost,
     Annotate => (GNATprove, At_End_Borrow);

   function Last (X : access constant List_Cell) return Integer is
     (if X.N = null then X.V else Last (X.N))
   with Pre => X /= null, Annotate => (GNATprove, Always_Return);

   procedure Set_Last (X : List; V : Integer) with Pre => X /= null is
      B : not null access List_Cell := X;
   begin
      loop
         pragma Loop_Invariant (Last (At_End (X)) = Last (At_End (B)));
         if B.N = null then
            B.V := V;
            exit;
         end if;
         B := B.N;
      end loop;
      pragma Assert (Last (At_End (X)) = Last (At_End (B))); --@ASSERT:PASS
   end Set_Last;

   procedure Set_Last_2 (X : List; V : Integer) with Pre => X /= null is
      B : access List_Cell := X;
   begin
      loop
         pragma Loop_Invariant (B /= null);
         pragma Loop_Invariant (Last (At_End (X)) = Last (At_End (B)));
         if B.N = null then
            B.V := V;
            exit;
         end if;
         B := B.N;
      end loop;
      pragma Assert (Last (At_End (X)) = Last (At_End (B))); --@ASSERT:PASS
   end Set_Last_2;
begin
   null;
end Borrow_Frame;
