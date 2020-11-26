procedure Traversal_Funcs with SPARK_Mode is
   pragma Unevaluated_Use_Of_Old (Allow);

   type List;
   type List_Acc is access List;
   type List is record
      V : Integer;
      N : List_Acc;
   end record;

   function At_End_Borrow (X : access constant List) return access constant List is (X) with
     Ghost,
     Annotate => (GNATprove, At_End_Borrow);

   function Length (L : access constant List) return Natural is
     (if L = null then 0
      else Integer'Min (Natural'Last - 1, Length (L.N)) + 1)
   with Ghost,
     Annotate => (GNATprove, Terminating);

   function Next (X : access List) return access List with
     Pre => Length (X) < Natural'Last,
     Contract_Cases =>
       (X = null => Next'Result = null and then At_End_Borrow (X) = null,
        others   => Length (Next'Result) = Length (X) - 1
        and then
          (if Length (At_End_Borrow (Next'Result)) < Natural'Last
           then Length (At_End_Borrow (X)) = Length (At_End_Borrow (Next'Result)) + 1))
   is
   begin
      if X /= null then
         return X.N;
      else
         return X;
      end if;
   end Next;

   function Next_2 (X : access List) return access List with
     Pre  => Length (X) < Natural'Last,
     Post => (if Length (X) < 2 then Length (At_End_Borrow (X)) = Length (X)
              elsif Length (At_End_Borrow (Next_2'Result)) < Natural'Last - 1
              then Length (At_End_Borrow (X)) = Length (At_End_Borrow (Next_2'Result)) + 2)
   is
   begin
      if Next (X) /= null then
         return Next (X).N;
      else
         return null;
      end if;
   end Next_2;

   procedure P1 (X : List_Acc) with
     Pre  => Length (X) < Natural'Last
     and Length (X) >= 2,
     Post => Length (X) = Length (X)'Old
   is
      L : Natural := Length (X) with Ghost;
      C : access List := Next (X).N;
      pragma Assert
        (if L < 2 then Length (At_End_Borrow (X)) = L
         elsif Length (At_End_Borrow (C)) < Natural'Last - 1
         then Length (At_End_Borrow (X)) = Length (At_End_Borrow (C)) + 2);
   begin
      if C /= null then
         C.V := 3;
      end if;
   end P1;

   procedure P2 (X : List_Acc) with
     Pre  => Length (X) < Natural'Last
     and X /= null,
     Post => Length (X) = Length (X)'Old
   is
      C : access List := Next (X.N);
   begin
      if C /= null then
         C.V := 3;
      end if;
   end P2;

   procedure P3 (X : List_Acc) with
     Pre  => Length (X) < Natural'Last,
     Post => Length (X) = Length (X)'Old
   is
      C : access List := Next (Next (X));
   begin
      if C /= null then
         C.V := 3;
      end if;
   end P3;
begin
   null;
end Traversal_Funcs;
