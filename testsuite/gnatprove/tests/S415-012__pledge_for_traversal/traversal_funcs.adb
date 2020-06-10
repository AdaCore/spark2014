procedure Traversal_Funcs with SPARK_Mode is
   pragma Unevaluated_Use_Of_Old (Allow);

   type List;
   type List_Acc is access List;
   type List is record
      V : Integer;
      N : List_Acc;
   end record;

   function Pledge ( X : access constant List; B : Boolean) return Boolean is (B) with
     Ghost,
     Annotate => (GNATprove, Pledge);

   function Length (L : access constant List) return Natural is
     (if L = null then 0
      else Integer'Min (Natural'Last - 1, Length (L.N)) + 1)
   with Ghost,
     Annotate => (GNATprove, Terminating);

   function Next (X : access List) return access List with
     Pre => Length (X) < Natural'Last,
     Contract_Cases =>
       (X = null => Next'Result = null and then Pledge (Next'Result, X = null),
        others   => Length (Next'Result) = Length (X) - 1
        and then Pledge (Next'Result, (if Length (Next'Result) < Natural'Last then Length (X) = Length (Next'Result) + 1)))
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
     Post => (if Length (X) < 2 then Pledge (Next_2'Result, Length (X) = Length (X)'Old)
              else Pledge (Next_2'Result, (if Length (Next_2'Result) < Natural'Last - 1 then Length (X) = Length (Next_2'Result) + 2)))
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
        (if L < 2 then Pledge (C, Length (X) = L)
         else Pledge (C, (if Length (C) < Natural'Last - 1 then Length (X) = Length (C) + 2)));
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
