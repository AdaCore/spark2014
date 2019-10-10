procedure Traversals with SPARK_Mode is
   type List1;
   type List2;
   type List1_Acc is access List1;
   type List2_Acc is access List2;
   type List1 is record
      V : Integer;
      N : List2_Acc;
   end record;
   type List2 is record
      V : Integer;
      N : List1_Acc;
   end record;

   function Pledge (Borrower : access constant List2; Prop : Boolean) return Boolean is
     (Prop)
   with Ghost,
     Annotate => (GNATProve, Pledge);

   function Length (L : access constant List1) return Natural is
     (if L = null then 0
      elsif L.N = null then 1
      else Integer'Min (Natural'Last - 2, Length (L.N.N)) + 2)
   with Ghost,
     Annotate => (GNATProve, Terminating),
     Post => (if L /= null then Length'Result = Integer'Min (Natural'Last - 1, Length (L.N)) + 1);

   function Length (L : access constant List2) return Natural is
     (if L = null then 0
      elsif L.N = null then 1
      else Integer'Min (Natural'Last - 2, Length (L.N.N)) + 2)
   with Ghost,
     Annotate => (GNATProve, Terminating),
     Post => (if L /= null then Length'Result = Integer'Min (Natural'Last - 1, Length (L.N)) + 1);

   function Next (X : access List1) return access List2 with
     Pre => Length (X) < Natural'Last,
     Contract_Cases =>
       (X = null => Next'Result = null and then Pledge (Next'Result, X = null),
        others   => Length (Next'Result) = Length (X) - 1
              and then Pledge (Next'Result, Length (X) = Integer'Min (Natural'Last - 1, Length (Next'Result)) + 1))
   is
      Y : access List1 := X;
   begin
      if Y /= null then
         declare
            Z : access List2 := Y.N;
         begin
            return Z;
         end;
      end if;
      return null;
   end Next;
begin
   null;
end Traversals;
