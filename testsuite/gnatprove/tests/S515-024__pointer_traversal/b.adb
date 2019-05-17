procedure B with SPARK_Mode is
   type List;
   type List_Ptr is access List;
   type List is record
      Val  : Integer;
      Next : List_Ptr;
   end record;

   LNN : List_Ptr := new List'(Val => 3, Next => null);
   LN : List_Ptr := new List'(Val => 2, Next => LNN);
   L : List_Ptr := new List'(Val => 1, Next => LN);

   function Length (X : List_Ptr) return Natural is
     (if X = null then 0
      elsif Length (X.Next) = Natural'Last then Natural'Last
      else 1 + Length (X.Next));
   pragma Annotate (GNATprove, Terminating, Length);

   function Get_Next (X : List_Ptr; I : Natural) return access constant List is
     (case I is when 0 => X, when others => Get_Next (X.Next, I - 1))
   with Pre => I <= Length (X) and I /= Natural'Last;
   pragma Annotate (GNATprove, Terminating, Get_Next);

begin
   declare
      N : access constant List := L;
   begin
      while N /= null loop
         pragma Loop_Invariant
           (for some I in 1 .. Length (L) => Get_Next (L, I) = N);
         pragma Assert (N.Val > 0);
         N := N.Next;
      end loop;
   end;
end B;
