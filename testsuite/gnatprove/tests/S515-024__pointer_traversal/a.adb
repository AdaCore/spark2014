procedure A with SPARK_Mode is
   type List;
   type List_Ptr is access List;
   type List is record
      Val  : Integer;
      Next : List_Ptr;
   end record;

   function Eq (X, Y : access constant List) return Boolean with
     Annotate => (GNATprove, Always_Return);
   function "=" (X, Y : List) return Boolean is
     (X.Val = Y.Val and then Eq (X.Next, Y.Next))
   with
     Annotate => (GNATprove, Always_Return);
   function Eq (X, Y : access constant List) return Boolean is
     ((X = null) = (Y = null)
      and then (if X /= null then X.all = Y.all));

   LNN : List_Ptr := new List'(Val => 3, Next => null);
   LN : List_Ptr := new List'(Val => 2, Next => LNN);
   L : List_Ptr := new List'(Val => 1, Next => LN);

   function Length (X : List_Ptr) return Natural is
     (if X = null then 0
      elsif Length (X.Next) = Natural'Last then Natural'Last
      else 1 + Length (X.Next));
   pragma Annotate (GNATprove, Always_Return, Length);

   function Get_Next (X : List_Ptr; I : Natural) return access constant List is
     (if I = 0 then X else Get_Next (X.Next, I - 1))
   with Pre => I <= Length (X) and I /= Natural'Last;
   pragma Annotate (GNATprove, Always_Return, Get_Next);

begin
   declare
      N : access constant List := L;
   begin
      while N /= null loop
         pragma Loop_Invariant
           (for some I in 1 .. Length (L) => Eq (Get_Next (L, I), N));
         pragma Assert (N.Val > 0);
         N := N.Next;
      end loop;
   end;
end A;
