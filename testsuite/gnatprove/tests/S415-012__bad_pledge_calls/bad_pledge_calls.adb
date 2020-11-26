procedure Bad_Pledge_Calls with SPARK_Mode is
   type Int_Acc is not null access Integer;
   type List;
   type List_Acc is access List;
   type List is record
      V : Int_Acc;
      N : List_Acc;
   end record;

   function At_End_Borrow (X : access constant List) return access constant List is (X) with
     Ghost,
     Annotate => (GNATprove, At_End_Borrow);

   procedure Do_Something (X : List_Acc) is
      Y : access List := X;

      procedure Next with
        Pre  => Y /= null,
        Post => At_End_Borrow (Y).V.all'Old = 0; --  Should not be prouvable

      procedure Next_2 with
        Import,
        Pre  => Y /= null,
        Post => At_End_Borrow (Y.N).V.all = 0;

      procedure Next is
      begin
         Y.V.all := 0;
         Y := Y.N;
      end Next;
   begin
      while Y /= null loop
         pragma Loop_Invariant (At_End_Borrow (Y).V.all = At_End_Borrow (Y).V.all'Loop_Entry);
         Y.V.all := 0;
         Y := Y.N;
      end loop;
   end Do_Something;

   function Next (L : access List) return access List with
     Pre => L /= null,
     Import,
     Post => At_End_Borrow (L.N) = At_End_Borrow (Next'Result);

   function Next_2 (L : access List) return access List with
     Pre => L /= null and L.N /= null,
     Import,
     Post => At_End_Borrow (L).N.N = At_End_Borrow (Next_2'Result.N);

   function Good (X : access constant Integer) return access constant Integer is (X) with Ghost;
   pragma Annotate (GNATprove, At_End_Borrow, Good);

   function F (X : access constant Integer) return access constant Integer is (X) with Ghost;

   type Int_Access is access Integer;

   A  : Int_Access;
   I  : Positive := 1;
   X  : access Integer := A;
   pragma Assert (Good (F (X)) = Good (A));
   C  : access constant Integer := Good (A) with Ghost;
begin
   null;
end Bad_Pledge_Calls;
