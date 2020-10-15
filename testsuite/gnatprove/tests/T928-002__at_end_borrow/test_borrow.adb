with Ada.Containers; use Ada.Containers;
with Ada.Containers.Functional_Vectors;
with Ada.Numerics.Big_Numbers.Big_Integers; use Ada.Numerics.Big_Numbers.Big_Integers;

procedure Test_Borrow with SPARK_Mode is
   pragma Unevaluated_Use_Of_Old (Allow);
   type Int_Acc is not null access Integer;
   type List;
   type List_Acc is access List;
   type List is record
      V : Int_Acc;
      N : List_Acc;
   end record;

   function At_End_Borrow (X : access constant Integer) return access constant Integer is (X) with
     Ghost,
     Annotate => (GNATprove, At_End_Borrow);
   function At_End_Borrow (X : access constant List) return access constant List is (X) with
     Ghost,
     Annotate => (GNATprove, At_End_Borrow);

   function Length (X : access constant List) return Big_Natural is
     (if X = null then Big_Natural'(0) else Length (X.N) + 1)
   with Ghost,
       Annotate => (GNATprove, Terminating);

   function Get (X : access constant List; Pos : Positive) return Integer is
     (if Pos = 1 then X.V.all else Get (X.N, Pos - 1))
   with Ghost,
       Pre => Length (X) <= To_Big_Integer (Positive'Last)
       and then To_Big_Integer (Pos) <= Length (X),
       Subprogram_Variant => (Decreases => Pos);

   package Sequences is new Ada.Containers.Functional_Vectors
     (Positive, Integer);
   type Model_Type is new Sequences.Sequence with Ghost;

   function Model (X : access constant List) return Model_Type
   with Ghost,
     Import,
     Contract_Cases =>
       (Length (X) <= To_Big_Integer (Positive'Last) =>
          To_Integer (Length (X)) = Integer (Length (Model'Result))
        and then (for all I in 1 .. To_Integer (Length (X)) =>
            Get (X, I) = Get (Model'Result, I)),
        others                                       =>
          Length (Model'Result) = 0);

   function Reference (X : access List; Pos : Positive) return access Integer
   with Pre => Length (X) <= To_Big_Integer (Positive'Last)
       and then To_Big_Integer (Pos) <= Length (X),
     Post =>  Length (At_End_Borrow (X)) = Length (X) and then
      (for all I in 1 .. To_Integer (Length (X)) =>
         (if I = Pos then Get (At_End_Borrow (X), I) = At_End_Borrow (Reference'Result).all
          else Get (At_End_Borrow (X), I) = Get (X, I)));

   function Reference (X : access List; Pos : Positive) return access Integer is
      Y : access List := X;
   begin
      for I in 1 .. Pos - 1 loop
         Y := Y.N;

         pragma Loop_Invariant (Length (Y) = Length (X) - To_Big_Integer (I));
         pragma Loop_Invariant
           (for all K in I + 1 .. To_Integer (Length (X)) => Get (Y, K - I) = Get (X, K));
         pragma Loop_Invariant
           (for all K in 1 .. To_Integer (Length (Y)) => Get (Y, K) = Get (X, K + I));

         pragma Loop_Invariant (Length (At_End_Borrow (X)) = To_Big_Integer (I) + Length (At_End_Borrow (Y)));
         pragma Loop_Invariant
           (if Length (At_End_Borrow (X)) <= To_Big_Integer (Positive'Last) then
                (for all K in 1 .. I => Get (At_End_Borrow (X), K) = Get (X, K)));
         pragma Loop_Invariant
           (if Length (At_End_Borrow (X)) <= To_Big_Integer (Positive'Last) then
                (for all K in I + 1 .. To_Integer (Length (At_End_Borrow (X))) => Get (At_End_Borrow (X), K) = Get (At_End_Borrow (Y), K - I)));
      end loop;
      return Y.V;
   end Reference;

   type List_Array is array (Positive range <>) of List_Acc;
   type List_Arr_Acc is access List_Array;

   procedure Do_Something (A : in out List_Arr_Acc; I : Positive) with
     Pre => A /= null and then I in A'Range and then I < A'Last,
     Post => A /= null and then A'First = A'First'Old
     and then A'Last = A'Last'Old and then Length (A (A'Last)) = Length (A (A'Last))'Old
   is
      Y : access List := A (I);
   begin
      while Y /= null loop
         Y.V.all := 0;
         Y := Y.N;
      end loop;
   end Do_Something;

   V1 : Int_Acc := new Integer'(1);
   X1 : List_Acc := new List'(V => V1,
                              N => null);
   V2 : Int_Acc := new Integer'(2);
   X2 : List_Acc := new List'(V => V2,
                              N => X1);
   V3 : Int_Acc := new Integer'(3);
   X3 : List_Acc := new List'(V => V3,
                              N => X2);
   V4 : Int_Acc := new Integer'(4);
   X4 : List_Acc := new List'(V => V4,
                              N => X3);
begin
   declare
      Y : access List := X4.N;
   begin
      Y := Y.N;
      declare
         Z : access Integer := Y.V;
      begin
         pragma Assert (At_End_Borrow (Y.V) = At_End_Borrow (Z));
         pragma Assert (At_End_Borrow (Y.N) = At_End_Borrow (X4.N.N.N));
         pragma Assert (At_End_Borrow (Z) = At_End_Borrow (X4.N.N.V)); --@ASSERT:FAIL
         Z.all := 42;
      end;
      Y := Y.N;
   end;
   pragma Assert (X4.V.all = 4);
   pragma Assert (X4.N.V.all = 3);
   pragma Assert (X4.N.N.V.all = 42);
   pragma Assert (X4.N.N.N.V.all = 1);
   pragma Assert (X4.N.N.N.N = null);

   declare
      Y : access List := X4;

      procedure Next with
        Pre  => Y /= null and Length (Y) <= To_Big_Integer (Positive'Last),
        Post =>
          Model (Y.N)'Old = Model (Y)
        and then Length (Y)'Old = Length (Y) + 1
        and then At_End_Borrow (Y'Old).V.all = Y.V.all'Old
        and then Length (At_End_Borrow (Y'Old)) = Length (At_End_Borrow (Y)) + 1
        and then Model (At_End_Borrow (Y'Old).N) = Model (At_End_Borrow (Y));

      procedure Next is
      begin
         Y := Y.N;
      end Next;
   begin
      Next;
      declare
         Z : access Integer := Y.V;
      begin
         Z.all := 42;
      end;
      Y := Y.N;
   end;
   pragma Assert (X4.V.all = 4);
   pragma Assert (X4.N.V.all = 42);
   pragma Assert (X4.N.N.V.all = 42);
   pragma Assert (X4.N.N.N.V.all = 1);
   pragma Assert (X4.N.N.N.N = null);

   declare
      type Two_Val is record
         X, Y : Int_Acc;
      end record;

      type Two_Val_Array is array (Positive range <>) of Two_Val;

      type Two_Val_Array_Acc is not null access Two_Val_Array;

      type Two_Arrays is record
         F, G : Two_Val_Array_Acc;
      end record;

      type Two_Array_Acc is not null access Two_Arrays;

      function At_End_Borrow (X : access constant Two_Arrays) return access constant Two_Arrays is (X) with
        Ghost,
        Annotate => (GNATprove, At_End_Borrow);
      function At_End_Borrow (X : access constant Two_Val_Array) return access constant Two_Val_Array is (X) with
        Ghost,
        Annotate => (GNATprove, At_End_Borrow);

      procedure Try (X : Two_Array_Acc) with
        Pre => X.F'First = 1 and X.F'Last = 2 and X.G'First = 1 and X.G'Last = 2
      is
         CF1X : Integer := X.F (1).X.all;
         CF2X : Integer := X.F (2).X.all;
         CF1Y : Integer := X.F (1).Y.all;
         CF2Y : Integer := X.F (2).Y.all;
         CG1X : Integer := X.G (1).X.all;
         CG2X : Integer := X.G (2).X.all;
         CG1Y : Integer := X.G (1).Y.all;
         CG2Y : Integer := X.G (2).Y.all;
         Z : access Integer := X.F (1).X;
      begin
         pragma Assert (X.G'First = 1 and X.G'Last = 2); --  not borrowed
         pragma Assert (Z.all = CF1X);
         pragma Assert (At_End_Borrow (X.F (1).X) = At_End_Borrow (Z)); --  actually borrowed
         pragma Assert (At_End_Borrow (X.F (2).X).all = CF2X); --  conservatively frozen by the borrow
         pragma Assert (X.F (1).Y.all = CF1Y); --  not borrowed
         pragma Assert (X.F (2).Y.all = CF2Y); --  not borrowed
         pragma Assert (X.G (1).X.all = CG1X); --  not borrowed
         pragma Assert (X.G (2).X.all = CG2X); --  not borrowed
         pragma Assert (X.G (1).Y.all = CG1Y); --  not borrowed
         pragma Assert (X.G (2).Y.all = CG2Y); --  not borrowed
      end Try;

   begin
      null;
   end;
end Test_Borrow;
