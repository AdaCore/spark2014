procedure Test_Constrained_Type with SPARK_Mode is
   type Int_Array is array (Positive range <>) of Integer;

   procedure P (X : in out Int_Array; F, L : in out Integer) with
     Pre => F in X'Range and then L in X'Range and then F <= L,
     Post => X (F'Old .. L'Old) = (X (F .. L)'Old with delta F'Old => 12);

   procedure P (X : in out Int_Array; F, L : in out Integer) is
   begin
      X (F) := 12;
      L := 0;
      F := 0;
   end P;

   procedure P2 (X : in out Int_Array; F, L : in out Integer) with
     Pre => F in X'Range and then L in X'Range and then F <= L;

   procedure P2 (X : in out Int_Array; F, L : in out Integer) is
   begin
      loop
         X (F) := 12;
         L := 0;
         F := 0;
         pragma Loop_Invariant (X (F'Loop_Entry .. L'Loop_Entry) = (X (F .. L)'Loop_Entry with delta F'Loop_Entry => 12));
         exit;
      end loop;
   end P2;

   X : Int_Array := (1 .. 6 => 0);
   F, L : Integer := 1;
begin
   P (X, F, L);
end Test_Constrained_Type;
