procedure Test_At_End_In_Lemma with SPARK_Mode is
   type List_Cell;
   type List is access List_Cell;
   type List_Cell is record
      V : Integer;
      N : List;
   end record;

   function At_End (X : access constant List_Cell) return access constant List_Cell is (X) with
     Ghost,
     Annotate => (GNATprove, At_End_Borrow);

   procedure Lemma_OK (X : access constant List_Cell) with
     Ghost,
     Import,
     Global => null;

   procedure Lemma_No_Glob (X : access constant List_Cell) with
     Ghost,
     Import;

   procedure Lemma_Bad_1 (X : access constant List_Cell; Y : access List_Cell) with
     Ghost,
     Import,
     Global => null;

   W : Integer with Ghost;

   procedure Lemma_Bad_2 (X : access constant List_Cell) with
     Ghost,
     Import,
     Global => (In_Out => W);

   procedure Call_Lemmas (L1, L2 : List) is
      B : access List_Cell := L1;
   begin
      Lemma_OK (B);
      Lemma_No_Glob (B);
      Lemma_Bad_1 (B, L2);
      Lemma_Bad_2 (B);
      Lemma_OK (At_End (B));
      Lemma_No_Glob (At_End (B));   -- Rejected for now
      Lemma_Bad_1 (At_End (B), L2); -- Rejected
      Lemma_Bad_2 (At_End (B));     -- Rejected
   end Call_Lemmas;
begin
   null;
end Test_At_End_In_Lemma;
