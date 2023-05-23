package body Double_Shift is
   procedure Lemma_Double_Shift_Left (X : Double_Uns; S, S1 : Double_Uns)
   is null;
   -----------------------------
   -- Lemma_Double_Shift_Left --
   -----------------------------

   procedure Lemma_Double_Shift_Left (X : Double_Uns; S, S1 : Natural) is
   begin
      Lemma_Double_Shift_Left (X, Double_Uns (S), Double_Uns (S1));
      pragma Assert (Shift_Left (Shift_Left (X, S), S1)
        = Shift_Left (Shift_Left (X, S), Natural (Double_Uns (S1))));
      pragma Assert (Shift_Left (X, S + S1)
        = Shift_Left (X, Natural (Double_Uns (S + S1))));
   end Lemma_Double_Shift_Left;
end Double_Shift;
