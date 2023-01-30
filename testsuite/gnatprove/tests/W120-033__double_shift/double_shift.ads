package Double_Shift is

   type Double_Uns is mod 2 ** 32;
   type Double_Int is range -2 ** 31 .. 2 ** 31 - 1;
   Double_Size : constant Natural := Double_Int'Size;

   function Shift_Left (A : Double_Uns; B : Natural) return Double_Uns
      with Convention => Intrinsic,
           Import,
           Global => null,
           Annotate => (Gnatprove, Always_Return);

   procedure Lemma_Double_Shift_Left (X : Double_Uns; S, S1 : Double_Uns)
   with
     Ghost,
     Pre  => S <= Double_Uns (Double_Size)
       and then S1 <= Double_Uns (Double_Size),
     Post => Shift_Left (Shift_Left (X, Natural (S)), Natural (S1)) =
             Shift_Left (X, Natural (S + S1));

   procedure Lemma_Double_Shift_Left (X : Double_Uns; S, S1 : Natural)
   with
     Ghost,
     Pre  => S <= Double_Size - S1,
     Post => Shift_Left (Shift_Left (X, S), S1) = Shift_Left (X, S + S1);


end Double_Shift;
