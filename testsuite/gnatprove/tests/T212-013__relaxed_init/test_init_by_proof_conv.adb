procedure Test_Init_By_Proof_Conv with SPARK_Mode is
   type InRec is record
      F : Integer;
   end record;

   type Rec (D : Boolean) is record
      G : InRec;
   end record;

   type Rec_2 is new Rec (True) with
     Relaxed_Initialization;
   type Rec_3 is new Rec (True);

   type InRec_2 is new InRec with
     Relaxed_Initialization;

   X : Rec_2;
   Y : InRec_2 := InRec_2 (Rec_3 (X).G); --@INIT_BY_PROOF:NONE
   Z : InRec := Rec_3 (X).G; --@INIT_BY_PROOF:FAIL
begin
   null;
end Test_Init_By_Proof_Conv;
