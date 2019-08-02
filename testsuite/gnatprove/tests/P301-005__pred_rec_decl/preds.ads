package Preds is

   type Int_OK is new Integer with
     Default_Value => 1,
     Predicate => Int_OK /= 0;

   type Int_Bad is new Integer with
     Default_Value => 0,
     Predicate => Int_Bad /= 0;

   procedure Create_Int_OK (X : out Int_OK);
   procedure Create_Int_Bad (X : out Int_Bad);

   type Int1 is new Integer with
     Default_Value => 1;

   type Int0 is new Integer with
     Default_Value => 0;

   type Sub_Int_OK is new Int1 with
     Predicate => Sub_Int_OK /= 0;

   type Sub_Int_Bad is new Int0 with
     Predicate => Sub_Int_Bad /= 0;

   procedure Create_Sub_Int_OK (X : out Sub_Int_OK);
   procedure Create_Sub_Int_Bad (X : out Sub_Int_Bad);

   type Intp is new Integer with
     Predicate => Intp /= 0;

   type Sub_Intp_OK is new Intp with
     Default_Value => 1;

   type Sub_Intp_Bad is new Intp with
     Default_Value => 0;

   procedure Create_Sub_Intp_OK (X : out Sub_Intp_OK);
   procedure Create_Sub_Intp_Bad (X : out Sub_Intp_Bad);

   type Arr_OK is array (1 .. 10) of Integer with
     Default_Component_Value => 1,
     Predicate => (for all K in Arr_OK'Range => Arr_OK (K) /= 0);

   type Arr_Bad is array (1 .. 10) of Integer with
     Default_Component_Value => 0,
     Predicate => (for all K in Arr_Bad'Range => Arr_Bad (K) /= 0);

   procedure Create_Arr_OK (X : out Arr_OK);
   procedure Create_Arr_Bad (X : out Arr_Bad);

   type Rec_OK is record
      I : Integer := 1;
      X : Int_OK;  --  @PREDICATE_CHECK:PASS
      A : Arr_OK;  --  @PREDICATE_CHECK:PASS
   end record with
     Predicate => Rec_OK.I /= 0 and Rec_OK.X /= 0 and (for all K in Rec_OK.A'Range => Rec_OK.A (K) /= 0);

   type Rec_Bad is record
      I : Integer := 0;
      X : Int_Bad;  --  @PREDICATE_CHECK:FAIL
      A : Arr_Bad;  --  @PREDICATE_CHECK:FAIL
   end record with
     Predicate => Rec_Bad.I /= 0 and Rec_Bad.X /= 0 and (for all K in Rec_Bad.A'Range => Rec_Bad.A (K) /= 0);

   procedure Create_Rec_OK (X : out Rec_OK);
   procedure Create_Rec_Bad (X : out Rec_Bad);

   type Rec_Int_OK is new Integer with
     Default_Value => 1,
     Predicate => Rec_Int_OK /= 0;

   type Rec_Int_Bad is new Integer with
     Default_Value => 0,
     Predicate => Rec_Int_Bad /= 0;

   type Rec_Wrap_OK is record
      X : Rec_Int_OK;  --  @PREDICATE_CHECK:PASS
   end record;

   type Rec_Wrap_Bad is record
      X : Rec_Int_Bad;  --  @PREDICATE_CHECK:FAIL
   end record;

end Preds;
