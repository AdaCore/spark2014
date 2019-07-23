package Pointers with
  SPARK_Mode
is
   --  Single level of pointers

   type Int_Ptr is access Integer;

   procedure Bad_Swap (X, Y : in out Int_Ptr);

   procedure Swap (X, Y : in out Int_Ptr);

   X, Y : Int_Ptr;

   procedure Bad_Swap with
     Global => (In_Out => (X, Y));

   procedure Swap with
     Global => (In_Out => (X, Y));

   --  Double level of pointers

   type Int_Ptr_Ptr is access Int_Ptr;

   procedure Bad_Swap2 (X, Y : Int_Ptr_Ptr);

   procedure Swap2 (X, Y : Int_Ptr_Ptr);

   XX, YY : Int_Ptr_Ptr;

   procedure Bad_Swap2 with
     Global => (Input => (XX, YY));

   procedure Swap2 with
     Global => (Input => (XX, YY));

   --  Constant single level of pointers

   type Int_Cst_Ptr is access Integer;

   procedure Bad_Swap3 (X, Y : in out Int_Cst_Ptr);

   procedure Swap3 (X, Y : in out Int_Cst_Ptr);

   CX, CY : Int_Cst_Ptr;

   procedure Bad_Swap3 with
     Global => (In_Out => (CX, CY));

   procedure Swap3 with
     Global => (In_Out => (CX, CY));

   --  Pointer to constant single level of pointers

   type Int_Ptr_Cst_Ptr is access Int_Cst_Ptr;

   procedure Bad_Swap4 (X, Y : Int_Ptr_Cst_Ptr);

   procedure Swap4 (X, Y : Int_Ptr_Cst_Ptr);

   CXX, CYY : Int_Ptr_Cst_Ptr;

   procedure Bad_Swap4 with
     Global => (Input => (CXX, CYY));

   procedure Swap4 with
     Global => (Input => (CXX, CYY));

   --  Constant double level of pointers

   type Int_Cst_Ptr_Ptr is access Int_Ptr;

   procedure Bad_Swap5 (X, Y : Int_Cst_Ptr_Ptr);

   procedure Swap5 (X, Y : Int_Cst_Ptr_Ptr);

   CCXX, CCYY : Int_Cst_Ptr_Ptr;

   procedure Bad_Swap5 with
     Global => (Input => (CCXX, CCYY));

   procedure Swap5 with
     Global => (Input => (CCXX, CCYY));

end Pointers;
