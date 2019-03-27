package body Pointers with
  SPARK_Mode
is
   --  Single level of pointers

   procedure Bad_Swap (X, Y : in out Int_Ptr) is
   begin
      X := Y;
   end Bad_Swap;

   procedure Swap (X, Y : in out Int_Ptr) is
      Tmp : Int_Ptr := X;
   begin
      X := Y;
      Y := Tmp;
   end Swap;

   procedure Bad_Swap is
   begin
      X := Y;
   end Bad_Swap;

   procedure Swap is
      Tmp : Int_Ptr := X;
   begin
      X := Y;
      Y := Tmp;
   end Swap;

   --  Double level of pointers

   procedure Bad_Swap2 (X, Y : Int_Ptr_Ptr) is
   begin
      X.all := Y.all;
   end Bad_Swap2;

   procedure Swap2 (X, Y : Int_Ptr_Ptr) is
      Tmp : Int_Ptr := X.all;
   begin
      X.all := Y.all;
      Y.all := Tmp;
   end Swap2;

   procedure Bad_Swap2 is
   begin
      XX.all := YY.all;
   end Bad_Swap2;

   procedure Swap2 is
      Tmp : Int_Ptr := XX.all;
   begin
      XX.all := YY.all;
      YY.all := Tmp;
   end Swap2;

   --  Constant single level of pointers

   procedure Bad_Swap3 (X, Y : in out Int_Cst_Ptr) is
   begin
      X := Y;
   end Bad_Swap3;

   procedure Swap3 (X, Y : in out Int_Cst_Ptr) is
      Tmp : Int_Cst_Ptr := X;
   begin
      X := Y;
      Y := Tmp;
   end Swap3;

   procedure Bad_Swap3 is
   begin
      CX := CY;
   end Bad_Swap3;

   procedure Swap3 is
      Tmp : Int_Cst_Ptr := CX;
   begin
      CX := CY;
      CY := Tmp;
   end Swap3;

   --  Pointer to constant single level of pointers

   procedure Bad_Swap4 (X, Y : Int_Ptr_Cst_Ptr) is
   begin
      X.all := Y.all;
   end Bad_Swap4;

   procedure Swap4 (X, Y : Int_Ptr_Cst_Ptr) is
      Tmp : Int_Cst_Ptr := X.all;
   begin
      X.all := Y.all;
      Y.all := Tmp;
   end Swap4;

   procedure Bad_Swap4 is
   begin
      CXX.all := CYY.all;
   end Bad_Swap4;

   procedure Swap4 is
      Tmp : Int_Cst_Ptr := CXX.all;
   begin
      CXX.all := CYY.all;
      CYY.all := Tmp;
   end Swap4;

   --  Constant double level of pointers

   procedure Bad_Swap5 (X, Y : Int_Cst_Ptr_Ptr) is
   begin
      X.all.all := Y.all.all;
   end Bad_Swap5;

   procedure Swap5 (X, Y : Int_Cst_Ptr_Ptr) is
      Tmp : Int_Ptr := X.all;
   begin
      X.all.all := Y.all.all;
      Y.all.all := Tmp.all;
   end Swap5;

   procedure Bad_Swap5 is
   begin
      CCXX.all.all := CCYY.all.all;
   end Bad_Swap5;

   procedure Swap5 is
      Tmp : Int_Ptr := CCXX.all;
   begin
      CCXX.all.all := CCYY.all.all;
      CCYY.all.all := Tmp.all;
   end Swap5;

end Pointers;
