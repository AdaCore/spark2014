procedure Test_Declare_Illegal with SPARK_Mode is
   type Int_Ptr is access Integer;

   procedure Bad1 is
      X : Integer := 1;
   begin
      X := (declare
            Y : constant Int_Ptr := new Integer'(3);
            begin Y.all + X);
   end Bad1;

   procedure Bad2 is
      C : Int_Ptr := new Integer'(3);
      X : Integer := 1;
   begin
      X := (declare
            Y : constant Int_Ptr := C;
            begin Y.all + X);
   end Bad2;

   function Create return Int_Ptr with Import;

   procedure Bad3 is
      X : Int_Ptr;
   begin
      X := (declare
            Y : constant Int_Ptr := Create;
            begin Y);
   end Bad3;
begin
   null;
end Test_Declare_Illegal;
