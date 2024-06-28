procedure Test with SPARK_Mode is
   type Int_Acc is access Integer;

   type Root is tagged record
      F : Int_Acc;
   end record;

   type Child is new Root with record
      G : Integer;
   end record;

   procedure Write (R : out Root) is
   begin
      R.F := new Integer'(42);
   end Write;

   procedure Write (C : out Child) is
   begin
      Write (Root (C)); -- @RESOURCE_LEAK:PASS
      C.G := 3;
   end Write;

   procedure Bad_Write (C : in out Child) is
   begin
      Write (Root (C)); -- @RESOURCE_LEAK:FAIL
      C.G := 3;
   end Bad_Write;

begin
   null;
end Test;
