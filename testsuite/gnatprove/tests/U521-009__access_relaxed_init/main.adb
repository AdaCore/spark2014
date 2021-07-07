procedure Main with SPARK_Mode is
   type H is record
      X : Integer;
   end record;

   X : H with Relaxed_Initialization;

   type Rec is record
      F : H := (X => 1);
      G : Integer := 1;
   end record;

   type Rec_Acc is access Rec;

   procedure Test1 with Global => (Input => X) is
      Z : Rec_Acc := new Rec'(X, 1); --@INIT_BY_PROOF:FAIL
   begin
      null;
   end Test1;

   procedure Test2 with Global => (Input => X) is
      Z : Rec_Acc := new Rec'((X with delta X => 1), 1); --@INIT_BY_PROOF:PASS
   begin
      null;
   end Test2;

   type Rec_2 is new Rec with Relaxed_Initialization;
   type Rec_2_Acc is access Rec_2;

   procedure Test3 with Global => null is
      Z : Rec_2_Acc := new Rec_2; --@INIT_BY_PROOF:NONE
      X : Rec_2 := Z.all;
      XX : Rec := Rec (X);--@INIT_BY_PROOF:PASS
   begin
      null;
   end Test3;

begin
   null;
end Main;
