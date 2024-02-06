procedure Main with SPARK_Mode is
   type Int_Acc is access Integer;
   type Int_Acc_Acc is access Int_Acc;
   type Int_Acc_Const is access constant Int_Acc;
   type R is record
      F : Int_Acc;
      G : Int_Acc;
   end record;
   type Ref_Matrix is
     array (Positive range <>, Positive range <>) of Int_Acc;

   procedure Through_Allocator;
   procedure Through_Aggregate;
   procedure Through_Array_Aggregate;
   procedure Through_Delta_Aggregate;
   procedure Through_Extension_Aggregate;
   procedure Through_Multidimensional_Update;

   procedure Through_Allocator is
      X : Int_Acc := new Integer'(0);
      Y : Int_Acc_Acc :=
        new Int_Acc'(declare I : constant Integer := 0; begin X);
   begin
      null;
   end Through_Allocator;
   
   procedure Through_Aggregate is
      X : Int_Acc_Const := new Int_Acc'(new Integer'(0));
      Y : R := (F => X.all, G => X.all);
   begin
      null;
   end Through_Aggregate;
   
   procedure Through_Array_Aggregate is
      X : Int_Acc_Const := new Int_Acc'(new Integer'(0));
      Y : Ref_Matrix (1 .. 3, 1 .. 3) :=
        ((X.all, others => X.all),
         (1 .. 3 => X.all),
         (1 => X.all, 2 => X.all, 3 => X.all));
   begin
      null;
   end Through_Array_Aggregate;

   procedure Through_Delta_Aggregate is
      X : Int_Acc_Const := new Int_Acc'(new Integer'(0));
      Y : R := (F | G => new Integer'(0));
      Z : R := (Y with delta F => X.all);
   begin
      null;
   end Through_Delta_Aggregate;

   procedure Through_Extension_Aggregate is
      type Rtag is tagged record
         F : Int_Acc;
         G : Int_Acc;
      end record;
      type Rext is new Rtag with record
         H : Integer;
      end record;
      X : Int_Acc_Const := new Int_Acc'(new Integer'(0));
      Z : Rext := (Rtag'(F => new Integer'(0), G => X.all) with H => 0);
   begin
      null;
   end Through_Extension_Aggregate;
   
   procedure Through_Multidimensional_Update is
      X : Int_Acc_Const := new Int_Acc'(new Integer'(0));
      Y : Ref_Matrix (1 .. 3, 1 .. 3) :=
        (others => (others => new Integer'(0)));
      Z : Ref_Matrix (1 .. 3, 1 .. 3) := Y'Update((1, 2) => X.all);
   begin
      null;
   end Through_Multidimensional_Update;
   
begin
   Through_Allocator;
   Through_Aggregate;
   Through_Array_Aggregate;
   Through_Delta_Aggregate;
   Through_Extension_Aggregate;
   Through_Multidimensional_Update;
end Main;
