package Access_To_Constants with SPARK_Mode is
   pragma Elaborate_Body;
   type Int_Acc is access Integer;
   type C_Int_Acc is access constant Integer;
   type Rec is record
      F : Int_Acc;
   end record;
   type Rec_Acc is access Rec;
   type C_Rec_Acc is access constant Rec;
   type Rec_2 is record
      F : C_Int_Acc;
   end record;
   type Rec_2_Acc is access Rec_2;
   type C_Rec_2_Acc is access constant Rec_2;

   function Allocate_Int_Acc (X : Integer) return Int_Acc with Global => null;
   --  Hide an allocation from SPARK

   function Allocate_Int_Acc (X : Integer) return Rec with Volatile_Function;

   X : Int_Acc := new Integer'(15);
   Y : constant C_Rec_Acc := new Rec'(F => X); --  This is a move
   X_2 : constant C_Int_Acc := new Integer'(15);
   Y_2 : constant C_Rec_2_Acc := new Rec_2'(F => X_2); -- should be ok

   Z : Int_Acc := new Integer'(15);
   Z_2 : constant C_Int_Acc := C_Int_Acc (Z); --  This is a move
end Access_To_Constants;
