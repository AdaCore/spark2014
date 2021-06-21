procedure Test_Annotate with SPARK_Mode is
   type Int_Acc is access Integer;
   type C_Int_Acc is access constant Integer;
   type Rec is record
      F : Int_Acc;
   end record;
   type Rec_Acc is access Rec;
   type C_Rec_Acc is  access constant Rec;
   type Rec_C is record
      F : C_Int_Acc;
   end record;
   type Rec_C_Acc is access Rec_C;
   type C_Rec_C_Acc is  access constant Rec_C;
   type Holder is record
      C : Rec_C_Acc;
   end record;

   procedure Move_OK (X : in out Rec_Acc; Y : out Int_Acc) with
     Pre => X /= null
   is
   begin
      Y := X.F;
      X.F := null;
   end Move_OK;
   function Move_OK (X : C_Rec_Acc) return C_Int_Acc with
     Pre => X /= null
   is
   begin
      return C_Int_Acc (X.F);
   end Move_OK;

   function Eq (X : Rec_Acc; Y : C_Rec_C_Acc) return Boolean is
     ((X = null) = (Y = null)
      and then (if X /= null then (X.F = null) = (Y.F = null))
      and then (if X /= null and then X.F /= null then X.F.all = Y.F.all));

   function Deep_Copy (R : Rec_Acc) return C_Rec_C_Acc with
     Volatile_Function,
     Post => Eq (R, Deep_Copy'Result)
   is
      Res : C_Rec_C_Acc;
   begin
      if R = null then
         null;
      elsif R.F = null then
         declare
            A : constant Rec_C_Acc := new Rec_C'(F => null);
            H : constant Holder := (C => A); --  Intentional memory leak
         begin
            Res := C_Rec_C_Acc (H.C);
         end;
      else
         declare
            C   : constant Int_Acc := new Integer'(R.F.all);
            R_1 : constant Rec := (F => C);  --  Intentional memory leak
            R_2 : constant Rec_C := (F => C_Int_Acc (R_1.F));
            A   : constant Rec_C_Acc := new Rec_C'(R_2);
            H   : constant Holder := (C => A); --  Intentional memory leak
         begin
            Res := C_Rec_C_Acc (H.C);
         end;
      end if;
      return Res;
   end Deep_Copy;

   type C_String_Acc is access constant String;
   type Values is array (Positive range <>) of Integer;
   type Values_Acc is access Values;
   type Values_Option is access constant Values;
   type Pair is record
      Key : not null C_String_Acc;
      Val : not null Values_Option;
   end record;
   type Pairs is array (Positive range <>) of Pair;
   type Map is not null access constant Pairs;

   function Find (M : Map; K : String) return Values_Option with
     Post => (if Find'Result = null then (for all P of M.all => P.Key.all /= K)
              else (for some P of M.all =>
                        P.Key.all = K and Find'Result /= null and Find'Result.all = P.Val.all))
   is
   begin
      for I in M'Range loop
         if M (I).Key.all = K then
            return M (I).Val;
         end if;
         pragma Loop_Invariant (for all J in M'First .. I => M (J).Key.all /= K);
      end loop;
      return null;
   end Find;

   procedure Do_Something (R : in out Rec_Acc) with
     Import;

   X   : Rec_Acc;
   Y   : C_Rec_C_Acc;
begin
   Do_Something (X);
   Y := Deep_Copy (X);
end Test_Annotate;
