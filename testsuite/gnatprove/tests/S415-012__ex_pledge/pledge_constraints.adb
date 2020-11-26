procedure Pledge_Constraints with SPARK_Mode is
   type Int_Acc is access Integer;
   type Int_Acc_Option (Present : Boolean := False) is record
      case Present is
      when True => Content : Int_Acc;
      when False => null;
      end case;
   end record;
   type Int_Opt_Arr is array (Positive range <>) of Int_Acc_Option;
   type Int_Arr_Acc is access Int_Opt_Arr;
   type Two_Arrays is record
      A1, A2 : Int_Arr_Acc;
   end record;

   function At_End_Borrow (T : access constant Integer) return access constant Integer is (T) with Ghost;
   pragma Annotate (GNATprove, At_End_Borrow, Entity => At_End_Borrow);

   function At_End_Borrow (T : access constant Int_Opt_Arr) return access constant Int_Opt_Arr is (T) with Ghost;
   pragma Annotate (GNATprove, At_End_Borrow, Entity => At_End_Borrow);

   procedure Update (X : in out Two_Arrays) with
     Pre => X.A1 /= null and then 1 in X.A1'Range and then X.A1 (1).Present
     and then X.A1 (1).Content /= null
   is
      Y : access Integer := X.A1 (1).Content;
      I : Integer := 1;
   begin
      X.A2 := new Int_Opt_Arr'(1 .. 3 => (Present => False));
      Y.all := 15;
      pragma Assert (At_End_Borrow (X.A1 (1).Content).all = At_End_Borrow (Y).all);
      pragma Assert (At_End_Borrow (X.A1 (I).Content).all = At_End_Borrow (Y).all); --  rejected in borrow checker
   end Update;
begin
   null;
end Pledge_Constraints;
